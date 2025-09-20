use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::hir::def::{DefId, DefType, Resolved};
use crate::hir::lowering_ast::{HirId, HirIdMap};
use crate::hir::node::{Block, Expr, ExprKind, HirLiteral, Local, Param, StmtKind, Universe};
use crate::pill::body::{AltarData, AltarId, Altars, IrFunc, LabelId, LabelVec, Proj};
use crate::pill::cfg::Cfg;
use crate::pill::instr::{InstrStream, Operand};
use crate::pill::scalar::Scalar;
use crate::session::{Session, SymbolId};
use crate::types::fun_cx::FieldId;
use crate::types::{fun_cx::TypeTable, ty::Ty};

pub struct IrBuilder<'il> {
    s: &'il Session<'il>,
    fns: Vec<IrFunc<'il>>,
    built_fns: HashSet<DefId>,
}

impl<'il> IrBuilder<'il> {
    pub fn new(s: &'il Session<'il>) -> Self {
        Self {
            s,
            fns: vec![],
            built_fns: HashSet::new(),
        }
    }

    pub fn build_ir_fun(&mut self, fun: DefId) {
        if self.built_fns.contains(&fun) {
            return;
        }

        self.fns.push(FnLowerer::new(self.s).lower_fn(fun));
        self.built_fns.insert(fun);
    }
}

pub struct FnLowerer<'il> {
    pub(crate) session: &'il Session<'il>,
    types: TypeTable<'il>,
    altars: RefCell<Altars<'il>>,
    pub(crate) cfg: Cfg<'il>,

    local_hir_ids_to_altar: RefCell<HirIdMap<AltarId>>,
}

impl<'il> FnLowerer<'il> {
    pub fn new(session: &'il Session<'il>) -> Self {
        Self {
            cfg: Cfg::new(),
            session,
            types: TypeTable::new(),
            altars: Altars::new().into(),
            local_hir_ids_to_altar: HashMap::new().into(),
        }
    }

    #[track_caller]
    pub fn lower_fn(mut self, def_id: DefId) -> IrFunc<'il> {
        self.types = self.session.typeck(def_id);
        let hir = self.session.hir_ref();
        let (sig, name) = hir.expect_fn(def_id);
        let body = hir.get_body(sig.body);

        let (labels, tac) =
            self.lower_fn_body(sig.arguments, body, self.session.fn_sig_for(def_id).output);

        IrFunc::new(name, body.span, self.altars.into_inner(), tac, labels)
    }

    pub fn new_temporary(&self, ty: Ty<'il>) -> AltarId {
        self.altars.borrow_mut().push(AltarData::new(ty))
    }

    pub fn project_altar(&self, orig: AltarId, proj: Proj) -> AltarId {
        let altar_data = self.altars.borrow();
        let mut new_data = altar_data.get(orig).unwrap().clone();
        new_data.push_proj(proj);

        self.altars.borrow_mut().push(new_data)
    }

    pub fn ty_table(&self) -> &TypeTable<'il> {
        &self.types
    }

    pub fn lower_fn_body(
        &mut self,
        inputs: &[Param<'_>],
        body: &'il Expr<'il>,
        ret_ty: Ty<'il>,
    ) -> (LabelVec<usize>, InstrStream<'il>) {
        let ExprKind::Block(block) = body.kind else {
            unreachable!("non-block bodies???");
        };

        self.lower_block_body(block, inputs, ret_ty)
    }

    pub fn lower_block_body(
        &mut self,
        block: &Block<'_>,
        inputs: &[Param<'_>],
        ret_ty: Ty<'il>,
    ) -> (LabelVec<usize>, InstrStream<'il>) {
        let mut altars = self.altars.borrow_mut();
        altars.push(AltarData::new(ret_ty));
        let mut map = self.local_hir_ids_to_altar.borrow_mut();

        for input in inputs {
            let input_ty = self.session.lower_ty(input.ty);
            let altar_id = altars.push(AltarData::new(input_ty));
            map.insert(input.hir_id, altar_id);
        }

        block
            .stmts
            .iter()
            .filter_map(|stmt| {
                if let StmtKind::Local(local) = stmt.kind {
                    return Some(local);
                }
                None
            })
            .map(|local| {
                let altar_ty = self.types.local_var_ty(local.hir_id);
                (altars.push(AltarData::new(altar_ty)), local.hir_id)
            })
            .for_each(|(alt_id, hir_id)| {
                map.insert(hir_id, alt_id);
            });

        drop(altars);
        drop(map);

        TacGenerator::new(self.session, self).generate(block)
    }

    pub fn altar_for_hir_var(&self, hir_id: HirId) -> AltarId {
        self.local_hir_ids_to_altar
            .borrow()
            .get(&hir_id)
            .copied()
            .expect("given `HirId` wasn't mapped to any Altar!")
    }
}

pub fn lower_universe<'il>(session: &'il Session<'il>, universe: &'il Universe<'il>) {
    use crate::hir::node::{BindItemKind, ThingKind};
    let mut builder = IrBuilder::new(session);

    for thing in universe.things {
        match thing.kind {
            ThingKind::Fn { name: _, sig: _ } => {
                builder.build_ir_fun(thing.def_id);
            }

            ThingKind::Bind(bind) => {
                for item in bind.items {
                    if let BindItemKind::Fun { sig: _, name: _ } = item.kind {
                        builder.build_ir_fun(thing.def_id);
                    }
                }
            }
            _ => (),
        }
    }
}

pub struct TacGenerator<'il, 'lv> {
    s: &'il Session<'il>,
    l: &'lv FnLowerer<'il>,
    ops: InstrStream<'il>,
    labels: LabelVec<usize>,
    loop_exit_label: Option<LabelId>,
}

impl<'il, 'lv> TacGenerator<'il, 'lv>
where
    'il: 'lv,
{
    pub fn new(s: &'il Session<'il>, l: &'lv FnLowerer<'il>) -> Self {
        Self {
            s,
            l,
            ops: InstrStream::new(),
            labels: LabelVec::new(),
            loop_exit_label: None,
        }
    }

    pub fn generate(mut self, block: &Block<'_>) -> (LabelVec<usize>, InstrStream<'il>) {
        self.handle_block(block, Some(AltarId::ZERO));
        (self.labels, self.ops)
    }

    fn handle_local(&mut self, loc: &Local<'_>) {
        if let Some(loc_init) = loc.init {
            let altar = self.get_altar(loc);
            let _ = self.handle_expr(loc_init, Some(altar));
        }
    }

    #[allow(clippy::too_many_lines)]
    pub fn handle_expr(&mut self, expr: &Expr<'_>, result: Option<AltarId>) -> Operand {
        match expr.kind {
            ExprKind::Index {
                index: _,
                indexed_thing: _,
            } => todo!(),

            ExprKind::MethodCall {
                receiver,
                method: _, // not needed
                args,
            } => {
                let method_def_id = self.l.ty_table().resolve_method(expr.hir_id);
                let altar = result.unwrap_or_else(|| {
                    let ty = self.s.fn_sig_for(method_def_id).output;
                    self.l.new_temporary(ty)
                });

                let args = std::iter::once(receiver)
                    .chain(args.iter())
                    .map(|expr| self.handle_expr(expr, None))
                    .collect();

                self.ops.emit_call(method_def_id, args, altar);

                Operand::Variable(altar)
            }
            ExprKind::CommaSep(exprs) => {
                let mut iter = exprs.iter();

                if let Some(first) = iter.next() {
                    self.handle_expr(first, result);

                    for expr in iter {
                        self.handle_expr(expr, None);
                    }
                }

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Break => {
                let label = self
                    .loop_exit_label
                    .expect("ast lowering should catch this");
                self.ops.emit_goto(label);

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Return { expr } => {
                if let Some(expr) = expr {
                    self.handle_expr(expr, result);
                }

                self.ops.emit_return();

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Literal(literal) => {
                let scalar = match literal {
                    HirLiteral::Bool(bool) => Scalar::new_u8(u8::from(bool)),
                    HirLiteral::Uint(num) => Scalar::new_u64(num),
                    HirLiteral::Int(num) => Scalar::new_i64(num),
                    HirLiteral::Float(_float) => todo!(),
                    HirLiteral::Str(_str) => todo!(),
                };

                Operand::Immediate(scalar)
            }

            ExprKind::Binary { lhs, rhs, op } => {
                let lhs = self.handle_expr(lhs, None);
                let rhs = self.handle_expr(rhs, None);

                let altar = result.unwrap_or_else(|| {
                    let ty = self.l.ty_table().type_of(*expr);
                    self.l.new_temporary(ty)
                });

                self.ops.emit_bin_op(op, lhs, rhs, altar);

                Operand::Variable(altar)
            }

            ExprKind::Unary { target, op } => {
                let target = self.handle_expr(target, None);

                let altar = result.unwrap_or_else(|| {
                    let ty = self.l.ty_table().type_of(*expr);
                    self.l.new_temporary(ty)
                });

                self.ops.emit_un_op(op, target, altar);
                Operand::Variable(altar)
            }

            ExprKind::AssignWithOp {
                variable,
                value,
                op,
            } => {
                let altar = result.unwrap_or_else(|| {
                    let ty = self.l.ty_table().type_of(*expr);
                    self.l.new_temporary(ty)
                });
                let var = self.handle_expr(variable, None);

                let target = self.get_altar_from_variable_expr(variable);
                let value = self.handle_expr(value, Some(target));

                self.ops.emit_bin_op(op.into(), var, value, altar);
                self.ops.emit_assign(target, Operand::Variable(altar));

                Operand::Variable(target)
            }

            // Somehow rewrite?
            ExprKind::Call { function, args } => self.handle_call_expr(function, args, result),

            ExprKind::If {
                condition,
                block,
                else_,
            } => {
                let result_temp = result.unwrap_or_else(|| {
                    let ty = self.l.ty_table().type_of(*expr);
                    self.l.new_temporary(ty)
                });
                self.handle_if_expr(condition, block, else_, result_temp);

                Operand::Variable(result_temp)
            }

            ExprKind::Block(block) => {
                let result_temp = result.unwrap_or_else(|| {
                    let ty = self.l.ty_table().type_of(*expr);
                    self.l.new_temporary(ty)
                });

                self.handle_block(block, result_temp.into());

                Operand::Variable(result_temp)
            }

            ExprKind::Field { src, field } => self.handle_field_expr(src, field),

            ExprKind::Path(path) => {
                log::debug!("path.res={:#?}", path.res);
                let Resolved::Local(hir_id) = path.res else {
                    unreachable!()
                };

                Operand::Variable(self.l.altar_for_hir_var(hir_id))
            }

            ExprKind::Assign { variable, value } => {
                let altar = self.get_altar_from_variable_expr(variable);
                let rvalue = self.handle_expr(value, None);
                self.ops.emit_assign(altar, rvalue);

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::List(..) => todo!("debatable"),

            ExprKind::Loop { body, reason: _ } => self.handle_loop_expr(body),
        }
    }

    pub fn handle_loop_expr(&mut self, body: &Block<'_>) -> Operand {
        let loop_label = self.new_label();
        self.labels[loop_label] = self.ops.tac().len();
        let exit_label = self.new_label();

        let old = self.loop_exit_label.replace(loop_label);
        self.handle_block(body, None);
        self.loop_exit_label = old;

        self.labels[exit_label] = self.ops.tac().len();
        self.loop_exit_label.take();

        Operand::Variable(AltarId::NIL_ALTAR)
    }

    pub fn handle_field_expr(&mut self, src: &Expr<'_>, field: SymbolId) -> Operand {
        let src_instance = self.l.ty_table().type_of(*src).expect_instance();
        let field_id = src_instance
            .fields
            .iter()
            .position(|field_def| field_def.name == field)
            .map(FieldId::new_usize)
            .expect("typeck didn't catch this?");

        let Operand::Variable(altar_id) = self.handle_expr(src, None) else {
            panic!("todo: message for this")
        };

        let projected = self.l.project_altar(
            altar_id,
            Proj::Field {
                field: field_id,
                source: altar_id,
            },
        );

        Operand::Variable(projected)
    }

    pub fn handle_call_expr(
        &mut self,
        function: &Expr<'_>,
        args: &[Expr<'_>],
        result: Option<AltarId>,
    ) -> Operand {
        let ExprKind::Path(pat) = function.kind else {
            unreachable!()
        };

        match pat.res {
            Resolved::Def(id, DefType::Fun) => {
                let altar = result.unwrap_or_else(|| {
                    let ty = self.s.fn_sig_for(id).output;
                    self.l.new_temporary(ty)
                });

                let args = args
                    .iter()
                    .map(|expr| self.handle_expr(expr, None))
                    .collect();

                self.ops.emit_call(id, args, altar);
                Operand::Variable(altar)
            }

            Resolved::Def(id, DefType::AdtCtor) => {
                let altar = result.unwrap_or_else(|| {
                    let ty = self.s.fn_sig_for(id).output;
                    self.l.new_temporary(ty)
                });

                let adt_sig = self.s.fn_sig_for(id);
                let instc = adt_sig.output.expect_instance();
                let args = args
                    .iter()
                    .map(|expr| self.handle_expr(expr, None))
                    .collect();

                self.ops.emit_constr(instc, args, altar);

                Operand::Variable(altar)
            }

            _ => unreachable!(),
        }
    }

    pub fn handle_if_expr(
        &mut self,
        cond: &Expr<'_>,
        block: &Block<'_>,
        else_: Option<&Expr<'_>>,
        result_temp: AltarId,
    ) {
        let cond_op = self.handle_expr(cond, None);
        let true_label = self.new_label();
        let false_label = self.new_label();
        let end_label = self.new_label();

        self.ops.emit_branch(cond_op, true_label, false_label);
        self.labels[true_label] = self.ops.tac().len();

        self.handle_block(block, Some(result_temp));

        self.ops.emit_goto(end_label);
        self.labels[false_label] = self.ops.tac().len();

        if let Some(otherwise) = else_ {
            self.handle_expr(otherwise, Some(result_temp));
        }

        self.labels[end_label] = self.ops.tac().len();
    }

    // pub fn handle_if_expr_inner(
    //     &mut self,
    //     cond: &Expr<'_>,
    //     block: &Block<'_>,
    //     result_temp: AltarId,
    //     end_label: LabelId,
    // ) {
    //     let cond_op = self.handle_expr(cond, None);
    //     let true_label = self.new_label();
    //     let false_label = self.new_label();

    //     self.ops.emit_branch(cond_op, true_label, false_label);
    //     self.labels[true_label] = self.ops.tac().len();
    //     self.handle_block(block, Some(result_temp));
    //     self.ops.emit_goto(end_label);
    //     self.labels[false_label] = self.ops.tac().len();
    // }

    pub fn handle_block(&mut self, block: &Block<'_>, result: Option<AltarId>) {
        for stmt in block.stmts {
            match stmt.kind {
                StmtKind::Local(local) => self.handle_local(local),
                StmtKind::Expr(expr) => {
                    self.handle_expr(expr, result);
                }

                StmtKind::Thing(..) => (),
            }
        }

        match block.expr {
            None => self.l.new_temporary(self.s.nil()),
            Some(expr) => {
                let op = self.handle_expr(expr, None);
                let temp = result
                    .unwrap_or_else(|| self.l.new_temporary(self.l.ty_table().type_of(*expr)));

                self.ops.emit_assign(temp, op);
                temp
            }
        };
    }

    pub fn new_label(&mut self) -> LabelId {
        self.labels.push(usize::MAX)
    }

    pub fn get_altar(&mut self, loc: &Local<'_>) -> AltarId {
        self.l.altar_for_hir_var(loc.hir_id)
    }

    pub fn get_altar_from_variable_expr(&self, expr: &Expr<'_>) -> AltarId {
        let ExprKind::Path(path) = expr.kind else {
            unreachable!("lhs of `assign` is not a path")
        };

        match path.res {
            Resolved::Local(id) => self.l.altar_for_hir_var(id),
            _ => todo!("idk to explode or not"),
        }
    }
}
