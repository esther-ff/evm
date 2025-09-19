use std::iter::once;

use crate::{
    ast::BinOp,
    hir::{
        def::{DefType, Resolved},
        node::{Expr, ExprKind, HirLiteral},
    },
    pill::{
        body::AltarId,
        cfg::{BasicBlock, BlockExit, Rvalue, Stmt},
        instr::Operand,
        lowering::FnLowerer,
        scalar::Scalar,
    },
};

impl FnLowerer<'_> {
    #[allow(clippy::too_many_lines)]
    pub fn lower_as_operand(&mut self, expr: &Expr<'_>, bb: BasicBlock) -> Operand {
        match expr.kind {
            ExprKind::Return { expr } => {
                if let Some(expr) = expr {
                    let src = self.lower_as_operand(expr, bb);

                    self.cfg.push_stmt(
                        bb,
                        Stmt::Assign {
                            dest: AltarId::ZERO,
                            src: Rvalue::Regular(src),
                        },
                    );
                }
                self.cfg.end_block(bb, BlockExit::Goto(BasicBlock::DUMMY));
                self.cfg.new_block();

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Block(block) => {
                // todo
                todo!("block")
            }

            ExprKind::If {
                condition,
                block,
                else_,
            } => todo!(),

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                let method_def_id = self.ty_table().resolve_method(expr.hir_id);

                let ty = self.session.fn_sig_for(method_def_id).output;
                let dest = self.new_temporary(ty);

                let args: Vec<_> = once(receiver)
                    .chain(args.iter())
                    .map(|expr| self.lower_as_operand(expr, bb))
                    .collect();

                self.cfg.push_stmt(
                    bb,
                    Stmt::Call {
                        fun: method_def_id,
                        ret: dest,
                        args,
                    },
                );

                Operand::Variable(dest)
            }

            ExprKind::Literal(lit) => {
                let scalar = match lit {
                    HirLiteral::Bool(bool) => Scalar::new_u8(u8::from(bool)),
                    HirLiteral::Uint(num) => Scalar::new_u64(num),
                    HirLiteral::Int(num) => Scalar::new_i64(num),
                    HirLiteral::Float(_float) => todo!(),
                    HirLiteral::Str(_str) => todo!(),
                };

                Operand::Immediate(scalar)
            }

            ExprKind::Binary { lhs, rhs, op } => {
                let ty = self.ty_table().type_of(*expr);
                let temp = self.new_temporary(ty);
                let lhs = self.lower_as_operand(lhs, bb);
                let rhs = self.lower_as_operand(rhs, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: temp,
                        src: Rvalue::Binary { op, lhs, rhs },
                    },
                );

                Operand::Variable(temp)
            }

            ExprKind::Unary { op, target } => {
                let ty = self.ty_table().type_of(*expr);
                let temp = self.new_temporary(ty);
                let val = self.lower_as_operand(target, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: temp,
                        src: Rvalue::Unary { op, val },
                    },
                );

                Operand::Variable(temp)
            }

            ExprKind::Assign { variable, value } => {
                let dest = self.lower_as_altar(variable, bb);
                let src = Rvalue::Regular(self.lower_as_operand(value, bb));
                self.cfg.push_stmt(bb, Stmt::Assign { dest, src });
                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Field { .. } | ExprKind::Index { .. } => {
                let altar = self.lower_as_altar(expr, bb);
                Operand::Variable(altar)
            }

            ExprKind::AssignWithOp {
                variable,
                value,
                op,
            } => {
                let op: BinOp = op.into();

                let lhs = self.lower_as_operand(variable, bb);
                let rhs = self.lower_as_operand(value, bb);
                let dest = self.lower_as_altar(variable, bb);

                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest,
                        src: Rvalue::Binary { op, lhs, rhs },
                    },
                );

                Operand::Variable(AltarId::NIL_ALTAR)
            }

            ExprKind::Call { function, args } => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.lower_as_operand(arg, bb))
                    .collect();

                let ExprKind::Path(pat) = function.kind else {
                    unreachable!()
                };

                match pat.res {
                    Resolved::Def(fun, DefType::Fun) => {
                        let ty = self.session.fn_sig_for(fun).output;
                        let dest = self.new_temporary(ty);

                        self.cfg.push_stmt(
                            bb,
                            Stmt::Call {
                                fun,
                                ret: dest,
                                args,
                            },
                        );
                        Operand::Variable(dest)
                    }

                    Resolved::Def(id, DefType::AdtCtor) => {
                        let ty = self.session.fn_sig_for(id).output;
                        let dest = self.new_temporary(ty);
                        let adt_sig = self.session.fn_sig_for(id);
                        let def = adt_sig.output.expect_instance();

                        self.cfg.push_stmt(
                            bb,
                            Stmt::Assign {
                                dest,
                                src: Rvalue::Make { def, args },
                            },
                        );

                        Operand::Variable(dest)
                    }

                    _ => unreachable!(),
                }
            }

            _ => todo!(),
        }
    }
}
