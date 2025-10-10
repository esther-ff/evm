use crate::{
    air::node::{Expr, ExprKind},
    pill::{
        body::{AltarId, Proj},
        cfg::{BasicBlock, Rvalue, Stmt},
        lowering::FnLowerer,
    },
    types::fun_cx::FieldId,
};

impl FnLowerer<'_> {
    pub fn lower_as_altar(&mut self, expr: &Expr<'_>, bb: BasicBlock) -> AltarId {
        match expr.kind {
            ExprKind::Index {
                index, // use it !!!
                indexed_thing,
            } => {
                let altar = self.lower_as_altar(indexed_thing, bb);
                let proj = Proj::Index(self.lower_as_operand(index, bb));
                self.project_altar(altar, proj, expr.air_id)
            }

            ExprKind::Field { src, field } => {
                let src_instance = self.ty_table().type_of(src).expect_instance();
                let field_id = src_instance
                    .fields
                    .iter()
                    .position(|field_def| field_def.name == field)
                    .map(FieldId::new_usize)
                    .expect("typeck didn't catch this?");

                let altar_id = self.lower_as_altar(src, bb);

                self.project_altar(
                    altar_id,
                    Proj::Field {
                        field: field_id,
                        source: altar_id,
                    },
                    expr.air_id,
                )
            }

            _ => {
                let ty = self.ty_table().type_of(expr);
                let temp = self.new_temporary(ty);

                let op = self.lower_as_operand(expr, bb);
                self.cfg.push_stmt(
                    bb,
                    Stmt::Assign {
                        dest: temp,
                        src: Rvalue::Regular(op),
                    },
                );

                temp
            }
        }
    }
}
