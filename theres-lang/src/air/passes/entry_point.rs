use crate::air::def::{DefId, DefType, Resolved};
use crate::air::node::{Expr, ExprKind};
use crate::air::visitor::{AirVisitor, walk_expr};
use crate::session::Session;
use crate::types::fun_cx::TypeTable;
use crate::visitor_common::VisitorResult;
use crate::{try_visit, visit_iter};
use std::collections::HashSet;

struct BuildCollector<'hs, 'cx> {
    cx: &'cx Session<'cx>,
    needed: &'hs mut HashSet<DefId>,
    types: TypeTable<'cx>,
}

impl<'vis> AirVisitor<'vis> for BuildCollector<'_, 'vis> {
    type Result = ();

    fn visit_expr(&mut self, expr: &'vis Expr<'vis>) -> Self::Result {
        match expr.kind {
            ExprKind::Lambda(lambda) => {
                self.needed.insert(lambda.did);

                let body = self.cx.air_body(lambda.did);
                self.visit_expr(body);
            }
            ExprKind::Call { function, args } => {
                if let ExprKind::Path(path) = function.kind
                    && let Resolved::Def(did, DefType::Fun) = path.res
                {
                    self.needed.insert(did);
                    let body = self.cx.air_body(did);
                    self.visit_expr(body);
                }

                visit_iter!(v:self, m:visit_expr, args);
            }

            ExprKind::MethodCall {
                receiver,
                method: _,
                args,
            } => {
                visit_iter!(v:self, m:visit_expr, args);
                self.visit_expr(receiver);

                let did = self.types.resolve_method(expr.air_id);
                self.needed.insert(did);
                let body = self.cx.air_body(did);
                self.visit_expr(body);
            }

            _ => walk_expr(self, expr),
        }
    }
}

pub fn gather_items_for_build<'cx>(
    cx: &'cx Session<'cx>,
    def_id: DefId,
    needed: &mut HashSet<DefId>,
) {
    let types = cx.typeck(def_id);
    let body = cx.air_body(def_id);
    let mut col = BuildCollector { cx, needed, types };

    col.visit_expr(body);
}
