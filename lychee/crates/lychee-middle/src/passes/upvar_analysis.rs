use lychee_air::lowering_ast::AirId;
use lychee_air::node::{Expr, ExprKind, Local, Path};
use lychee_air::visitor::{AirVisitor, walk_expr};
use lychee_util::def::{DefId, DefType, Resolved};

use crate::session::Session;
use std::collections::HashSet;

struct LocalCollector {
    set: HashSet<AirId>,
}

impl<'vis> AirVisitor<'vis> for LocalCollector {
    type Result = ();

    fn visit_local(&mut self, local: &'vis Local<'vis>) -> Self::Result {
        self.set.insert(local.air_id);
    }
}

struct UpvarCollector<'cx> {
    s: &'cx Session<'cx>,
    upvars: HashSet<AirId>,
    all_locals: HashSet<AirId>,
}

impl<'vis> AirVisitor<'vis> for UpvarCollector<'_> {
    type Result = ();

    fn visit_path(&mut self, path: &'vis Path<'vis>) -> Self::Result {
        if let Resolved::Local(air_id) = path.res
            && !self.all_locals.contains(&air_id)
        {
            self.upvars.insert(air_id);
        }
    }

    fn visit_expr(&mut self, expr: &'vis Expr<'vis>) -> Self::Result {
        if let ExprKind::Lambda(lambda) = expr.kind {
            for upvar in self.s.upvars_of(lambda.did) {
                if !self.all_locals.contains(upvar) {
                    self.upvars.insert(*upvar);
                }
            }
        }

        walk_expr(self, expr);
    }
}

pub fn analyze_upvars<'cx>(cx: &'cx Session<'cx>, did: DefId) -> &'cx HashSet<AirId> {
    assert!(
        matches!(cx.def_type(did), DefType::Lambda),
        "upvars for not lambda!"
    );

    let body = cx.air_body(did);
    let params = cx.air_get_lambda(did).inputs;

    let mut locals = LocalCollector {
        set: HashSet::new(),
    };

    for ele in params {
        locals.set.insert(ele.air_id);
    }
    locals.visit_expr(body);

    let mut upvars = UpvarCollector {
        s: cx,
        upvars: HashSet::new(),
        all_locals: locals.set,
    };

    upvars.visit_expr(body);

    cx.arena().alloc(upvars.upvars)
}
