use crate::{
    air::def::DefId,
    pill::{cfg::Stmt, visitor::PillVisitor},
    session::Session,
    types::ty::Ty,
};

struct BuildItem<'il> {
    did: DefId,
    params: &'il [Ty<'il>],
}

struct BuildCollector<'il> {
    queue: Vec<BuildItem<'il>>,
    visit: Vec<BuildItem<'il>>,
    cx: &'il Session<'il>,
}

impl<'il> PillVisitor<'il> for BuildCollector<'il> {
    fn cx(&self) -> &'il Session<'il> {
        self.cx
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt<'il>) {
        todo!()
    }
}
