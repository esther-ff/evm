use std::collections::HashSet;

use crate::{
    air::def::DefId,
    pill::{body::Pill, cfg::Operand, visitor::PillVisitor},
    session::Session,
    types::ty::{Ty, TyKind},
};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct BuildItem<'il> {
    did: DefId,
    params: &'il [Ty<'il>],
}

struct BuildCollector<'il> {
    queue: Vec<BuildItem<'il>>,
    visit: HashSet<BuildItem<'il>>,
    cx: &'il Session<'il>,
    body: Option<&'il Pill<'il>>,
}

impl<'il> BuildCollector<'il> {
    fn body(&self) -> &'il Pill<'il> {
        self.body.unwrap()
    }
}

impl<'il> PillVisitor<'il> for BuildCollector<'il> {
    fn cx(&self) -> &'il Session<'il> {
        self.cx
    }

    fn visit_body(&mut self, body: &'il Pill<'il>) {
        self.body.replace(body);

        for (bb, data) in body.cfg.blocks() {
            self.visit_basic_block(bb, data);
        }
    }

    fn visit_operand(&mut self, op: &Operand<'il>) {
        match op {
            Operand::Imm(imm) => {
                log::debug!("BuildCollector: function called <{imm:?}>");
                if let TyKind::FnDef(did) = *imm.ty() {
                    self.visit.insert(BuildItem { did, params: &[] });
                }
            }

            Operand::Use(acc) => {
                let base = self.body().local_data(acc.get_base()).ty();
                let ty = acc.deduct_type(self.cx, base);
                match *ty {
                    TyKind::FnDef(did) => {
                        self.visit.insert(BuildItem { did, params: &[] });
                    }
                    TyKind::Lambda(env) => {
                        self.visit.insert(BuildItem {
                            did: env.did,
                            params: &[],
                        });
                    }

                    _ => (),
                }
            }
        }
    }
}

pub fn collect_build_items<'cx>(cx: &'cx Session<'cx>, did: DefId) {
    let mut collector = BuildCollector {
        queue: vec![],
        visit: HashSet::new(),
        cx,
        body: None,
    };

    collector.visit.insert(BuildItem { did, params: &[] });

    let mut scratch = HashSet::with_capacity(64);
    loop {
        if collector.visit.is_empty() {
            break;
        }

        collector.visit.clone_into(&mut scratch);
        collector.visit.clear();

        for ele in &scratch {
            let body = cx.build_pill(ele.did);
            collector.visit_body(body);
        }
    }

    dbg!(&collector.queue);
}
