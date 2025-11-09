use std::collections::HashSet;

use crate::{
    air::def::{DefId, DefType},
    pill::{
        body::Pill,
        cfg::{Operand, Stmt, StmtKind},
        visitor::PillVisitor,
    },
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
    did: DefId,
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

    fn visit_stmt(&mut self, stmt: &Stmt<'il>) {
        match stmt.kind() {
            StmtKind::Call { fun, args, .. } => {
                let ty = fun.ty(self.body().local_data(), self.cx);

                let (mut item, did) = match *ty {
                    TyKind::FnDef(did) => (BuildItem { did, params: &[] }, did),

                    TyKind::Lambda(env) if self.did != env.did => (
                        BuildItem {
                            did: env.did,
                            params: &[],
                        },
                        env.did,
                    ),
                    _ => return,
                };

                let inputs = if let DefType::Lambda = self.cx.def_type(did) {
                    let parent = self.cx.air_get_parent(did);
                    let types = self.cx.typeck(parent);
                    types.lambda_type(did).expect_lambda().all_inputs
                } else {
                    self.cx.fn_sig_for(did).inputs
                };

                let mut cache = Vec::with_capacity(inputs.len());
                for (sig_input, arg_input) in inputs.iter().zip(
                    args.iter()
                        .map(|op| op.ty(self.body().local_data(), self.cx)),
                ) {
                    dbg!(sig_input, arg_input);

                    if sig_input.is_param() {
                        cache.push(arg_input);
                    }
                }

                item.params = self.cx.arena().alloc_from_iter(cache);

                self.visit.insert(item);
            }

            StmtKind::Assign {
                dest,
                src,
                bypass_const,
            } => (),

            StmtKind::CheckCond(..) | StmtKind::LocalLive(..) => {}
        }
    }

    fn visit_operand(&mut self, op: &Operand<'il>) {
        match op {
            Operand::Imm(imm) => {
                if let TyKind::FnDef(did) = *imm.ty() {
                    self.visit.insert(BuildItem { did, params: &[] });
                }
            }

            Operand::Use(acc) => {
                let base = self.body().local_data().get(acc.get_base()).unwrap().ty();
                let ty = acc.deduct_type(self.cx, base);
                match *ty {
                    TyKind::FnDef(did) => {
                        self.visit.insert(BuildItem { did, params: &[] });
                    }

                    TyKind::Lambda(env) if self.did != env.did => {
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
        did,
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
            collector.did = ele.did;
            collector.visit_body(body);
        }

        collector.queue.extend(collector.visit.iter().copied());
    }

    dbg!(&collector.queue);
}
