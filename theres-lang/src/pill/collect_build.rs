use crate::air::def::{DefId, DefType};
use crate::pill::body::Pill;
use crate::pill::cfg::{Operand, Stmt, StmtKind};
use crate::pill::visitor::{PillVisitor, visit_stmt};
use crate::session::Session;
use crate::types::ty::{ParamTy, Ty, TyKind};

use std::collections::HashSet;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BuildItem<'il> {
    did: DefId,
    params: &'il [Ty<'il>],
}

struct BuildCollector<'il> {
    queue: Vec<BuildItem<'il>>,
    visit: HashSet<BuildItem<'il>>,
    body: Option<&'il Pill<'il>>,
    cx: &'il Session<'il>,
    did: DefId,

    cache: Vec<Ty<'il>>,
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
        if let StmtKind::Call { fun, args, .. } = stmt.kind() {
            let ty = fun.ty(self.body().local_data(), self.cx);

            let (mut item, did) = match *ty {
                TyKind::FnDef(did) if self.cx.is_native_fn(did) => return,
                TyKind::FnDef(did) => (BuildItem { did, params: &[] }, did),

                TyKind::Lambda(env) if self.did != env.did => (
                    BuildItem {
                        did: env.did,
                        params: &[],
                    },
                    env.did,
                ),

                TyKind::Param {
                    kind: ParamTy::Fun { .. },
                    ..
                } => return,

                _ => unreachable!(),
            };

            let inputs = if let DefType::Lambda = self.cx.def_type(did) {
                let parent = self.cx.air_get_parent(did);
                let types = self.cx.typeck(parent);
                types.lambda_type(did).expect_lambda().all_inputs
            } else {
                self.cx.fn_sig_for(did).inputs
            };

            if self.cache.capacity() < args.len() {
                self.cache.reserve(args.len());
            }

            for (sig_input, arg) in inputs.iter().zip(args) {
                let ty = arg.ty(self.body().local_data(), self.cx);
                dbg!(sig_input, ty);

                if sig_input.is_param() {
                    self.cache.push(ty);
                }
            }

            item.params = self.cx.arena().alloc_from_iter(self.cache.iter().copied());
            self.visit.insert(item);
            self.cache.clear();
            return;
        }

        visit_stmt(self, stmt);
    }

    fn visit_operand(&mut self, op: &Operand<'il>) {
        match op {
            Operand::Imm(imm) => {
                if let TyKind::FnDef(did) = *imm.ty() {
                    if !self.cx.is_native_fn(did) {
                        self.visit.insert(BuildItem { did, params: &[] });
                    }
                }
            }

            Operand::Use(acc) => {
                let base = self.body().local_data().get(acc.get_base()).unwrap().ty();
                let ty = acc.deduct_type(self.cx, base);
                match *ty {
                    TyKind::FnDef(did) => {
                        if !self.cx.is_native_fn(did) {
                            self.visit.insert(BuildItem { did, params: &[] });
                        }
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

pub fn collect_build_items<'cx>(cx: &'cx Session<'cx>, did: DefId) -> Vec<BuildItem<'cx>> {
    let mut collector = BuildCollector {
        queue: vec![],
        cache: vec![],
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

    collector.queue
}
