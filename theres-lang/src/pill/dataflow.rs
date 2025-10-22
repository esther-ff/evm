use crate::{
    id::IdxVec,
    pill::{
        body::Local,
        cfg::{BasicBlock, BlockExitKind, Cfg, StmtKind},
    },
};

use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct DataflowState {
    gen_: HashSet<Local>,
    in_: HashSet<Local>,
    out: HashSet<Local>,
}

struct MaybeInitVariables {
    states: IdxVec<BasicBlock, DataflowState>,
}

impl MaybeInitVariables {
    fn compute_gen<'a>(&mut self, cfg: &'a Cfg<'a>) {
        for (bb, data) in cfg.blocks() {
            let gen_set = &mut self.states[bb].gen_;

            for instr in data.stmts() {
                if let StmtKind::Assign { dest, .. } = instr.kind()
                    && let Some(base) = dest.only_local()
                {
                    gen_set.insert(base);
                }
            }
        }
    }

    #[allow(clippy::assigning_clones)]
    fn analyze<'a>(&mut self, cfg: &'a Cfg<'a>) {
        let mut changed = true;

        while changed {
            changed = false;
            for (bb, data) in cfg.blocks() {
                let old_out = self.states[bb].out.clone();

                self.states[bb].in_.clear();

                let preds = data.predecessors();
                if let Some(first) = preds.first().copied() {
                    self.states[bb].in_ = self.states[first].out.clone();

                    for pred in &preds[1..] {
                        self.states[bb].in_ = self.states[bb]
                            .in_
                            .intersection(&self.states[*pred].out)
                            .copied()
                            .collect();
                    }
                }

                self.states[bb].out = self.states[bb].in_.clone();

                self.states[bb].out = self.states[bb]
                    .out
                    .union(&self.states[bb].gen_)
                    .copied()
                    .collect();

                changed = self.states[bb].out != old_out;
            }
        }
    }
}

pub fn analyze_maybe_init_variables<'a>(cfg: &'a Cfg<'a>) {
    let base = DataflowState {
        gen_: HashSet::new(),
        in_: HashSet::new(),
        out: HashSet::new(),
    };

    let mut variables = MaybeInitVariables {
        states: IdxVec::new_from_vec(vec![base; cfg.len()]),
    };

    variables.compute_gen(cfg);
    variables.analyze(cfg);

    let mut alive = HashSet::new();
    for (bb, data) in cfg.blocks() {
        let state = &mut variables.states[bb];
        alive.clone_from(&state.in_);

        for stmt in data.stmts() {
            match stmt.kind() {
                StmtKind::Assign { dest, src: _ } => {
                    if let Some(base) = dest.only_local() {
                        alive.insert(base);
                        continue;
                    }

                    let base = dest.get_base();
                    if !alive.contains(&base) {
                        todo!("uninit use of variable")
                    }

                    todo!("travel through rvalue")
                }

                StmtKind::Call { fun, ret, args } => todo!(),

                StmtKind::CheckCond(op) => todo!(),

                StmtKind::Nop | StmtKind::LocalLive(..) => (),
            }
        }
    }
}
