use crate::{
    id::IdxVec,
    pill::{
        body::Local,
        cfg::{BasicBlock, Cfg, Operand, Rvalue, StmtKind},
        errors::PillError,
    },
    session::cx,
    span::Span,
};

use std::{collections::HashSet, mem};

#[derive(Debug, Clone, Default)]
pub struct DataflowState {
    gen_: HashSet<Local>,
    in_: HashSet<Local>,
    out: HashSet<Local>,
}

pub fn dataflow_states(cfg: &Cfg<'_>) -> IdxVec<BasicBlock, DataflowState> {
    let base: Vec<_> = std::iter::repeat_n(DataflowState::default(), cfg.len()).collect();
    let mut states: IdxVec<BasicBlock, _> = IdxVec::new_from_vec(base);

    for (bb, data) in cfg.blocks() {
        let gen_set = &mut states[bb].gen_;

        for instr in data.stmts() {
            if let StmtKind::LocalLive(loc) = instr.kind() {
                gen_set.insert(*loc);
            }
        }
    }

    let mut changed = true;

    while changed {
        changed = false;
        for (bb, data) in cfg.blocks() {
            let old_out = states[bb].out.clone();

            states[bb].in_.clear();

            let preds = data.predecessors();
            if let Some(first) = preds.first().copied() {
                let out = mem::take(&mut states[first].out);
                states[bb].in_.clone_from(&out);
                states[first].out = out;

                for pred in &preds[1..] {
                    states[bb].in_ = states[bb]
                        .in_
                        .intersection(&states[*pred].out)
                        .copied()
                        .collect();
                }
            }

            let in_ = mem::take(&mut states[bb].in_);

            states[bb].out.clone_from(&in_);
            states[bb].in_ = in_;
            states[bb].out = states[bb].out.union(&states[bb].gen_).copied().collect();

            changed = states[bb].out != old_out;
        }
    }

    states
}

fn analyze_operand(op: &Operand<'_>, alive: &HashSet<Local>, span: Span) {
    match op.maybe_use() {
        None => (),
        Some(loc) if alive.contains(&loc.get_base()) => (),
        Some(..) => cx(|cx| {
            cx.diag().emit_err(PillError::LocalNotInitialized, span);
        }),
    }
}

fn analyze_rvalue(rvalue: &Rvalue<'_>, alive: &HashSet<Local>, span: Span) {
    match rvalue {
        Rvalue::Binary { lhs, rhs, .. } => {
            analyze_operand(lhs, alive, span);
            analyze_operand(rhs, alive, span);
        }

        Rvalue::Unary { val, .. } => analyze_operand(val, alive, span),
        Rvalue::Adt { args, .. } => {
            for elm in args {
                analyze_operand(elm, alive, span);
            }
        }

        Rvalue::List(elems) => {
            for elm in elems {
                analyze_operand(elm, alive, span);
            }
        }

        Rvalue::Length(place) | Rvalue::AddrOf(place) => {
            let base = place.get_base();

            if !alive.contains(&base) {
                todo!("uninit var")
            }
        }
        Rvalue::Regular(op) => analyze_operand(op, alive, span),
    }
}

pub fn analyze_maybe_init_variables<'a>(cfg: &'a Cfg<'a>) {
    let mut states = dataflow_states(cfg);

    let mut alive = HashSet::new();
    for (bb, data) in cfg.blocks() {
        let state = &mut states[bb];
        alive.clone_from(&state.in_);

        for stmt in data.stmts() {
            let span = stmt.span();
            match stmt.kind() {
                StmtKind::Assign { dest, src, .. } => {
                    if let Some(base) = dest.only_local() {
                        alive.insert(base);
                        continue;
                    }

                    let base = dest.get_base();
                    if !alive.contains(&base) {
                        cx(|cx| {
                            cx.diag().emit_err(PillError::LocalNotInitialized, span);
                        });
                    }

                    analyze_rvalue(src, &alive, span);
                }

                StmtKind::Call { fun, ret: _, args } => {
                    analyze_operand(fun, &alive, span);

                    for arg in args {
                        analyze_operand(arg, &alive, span);
                    }
                }

                StmtKind::CheckCond(cond) => {
                    analyze_operand(cond, &alive, span);
                }

                StmtKind::LocalLive(..) => (),
            }
        }
    }
}
