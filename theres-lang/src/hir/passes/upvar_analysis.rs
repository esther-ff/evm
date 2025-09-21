use crate::hir::HirId;
use std::collections::HashSet;

struct LocalCollector {
    set: HashSet<HirId>,
}
