use std::collections::HashMap;

use crate::hir::LateResolver;
use crate::hir::def::{DefId, DefMap, Definitions, Resolved};
use crate::hir::node::Node;
use crate::id::IdxVec;
use crate::parser::{AstId, AstIdMap};

crate::newtyped_index!(OwnerId, OwnerMap, OwnerVec);
crate::newtyped_index!(BodyId, BodyMap, BodyVec);
crate::newtyped_index!(LocalId, LocalMap, LocalVec);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct HirId {
    owner: OwnerId,
    itself: LocalId,
}

pub struct Mappings {
    instance_to_field_list: AstIdMap<Vec<AstId>>,
    field_id_to_instance: AstIdMap<AstId>,

    resolution_map: AstIdMap<Resolved<AstId>>,
}

pub struct HirMap<'hir> {
    nodes: LocalVec<Node<'hir>>,
    owner_id_to_local_id: OwnerMap<LocalId>,

    def_id_to_hir_id: DefMap<HirId>,
    hir_id_to_def_id: DefMap<HirId>,
}

impl HirMap<'_> {
    pub fn new() -> Self {
        Self {
            nodes: IdxVec::new(),
            owner_id_to_local_id: HashMap::new(),

            def_id_to_hir_id: HashMap::new(),
            hir_id_to_def_id: HashMap::new(),
        }
    }
}

pub struct HirLowerer<'hir> {
    current_owner: Option<OwnerId>,
    current_function: Option<DefId>,
    current_instance: Option<DefId>,

    definitions: Definitions,

    mappings: Mappings,

    local_id_counter: u32,
    owner_id_counter: u32,

    hir_map: HirMap<'hir>,
}

impl HirLowerer<'_> {
    pub fn new(r: LateResolver) -> Self {
        let mappings = Mappings {
            resolution_map: r.res_map,
            instance_to_field_list: r.instance_to_fields,
            field_id_to_instance: r.fields_to_instance,
        };

        Self {
            mappings,

            current_owner: None,
            current_function: None,
            current_instance: None,

            definitions: r.definitions,

            local_id_counter: 0,
            owner_id_counter: 0,

            hir_map: HirMap::new(),
        }
    }
}
