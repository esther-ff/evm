pub struct HirId {
    private: u32,
}

pub fn hir_id(i: u32) -> HirId {
    HirId(i)
}
