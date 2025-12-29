#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[allow(clippy::struct_field_names)]
pub struct Flags {
    pub dump_hir: HirDump,
    pub dump_ast: bool,
    pub dump_eair: bool,
    pub dump_pill: bool,
    pub log_level: log::Level,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum HirDump {
    None,
    Simple,
    WithBodies,
}
