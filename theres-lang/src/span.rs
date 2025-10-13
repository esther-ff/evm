use crate::sources::SourceId;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub sourceid: SourceId,
}

impl Span {
    pub const DUMMY: Self = Self {
        start: u32::MAX,
        end: u32::MAX,
        line: u32::MAX,
        sourceid: SourceId::DUMMY,
    };

    pub fn new(start: u32, end: u32, line: u32, sourceid: SourceId) -> Self {
        Self {
            start,
            end,
            line,
            sourceid,
        }
    }

    pub fn start(&self) -> u32 {
        self.start
    }

    pub fn end(&self) -> u32 {
        self.end
    }

    #[track_caller]
    pub fn between(left: Self, right: Self) -> Span {
        debug_assert!(left.sourceid == right.sourceid);
        Span::new(left.start, right.end, right.line, right.sourceid)
    }
}
