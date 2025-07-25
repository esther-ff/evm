use std::{io, path::Path};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OneWayVec<T>(Vec<T>);

impl<T> OneWayVec<T> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, item: T) {
        self.0.push(item);
    }

    pub fn get(&self, idx: usize) -> Option<&T> {
        self.0.get(idx)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineSpan {
    start: usize,
    end: usize,
}

impl LineSpan {
    pub const DUMMY: Self = Self {
        start: usize::MAX,
        end: usize::MAX,
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceId(u32);
impl SourceId {
    pub const DUMMY: Self = Self(u32::MAX);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceFile {
    id: SourceId,
    access_name: String,
    data: Box<str>,
    lines: Vec<LineSpan>,
}

impl SourceFile {
    pub fn new(id: SourceId, access_name: String, data: String) -> Self {
        let mut lines = vec![LineSpan::DUMMY];
        Self::count_lines_as_spans(&mut lines, data.as_bytes());

        Self {
            lines,
            data: data.into_boxed_str(),
            access_name,
            id,
        }
    }

    pub fn source_id(&self) -> SourceId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.access_name
    }

    fn count_lines_as_spans(storage: &mut Vec<LineSpan>, data: &[u8]) {
        let mut start = 0;

        for (ix, byte) in data.iter().enumerate() {
            if *byte == b'\n' {
                storage.push(LineSpan { start, end: ix });
                start = ix + 1;
            }

            if ix == data.len().saturating_sub(1) {
                storage.push(LineSpan { start, end: ix + 1 });
            }
        }
    }

    pub fn get_line(&self, idx: usize) -> Option<LineSpan> {
        self.lines.get(idx + 1).copied()
    }

    pub fn get_lines_from_to(&self, from: usize, to: usize) -> Option<Vec<&str>> {
        let slice = self.lines.get(from + 1..to + 1)?;

        slice
            .iter()
            .map(|span| {
                self.data
                    .get(span.start..span.end)
                    .expect("invalid line span")
            })
            .collect::<Vec<_>>()
            .into()
    }

    pub fn get_lines_above_below(&self, origin: usize, each: usize) -> Option<Vec<&str>> {
        self.get_lines_from_to(origin.saturating_sub(each), origin + each)
    }

    pub fn data(&self) -> &[u8] {
        self.data.as_bytes()
    }
}

pub trait FileManager {
    fn open_file(&mut self, path: &Path) -> io::Result<Vec<u8>>;
}

pub struct Sources<Io> {
    files: OneWayVec<SourceFile>,
    io: Io,
}

impl<Io> Sources<Io> {
    pub fn new(io: Io) -> Self {
        Self {
            io,
            files: OneWayVec::new(),
        }
    }
}

impl<Io: FileManager> Sources<Io> {
    pub fn open<A>(&mut self, filepath: A) -> io::Result<SourceFile>
    where
        A: AsRef<Path>,
    {
        let bytes = self.io.open_file(filepath.as_ref())?;
        let data = String::from_utf8(bytes).expect("file wasn't valid utf-8");
        let id = SourceId(self.files.len() as u32);
        let access_name = filepath.as_ref().to_string_lossy().into_owned();

        Ok(SourceFile::new(id, access_name, data))
    }

    pub fn get_by_source_id(&self, id: SourceId) -> &SourceFile {
        self.files
            .get(id.0 as usize)
            .expect("source ids should be valid")
    }
}

#[cfg(test)]
mod tests {
    use crate::sources::SourceFile;
    use crate::sources::SourceId;

    #[test]
    fn source_file_lines() {
        const DATA: &str = concat!("line 1\n", "line 2\n", "line 3\n", "line 4\n", "line 5");
        let file = SourceFile::new(SourceId(0), String::from("test"), DATA.to_string());

        let lines = file.get_lines_from_to(1, 3);
        dbg!(lines);

        let lines = file.get_lines_above_below(2, 2);
        dbg!(lines);
    }
}
