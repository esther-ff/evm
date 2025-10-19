use crate::pill::body::Pill;

pub trait PillVisitor<'vis> {
    fn visit_body(&mut self, body: Pill<'vis>);
}
