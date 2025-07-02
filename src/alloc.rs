use std::collections::HashMap;
use std::ptr::NonNull;

pub(crate) struct Header {}
pub(crate) struct Memory {
    ptr: NonNull<u8>,
    free: usize,
    taken: usize,

    header_map: HashMap<NonNull<()>, Header>,
}
