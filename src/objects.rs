#[derive(Debug, Clone, Copy)]
pub(crate) enum Value {
    Object(ObjRef),
    Number(u32),
    Nil,
    Function(FnRef),
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct FnRef(pub u32);

pub(crate) struct Functions(Vec<Func>);

impl Functions {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn insert(&mut self, f: Func) {
        self.0.push(f)
    }

    pub fn get(&self, fn_ref: FnRef) -> Option<&Func> {
        self.0.get(fn_ref.0 as usize)
    }
}

pub(crate) struct Func {
    jump_ip: usize,
    name: Box<str>,
    arity: u16,
}

impl Func {
    pub(crate) fn new<A>(jump_ip: usize, name: A, arity: u16) -> Self
    where
        A: Into<Box<str>>,
    {
        Self {
            name: name.into(),
            jump_ip,
            arity,
        }
    }

    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn arity(&self) -> u16 {
        self.arity
    }

    pub(crate) fn jump_ip(&self) -> usize {
        self.jump_ip
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ObjRef(u32);

pub(crate) enum Object {
    Todo,
}

pub(crate) struct Objects {
    storage: Vec<Object>,
}

impl Objects {
    pub(crate) fn new() -> Self {
        Self {
            storage: Vec::new(),
        }
    }

    pub(crate) fn get(&mut self, idx: usize) -> Option<&mut Object> {
        self.storage.get_mut(idx)
    }

    pub(crate) fn insert(&mut self, obj: Object) {
        self.storage.push(obj);
    }

    // pub(crate) fn inc_ref_count(&mut self, idx: usize) -> Option<usize> {
    //     self.storage.get_mut(idx).map(|obj| {
    //         let old = obj.ref_count;
    //         obj.ref_count += 1;

    //         old
    //     })
    // }

    // pub(crate) fn dec_ref_count(&mut self, idx: usize) -> Option<usize> {
    //     self.storage.get_mut(idx).map(|obj| {
    //         let old = obj.ref_count;
    //         obj.ref_count -= 1;

    //         old
    //     })
    // }
}
