use std::ops::Deref;

pub struct Mutation<T: ?Sized> {
    patient: T,
}

impl<T: ?Sized> Mutation<T> {
    pub fn from_ref(data: &T) -> &Self {
        unsafe { &*(std::ptr::from_ref::<T>(data) as *const Mutation<T>) }
    }
}

impl<T: ?Sized> Deref for Mutation<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.patient
    }
}
