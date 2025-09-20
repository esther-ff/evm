use crate::hir::def::IntTy;

/// Lowest level representation of a Theres type.
pub enum IrType<'il> {
    /// Generally just refers to `instances`
    Complex(&'il [IrType<'il>]),

    /// unsigned ints
    Uint(IntTy),

    /// signed ints
    Int(IntTy),

    F32,
    F64,
    Nil,

    /// `[T]`
    /// This type is a bit specific because it doesn't truly
    /// explain the layout of a list
    /// however the actual machine layout would be
    /// (capacity, length, data ptr) except this needs to be opaque enough
    /// to be compiled to a vm too
    List(&'il IrType<'il>),

    /// Array, mostly useless but used for padding
    Array(&'il IrType<'il>, usize),

    /// Not present in the surface type system
    /// but due to GC use it's needed here
    /// the idea is if we have an instance like
    /// ```
    /// instance Alala {
    ///     field: Alala
    ///     field1: u32
    ///     field2: u32,
    /// }
    /// ```
    ///
    /// Then we turn that into
    /// ```
    /// Complex(&'il [Ptr<None>], Uint(IntTy::N32), Uint(IntTy::N32))
    /// ```
    ///
    /// `None` means the pointer points to the type being defined
    /// or can be casted to any type
    Ptr(Option<&'il IrType<'il>>),
}
