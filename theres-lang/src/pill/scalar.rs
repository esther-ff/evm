use core::fmt::{Debug, Display};
use core::num::NonZero;

#[derive(Clone, Copy)]
pub struct Scalar {
    bytes: [u8; 16],
    size: NonZero<usize>,
}

macro_rules! scalar_impls {
    ($($ty:ty > $to:ident > $new: ident),*) => {
        $(
            pub fn $new(val: $ty) -> Self {
                use ::std::io::Write as _;

                let bytes = val.to_ne_bytes();
                let mut arr: [u8; 16] = [0; 16];
                let _ = (&mut arr as &mut [u8]).write(&bytes);

                Self {
                    size: NonZero::new(size_of::<$ty>()).expect("passed in a ZST?"),
                    bytes: arr,
                }
            }

            pub fn $to(self) -> $ty {
                assert!(self.size.get() == size_of::<$ty>(), "size was meant to be: {}, was: {}", size_of::<$ty>(), self.size.get());

                let num_bytes = self.bytes[..size_of::<$ty>()]
                    .try_into()
                    .expect("infallible");

                <$ty>::from_ne_bytes(num_bytes)
            }
        )*
    };
}

impl Scalar {
    scalar_impls! {
        u8 > to_u8 > new_u8,
        u16 > to_u16 > new_u16,
        u32 > to_u32 > new_u32,
        u64 > to_u64 > new_u64,
        i8 > to_i8 > new_i8,
        i16 > to_i16 > new_i16,
        i32 > to_i32 > new_i32,
        i64 > to_i64 > new_i64,
        f64 > to_f64 > new_f64,
        f32 > to_f32 > new_f32
    }

    pub fn to_bool(self) -> bool {
        let byte = self.to_u8();

        assert!(byte < 2, "`to_bool` has an invalid val for a bool: {byte}!");

        byte == 1
    }

    pub fn new_bool(val: bool) -> Self {
        Self::new_u8(u8::from(val))
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", u128::from_ne_bytes(self.bytes))
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Scalar as Debug>::fmt(self, f)
    }
}

#[test]
fn scalar() {
    let sc = Scalar::new_u8(u8::MAX);
    let num = sc.to_u8();
    assert!(num == u8::MAX);

    let sc = Scalar::new_u16(u16::MAX);
    let num = sc.to_u16();
    assert!(num == u16::MAX);

    let sc = Scalar::new_u32(u32::MAX);
    let num = sc.to_u32();
    assert!(num == u32::MAX);

    let sc = Scalar::new_u64(u64::MAX);
    let num = sc.to_u64();
    assert!(num == u64::MAX);
}
