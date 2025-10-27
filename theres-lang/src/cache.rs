use crate::air::def::DefId;

#[macro_export]
macro_rules! cache {
    (
        [lock: $($lock:tt)*]
        $(
        $(#[$outer:meta])*
        $vis:vis fn $name:ident
        (
            $rf:tt
            $($lt:lifetime)?
            $($mut:ident)?
            !
            self,
            $(
                $param:ident: $param_ty:ty
            ),*
        )
        -> $ret: ty
        { $body:path }
        )+
    ) => {
        type CacheCell<K, V> = $($lock)*<::std::collections::HashMap<K, V>>;

        mod a {
            pub(crate) trait Detuple<T>: Sized {
                fn spec_into(self) -> T;
            }

            impl<T> Detuple<T> for (T,) {
                #[inline(always)]
                fn spec_into(self) -> T {
                    self.0
                }
            }

            impl<T> Detuple<T> for T {
                #[inline(always)]
                fn spec_into(self) -> T {
                    self
                }
            }
        }

        use a::Detuple as _;

        #[derive(Debug)]
        #[allow(unused_parens)]
        struct Cache<'cx> {
            _boo: ::core::marker::PhantomData<&'cx ()>,
            $(
                $name:
                CacheCell<($($param_ty),*), $ret>,
            )*
        }

        impl<'cx> Cache<'cx> {
            pub(crate) fn new() -> Self {
                Self {
                    _boo: ::core::marker::PhantomData,
                    $(
                        $name: CacheCell::new(::std::collections::HashMap::new()),
                    )*
                }
            }
        }

        #[allow(clippy::double_parens)]
        impl<'cx> Session<'cx> {
            $(
                $(
                    #[$outer]
                )*
                $vis fn $name
                (
                    $rf $($lt)? self, $($param: $param_ty,)*
                ) -> $ret
                {
                    if let Some(cache) = self.cache.$name.borrow().get(
                        &($($param,)*).spec_into()
                    )
                    {
                        return *cache
                    }

                    let ret = $body(self, $($param,)*);
                    self.cache.$name.borrow_mut().insert
                        (($($param,)*).spec_into(),
                    ret);

                    self.cache.$name.borrow_mut()[&(($($param,)*)).spec_into()]

                }
            )*
        }
    };
}

impl From<(DefId,)> for DefId {
    fn from(value: (DefId,)) -> Self {
        value.0
    }
}
impl<'a> From<&'a (DefId,)> for &'a DefId {
    fn from(value: &'a (DefId,)) -> Self {
        &value.0
    }
}
