#[macro_export]
macro_rules! cache_fn {
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

        #[derive(Debug)]

        struct Cache {
            $(
                $name:
                CacheCell<($($param_ty),*), $ret>,
            )*
        }

        impl Cache {
            pub(crate) fn new() -> Self {
                Self {
                    $(
                        $name: CacheCell::new(::std::collections::HashMap::new()),
                    )*
                }
            }
        }

        impl Session {
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
                        &($($param,)*)
                    )
                    {
                        return *cache
                    }

                    let ret = $body(self, $($param,)*);
                    self.cache.$name.borrow_mut().insert
                        (($($param,)*),
                    ret);

                    ret
                }
            )*
        }
    };
}
