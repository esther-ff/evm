# Thoughts about coercing a diverging marker type

Take a piece of code like:

```rs
fn panics() -> i32 {
    let a: i32 = panic!();
    return a
}
```


This is valid as the `!` type is coerced to `i32`
and the `return` is given `a` which is of type `i32`
due to the binding being declared with a type hint of `i32`
therefore it's sound.

```rs
fn weird() -> ! {
    return 1;
}
```

This on the other hand is not sound as it returns an `{integer}`
(defaulted to i32).

So, how can we simply solve this here? My idea here is when matching for
unifing types, we must define a clear `expected` and `got` type.

Which means in the first example if we unify the type of `a` type hint (`i32`) and the `!` we must place the `i32` type as the expected one due to the hint.
Essentially this shows that i can coerce the `diverges` type in Theres to any type only if it's a type on the `got` position, else im coercing some type `T`to a `diverges` which will break stuff up.

```rs
// <snip>
  (expected, TyKind::Diverges) => {
      // no action, it unifies
      // because the computation never finishes
  }
```

This seems to be the right way to handle it.

Though now i expose a really annoying problem: i might just mess up the order
so that begs the question whether i should make a type like

```rs
pub struct Unify<'ty> {
    expected: Ty<'ty>,
    got: Ty<'ty>,
}
```

Which i think could be nice to just place more care on the arguments,
since it might be hard to find this issue later.
