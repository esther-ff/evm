# Design of the PILL

The name isn't that stupid...
it stands for the **P**uppygirl **I**ntermediate **L**owering **L**anguage
the idea of is it to represent the program in a simple basic-block way
amenable to analysis but also easy to translate into SSA form to perform further analysis or constant evaluation.

let's imagine a function in Theres like
```rs
fun esprit() => [i32] {
    let base: [[i32]]
        = [
            [1,2,3],
            [4,5,6],
            [7,8,9]
          ];

    let add: i32 = base[1][1] + 1;
    let sub: i32 = base[2][2] - base[1][1];

    base[sub]
}
```

The IL generated for it would be:
```rs
fun esprit() => [i32] {
  altar ret: [i32]

  -- local vars --
  altar _0: [[i32]] >> "base"
  altar _1: i32     >> "add"
  altar _2: i32     >> "sub"

  -- temporaries --
  altar _3: i32 // temporary for add
  altar _4: i32 // lhs for sub
  altar _5: i32 // rhs for sub

  altar _6: [i32] // first index out of add
  altar _7: [i32] // first index out of sub lhs
  altar _8: [i32] // first index out of sub rhs

  bb0: {
    _6 = Index(_0, 1)
    _3 = Index(_6, 1)
    _1 = Add(_3, const 1_i32)

    _7 = Index(_0, 2)
    _4 = Index(_7, 2)
    _8 = Index(_0, 1)
    _5 = Index(_8, 1)
    _2 = Sub(_4, _5)

    ret = Index(_0, _2)

    exit: return
  }
}
```

The idea is that each `altar` represents a place in memory we store something, each "use" of an altar like in `Sub(_4, _5)` corresponds to using it as a operand, so just referencing the memory.
The `exit: return` semi-statement describes the end of this block is a return of the function.


Each subexpression is visibly broken into it's core components which simplifies the flow a lot!

Now how would branching look like?

Let's consider another function:
```rs
fun geist(cond: bool) => i32 {
    if cond {
        esprit()[1]
    } else {
        32
    }
}
```

In our IL, it would be like:
```rs
fun geist(cond: bool) => i32 {
  altar ret: i32

  -- args --
  altar cond: bool
  
  -- temporaries --
  altar _0: [i32] // `esprit` call

  bb0: {
    exit: switch(cond)
            | 0 -> bb1
            | otherwise -> bb2
  }

  bb1: {
    ret = const 32_i32

    exit: goto -> bb4
  }

  bb2: {
    exit: call (esprit, ret: _0) -> bb3
  }

  bb3: {
    ret = Index(_0, 1)

    exit: goto -> bb4
  }

  bb4: {
    exit: return 
  }
}
```

