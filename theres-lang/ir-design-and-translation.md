# Design of the PILL

The name isn't that stupid...
it stands for the **P**uppygirl **I**ntermediate **L**owering **L**anguage
the idea of is it to represent the program as a simple graph built from basic block amenable to analysis but also easy to translate into SSA form.

## Some examples

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

## Terminators
The `exit` describes a terminator of the block where it diverges by returning, calling a function, doing a direct goto or a switch or becomes unreachable.

I think these terminators would be enough for the language at this time:
- `goto` for simple jumps
- `call` for function calls
- `switch` for if and eventually match statements
- `return` for returning from a function

I see a possible use for some sort a `unreachable` terminator
that would describe a block that is unreachable (duh)

## Instructions of the IR
The following instructions should be enough to handle the language:
- arithmetic operations like `Add`, `Sub`, `Mul`, `Div`, `Mod`, `BitOr` and `BitAnd`
- comparisons like `Greater`, `Equal` and `Lesser``
- operations like `Index` for lists and strings (i don't know how i'll handle slicing with ranges)
- constructors for `instance`s

With this semi-spec we could try translating another program to the IL by hand
```rs
instance Vector3 (
    x: f32,
    y: f32,
    z: f32,
)

fun mkVector(cond: i32) => Vector3 {
    if cond == 0 {
        Vector3(0.0, 0.0, 0.0)
    } else if cond == 1 {
        Vector3(0.1, 0.1, 0.1)
    } else {
        Vector(1.1, 1.1, 1.1)
    }
}

fun main() => nil {
    let vector: Vector3 = mkVector(2)
}
```

The IL for this could look like:
```rs
fun mkVector(cond: i32) => Vector3 {
  altar ret: Vector3
  
  -- args --
  cond: i32

  bb0: {
    exit: switch(cond)
            | 0 -> bb1
            | 1 -> bb2
            | otherwise -> bb3
`  }

  bb1: {
    ret = Construct(Vector3, 0.0_f32, 0.0_f32, 0.0_f32)

    exit: goto -> bb4
  }

  bb2: {
    ret = Construct(Vector3, 0.1_f32, 0.1_f32, 0.1_f32)

    exit: goto -> bb4
  }

  bb3: {
    ret = Construct(Vector3, 1.1_f32, 1.1_f32, 1.1_f32)

    exit: goto -> bb4
  }

  bb4: {
    exit: return
  }
}

fun main() => nil {
  altar ret: nil

  -- user variables --
  altar _0: Vector3 >> "vector"

  bb0: {
    exit: call (mkVector, 3_i32, ret: _0) -> bb1
  }

  bb1 {
    exit: return
  }
}
```

The idea of slightly abstracting away constructing an instance allows us to make it opaque enough to implement it in a VM and implement it in a native runtime existing as garbage collected pointers.
