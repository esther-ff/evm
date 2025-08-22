# Creating a middle-level IR and lowering it to... something?

So i'd want a comfortable to analyze, basic-block based, SSA-form, semi-typed IR.

I think the first draft is of course going to be rough, but let's create some IR for a simple function:
```rs
fun func(arg: i32) -> i32 {
    let a: i32 = 1;
    let b: i32 = 1;

    if arg == 1 {
        return a+b
    } else {
        return a*b
    }
}
```

The IR for this could look like: 
```
fun func(arg: i32) -> i32:
  _0: i32; // return place
  _1: i32; // our a
  _2: i32; // our b
  _3: i32; // intermediate for the math ops
  _4: bool; // intermediate for the comparison
  _5: i32 // our arg


  bb0:
    _4.0 = cmp(_5, imm 1_i32)

    exit: switch
      1 -> bb1
      otherwise -> bb2

  bb1:
    _0.0 = add(i32, _1, _2)

    exit: return _0.0

  bb2:
    _0.1 = mul(i32, _1, _2)

    exit: ret _0.1
```

This looks relatively clean and simple however i wonder how would it look where SSA's features shine a bit.

Let's take a function like:
```rs
fun branching(num: u8) => i32 {
    let a;

    if num == 1 {
        a = 4
    } else if num == 2 {
        a = 5
    } else {
        a = 6
    }

    return a + 1
}
```

The IR for that could roughly look like (not-SSA):
```
fun branching(num: u8) => i32:
  _0: i32 // return
  _1: i32 // a
  _2: u8  // num

  bb0:
    exit: switch _2
      1 -> bb1
      2 -> bb2
      otherwise -> bb3

  bb1:
    _1 = 4

    goto -> bb4

  bb2:
    _1 = 5

    exit: goto -> bb4

  bb3:
    _1 = 6

    exit: goto -> bb4

  bb4:
    _0 = add(i32, _1, imm 1_u32)
    ret _0
```

with SSA it would be:
```
fun branching(num: u8) => i32:
  _1: i32 // a
  _2: u8  // num

  bb0:
    exit: switch _2
      1 -> bb1
      2 -> bb2
      otherwise -> bb3

  bb1:
    _1.0 = 4

    goto -> bb4

  bb2:
    _1.1 = 5

    exit: goto -> bb4

  bb3:
    _1.2 = 6

    exit: goto -> bb4

  bb4:
    _1.3 = phi(
        (bb1, _1.0),
        (bb2, _1.1),
        (bb3, _1.2),
    )
    ret _1.3
```

    
