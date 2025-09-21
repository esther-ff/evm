# Weird idea how to handle privacy in blocks and realms alike.

```rs
// scope #0
fn main() {
    // scope #1 (anchor: #0)

    {
        // scope #2 (anchor: #1)
        let x = 1;
    }

    {
        // scope #3 (anchor #1)
        let y = 2;
    }
}
```

Path undertaken: #0 -> #1 -> #2 -> #1 -> #3 -> #0

The idea is to build a scope map and a scope path
so we'd build a path like that to basically traverse the scopes later for resolving stuff like local variables.

This would allow me to first record the existence of items which allows us to function like a modern compiler.

How would the path look?
I think something like 
#0 -> #1 -> #2 -> #1 -> #3 -> #0

The steps taken would be roughly:
- Enter scope #0 -> resolve
- Enter scope #1 -> resolve
- Enter scope #2 -> resolve
- Enter scope #1 -> continue resolving
- Enter scope #3 -> resolve
- Enter scope #1 -> continue resolving
- Enter scope #0 -> continue resolving
- End

The "path" could be stored alongside my `ScopeStack` struct to allow switching between scopes for `realm`s

The entire switching of scopes could be elegantly handled by a higher-order function in a fashion like:
```rs
fn path_forward(&mut self, work: F) -> R
where
    F: FnOnce(&mut Self) -> R
{
    self.path_idx += 1;
    let ret = work(self);
    self.path_idx -= 1;
    ret      
}
```
 

Example of creating a path for a function (in the Rust language due to highlighting :3)
```rs
// current scope: #0 -> no anchor <> path: [#0]
fn function() -> i32 {
    // scope #1 -> anchored to #0 <> path: [#0, #1]
    let x = 1;

    {
        // scope #2 -> anchored to #1 <> path: [#0, #1, #2]
        let c = b();
        let y = x;
        fn b() {};
    }

    // scope #1 anchored to -> #1 <> path: [#0, #1, #2, #1]
    let c = x;
    let b = 1;
    println!("{b}");
    b
}
```
    
path: [#0, #1, #2, #1, #0]

We are in scope #0
so we enter the function body and start another scope (#1).
Then, we hit a block so we create another scope (#2) with an anchor set to #1
we save that scope #2 has a definition `b` and since there is 
nothing further for us to care about, we exit that scope.


In the second phase of resolution, we take the path and set our scopes following the path
disregarding the actual flow, which will be the same

Recorded path: `[#0, #1, #2, #1, #0]`
Index starts at `0` since we start from the top scope of `#0`

```rs
fn function() -> i32 {
    // index: 1
    let x = 1;

    {
        // index: 2
        // `b` is already in scope from our earlier traversal
        // so `b` is properly resolved here!
        let c = b();

        // we are at index 2, so scope #2 which has an anchor of #1
        // so we search for `y` through scopes #2 -> #1 -> #0 (anchor of #1)
        //
        // x is in #1
        let y = x;
        fn b() {};
    }

    // index: 3
    // path[3] is #1
    // so we are again in scope #1 and can look through it's anchor (#0)
    // x is in #1
    let c = x;
    let b = 1;
    println!("{b}"); // again resolving from a "scope path" of #1 -> #0
    b

    // fin!
}
```

## Modules!

modules give us a slight problem
```rs
mod italy {
    const ROME: () = ();
    const MESSINA: () = (); 
}

fn func() -> i32 {
    italy::ROME
}
```

how do we manage to resolve the paths correctly here?

my rough idea looks like this
we maintain a path for each module
so

```rs
// let's consider the topmost module (a crate) as module 0
// and the `italy` module as module 1

// module 0: [#0]
// we register to scope #0, a module named `italy`
// and switch our realm 
mod italy {
    // module 1: [#0]
    const ROME: () = ();
    const MESSINA: () = ();
    // we register to module 1's #0 scope that `ROME` and `MESSINA` exist 
}
// we exited the module and we are back in module 0


fn func() -> i32 {
    // module 1: [#0 -> #1]
    // resolution of a path
    // so we resolve the module italy
    // then we check it's first scope for `ROME`
    italy::ROME
}
```
