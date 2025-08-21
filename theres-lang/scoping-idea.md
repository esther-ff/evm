scope #0
```rs
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
so we'd build a path like that to basically traverse the scopes later for resolving stuff like local variables
This would allow me to first record the existence of items (like fns)
How would the path work?
I think something like
#0 -> #1 -> #2 -> #1 -> #3 -> #0
Enter scope 0 -> resolve -> enter scope 1 -> resolve from it's anchor (#0)
then, enter scope #2 and resolve from it's anchor (#1 -> #0), after that
go to scope #1 again and enter scope #3 and resolve from it's anchor (#1 -> #0)
then exit that scope, resolve further the rest of the scope and exit.
The "exiting" for a scope like from #3 to #1 would basically be a closure callback
because of how we traverse the AST
This can be adapted to scope stacks so i can switch out a scope stack for realm
The anchors provide a pathway of resolution, basically
if im in scope #3 which has anchor #1, i have the access to all items in #1 and it's anchors recursively, so i have access to #1 and #0

How to create such a path though?
For this function we could work it out like this!

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
so we enter the function body and start another scope of #1
Then, we hit a block so we create a scope (#2) with an anchor of #1
we save that scope #2 has a definition `b` and exit
nothing further for us to care about so we exit.
In the second phase of resolution, we take the path and set our scopes following the path
disregarding the actual flow, which should be the same

path: [#0, #1, #2, #1, #0]
Start of the path at scope #0, so index: 0

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
