# Upvar analysis

imagine a closure like
```rs
let a = 1;
let b = 2;

|arg| {
    let val = a + b;
    arg + b + a + val;
}
```

first we must analyse it to know which
referenced variables are infact upvars


i think maintaining a set of local declarations
**inside** of the closure as a first step would be good

```rs
struct LocalCollector {
    set: HashMap<HirId>,
}
```

then, for every `let` statement and pattern
we can push the `HirId` into the set


now, we are left with determining the upvars
which could be done by traversing every use
of some variable and if it isn't in the set
we insert it into some `Vec` of captured upvars

```rs
struct UpvarCollector {
    set: HashSet<HirId>,
    upvars: Vec<HirId>,
}
```

the pseudocode could roughly be:
```rs
// assume this is inside a function
// where `self` is for `UpvarCollector`
for expr in (expressions of the closure body) {
    if let ExprKind::Path(res, ..) = expr.kind {
        if let Resolved::Local(local_hir_id) = res
          && !self.set.contains(local_hir_d)
        {
            self.upvars.push(local_hir_id)
        }
    }
}
```

# Lowering lambdas into something??

fuck!

i think it would make sense to include them
during the transition between the HIR and the EAIR (tbd)
so later stages don't have to bother with that and just get
raw functions and instances.

so the idea is that the builder for the EAIR would first check if the
given `DefId` points to a lambda and if it does it inserts the first
parameter needed (the environment)

the body generation proceeds and we can lower variable uses by using
our constructed `Vec` of `HirId`s

so
```rs
// pseudocode
if self.upvars.contains(id_of_current_processed_var) {
    return ExprKind::Upvar(...)
} else {
    return ExprKind::Local(...)
}
```

this would expose the upvars in the EAIR directly
which woulds be nice


we can later resolve them by the PILL builder context
containing a map of upvars which would map our captured Upvar's id
to some created altar that would point to the place except inside the lambda environment


so like we could transform the list of `HirId`s into a tuple of `(LocalId, Ty)`
and that would let us create places inside a closure body being built which would replace the previous upvars with field projections into the environment.

## Lowering lambda expressions

those would just become struct constructors with the fields
being filled out with upvars

## Lowering lambda bodies

explained earlier, the obtained list of upvars would be used to create locals
that lated would be referenced by `ExprKind::Upvar` and looked up.

# Somehow inserting calls into kinda generic functions

serve functions as zero-sized types
closures as their structs
to a singular unified Call stmt


so i have a type like `fun(i32) => i32`
and i think the idea to implement this is
that i would generate generic IR for every function etc.
and upon hitting a callsite i would prompt for generating a specialized version of it

like imagine
```rs
fun m<T>(v: T, x: fun(T) => T) => T {
    x(T)
}
```

in a call
```rs
_1: i32 = Call(/* func ref */, [i32, fun(i32) => T]);
```

such a call terminator would trigger a monomorphization of the function
to the required types (pseudo ir)

```rs
fun _m_func_mono_1(v: i32, x: fun(i32) => i32) => i32 {
    _1: i32 = Call(x, [v]);
    _0 = _1
    return
}
```


