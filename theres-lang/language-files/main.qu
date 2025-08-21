instance MyInstance (
    const field: type,
    fieldA: type,
)

bind MyInstance with (
    const InstanceConst: type = 2;
    
    fun method(self, arg1: type) => type {
        
    };
)

interface A {
    const Constant: type = 1
    
    fun methodSig(self, argument: sometype) => type

    fun methodSigAlt(self) => type

    fun providedMethod(self, arg1: type, arg2: type) => type {
        1 + 1;
    }

    fun methodNoSelf() => type
}

apply A for MyInstance {
    const Constant: type = 1

    fun methodSig(self, argument: sometype) => type {
        # panic somehow?
    }

    fun methodSigAlt(self) => type {
        # panic somehow?
    }

    fun methodNoSelf() => type {
        1;
    }
}

fun main(arg2: type, arg1: type) => type {
    fun innerFn() => type {};
    
    if true {
        cond();
    } else {
        condA();
    }.into().into.b.anothercall() + 1;

    let array: [u64] = [12]u64;

    let lambda: fun(u64) => u64 = \x => x + 1;

    let expr: u64 = (1 + 1) / 2 << 2;

    let muerte: u64 = if condition {
        gimmeNum();
    } else {
        no();
    }.someMethod(\x => x + 1);

    let arrayInit: [u64] = [12]u64 { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 };

    return;
    return 1;
}
