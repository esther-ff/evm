instance Simple (
    field: nil
)

instance Vector (
    x: f32,
    y: f32
)

bind Vector with (
    fun mul(self, m: f32) => nil {
        self.x *= m;
        self.y *= m;
    }
)

realm meow {
    pub fun i() => nil {}    
}

bind [i32] with (
    fun push(self, m: i32) => [i32] {
        push_list(self, m)
    }
)

fun inst() => Simple {
    Simple({})
}

fun hof(f: fun(i32) => i32) => i32 {
    f(1)
}

native {
    fun print(l: [u8]) => i32
    fun push_list(l: [i32], item: i32) => i32
}

fun main(param: i32) => nil {
    meow::i();
    # let adt = inst()
    # adt.field;

    # let vector: Vector;

    # let num: i32 = if true || 1 == 1 {
    #     1 + 1
    # } else {
    #     2 + 2
    # };

    # let var: i32 = 1;
    # [var].push(var);

    # Vector::mul(vector, 2.5);

    # print([]);

    # vector.mul(2.5);
    # let a = \b => num + b;
    # (\x => x + x)(1);
    # a(1);

    # hof(\x => x);

    # while true {
    #     1;
    # };
    # let f = 1;
    # let h = 2;
    # let j = 3;
    # (\x: i32 => f + h + j + x)(1);
    
    # vector.x;
    # adt.field
    let mut a = 1;
    let mut b = 1;
    let mut c = 1;

    first: loop {
        a += 1;
        second: loop {
            b += 2;
            third: loop {
                c += 3;
                break
            }
        }
    }
}


# fun test_ifs(test: bool) => i64 {
#   let null: nil = if 0 == 0 {
#       0;
#   };

#   let num: i64 = if test {
#       1
#   } else if 1 == 1{
#       2
#   } else if 1 == 1 {
#       3
#   } else {
#       1
#   };

#   num
# }

fun a() => nil {
    let a = 1;
    (\x => x + x)(1);
    a + 1;
}

