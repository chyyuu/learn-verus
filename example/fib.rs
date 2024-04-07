use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> (f: nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        fib((n - 2) as nat) + fib((n - 1) as nat)
    }
}

proof fn fib_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        fib(x) <= fib(y),
    decreases y,
{
    if x < y {
        reveal_with_fuel(fib, 2);
        fib_mono(x, (y - 1) as nat);
    }
}

fn calc_fib(n: u32) -> (f: u32)
    requires
        n <= 20,
    ensures
        f == fib(n as nat),
{
    if n <= 1 {
        return 1;
    }
    let mut a = 1;
    let mut b = 1;
    let mut index = 0;
    assert(fib(n as nat) <= u32::MAX) by { reveal_with_fuel(fib, 11) };
    while index < n - 1
        invariant
            a == fib(index as nat),
            b == fib((index + 1) as nat),
            index <= n - 1,
            fib(n as nat) <= u32::MAX,
    {
        assert((a + b) as nat <= u32::MAX) by {
            fib_mono((index + 2) as nat, n as nat);
        }
        let t = a + b;
        a = b;
        b = t;
        index += 1;
    }
    b
}

fn test() {
    for i in 0..20 {
        calc_fib(i);
    }
}

} // verus!

fn main() {
    for i in 0..20 {
        println!("{i}: {}", calc_fib(i));
    }
}