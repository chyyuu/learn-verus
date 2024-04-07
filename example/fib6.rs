use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> (f: nat)
    decreases n,
{
    if n == 0 { 0 } else if n == 1 { 1 }
    else {
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
    if x < 2 && y < 2 {
    } else if x == y {
    } else if x == y - 1 {
        reveal_with_fuel(fib, 2);
        fib_mono(x, (y - 1) as nat);
    } else {
        fib_mono(x, (y - 1) as nat);
        fib_mono(x, (y - 2) as nat);
    }
}

spec fn fib_fits_u32(n: nat) -> bool {
    fib(n) <= 0xffff_ffff
}

fn calc_fib(n: u32) -> (f: u32)
    requires
        //n<=20,
        fib_fits_u32(n as nat),
    ensures
        f == fib(n as nat),
{
    if n == 0 {
        return 0;
    }

    let mut a = 0;
    let mut b = 1;
    let mut index = 1;
    assert(fib_fits_u32(n as nat)) by { reveal_with_fuel(fib, 11) };
    while index < n
        invariant
            a == fib((index-1) as nat),
            b == fib(index as nat),
            0< index <= n,
            fib_fits_u32(n as nat),
            fib_fits_u32(index as nat),
    {

        index += 1;
        assert((a + b) as nat <= u32::MAX) by {
            fib_mono(index as nat, n as nat);
        }
        let t = a + b;
        a = b;
        b = t;

    }
    b
}
// fn test() {
//     for i in 0..20 {
//         calc_fib(i);
//     }
// }
} // verus!

fn main() {
    for i in 0..20 {
        println!("{i}: {}", calc_fib(i));
    }
}