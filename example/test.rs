use builtin_macros::*;
use builtin::*;

verus! {

pub fn foo(a: u64) -> u64
    requires a < 100
{
    a + 1
}

fn main() {
    let c = 1;
    let mut b : u64 = 3;
    b = 4;
    b = foo(c);
    //println!("{}", b);
}

} // verus!