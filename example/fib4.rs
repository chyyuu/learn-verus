use vstd::prelude::*;

verus! {

// 斐波那契函数的规范
spec fn fib_spec(n: nat) -> nat
    decreases n
{
    if n <= 1 {
        1
    } else {
        fib_spec(n - 2) + fib_spec(n - 1)
    }
}

// 斐波那契函数的实现
fn fib(n: u32) -> u32
    requires
        n < 30, // 限制输入以避免溢出
    ensures
        fib(n) == fib_spec(n as nat),
    decreases n
{
    if n <= 1 {
        1
    } else {
        fib(n - 2) + fib(n - 1)
    }
}

// 斐波那契函数的证明
proof fn fib_proof(n: nat)
    requires
        n < 30,
    ensures
        fib(n as u32) == fib_spec(n),
    decreases n
{
    if n > 1 {
        fib_proof(n - 1);
        fib_proof(n - 2);
    }
}

} // verus!

fn main() {
    // 测试斐波那契函数
    for i in 0..10 {
        println!("fib({}) = {}", i, fib(i));
    }
}
