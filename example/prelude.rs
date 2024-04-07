#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    proof fn lemma() {
        let a: Seq<nat> = seq![1, 2, 3];
        assert(a[1] == 2);
    }

    fn main() {
        proof{
            let a: Seq<nat> = seq![1, 2, 1, 3];
            assert(a[1] == 2);
            assert(a[0] == 1);
        }
    }
}
