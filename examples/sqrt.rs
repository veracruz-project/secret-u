//! Simple README example, tests for Heronian-Pythagorean triples
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

use secret_u::*;

#[lazy_compile]
fn sqrt(x: SecretU32) -> SecretU32 {
    // binary search
    let mut lo = SecretU32::const_(0);
    let mut hi = x.clone();

    // each round determines one bit, so only need log(x) rounds
    for _ in 0..8 {
        // test mid
        let mid = (lo.clone() + hi.clone()) >> SecretU32::const_(1);
        let mid_sq = mid.clone()*mid.clone();

        // find new lo/hi using select to preserve const-time
        let mid_sq_lt = mid_sq.lt(x.clone());
        lo = mid_sq_lt.clone().select(mid.clone(), lo.clone());
        hi = mid_sq_lt.clone().select(hi.clone(), mid.clone());
    }

    // lo and hi should converge
    hi
}

// entry point
fn main() {
    let res = sqrt(SecretU32::new(16)).declassify();

    println!("sqrt(16) => {}", 4);
    assert_eq!(res, 4);
}
