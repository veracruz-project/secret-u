//! Shamir's secret sharing example
//!
//! Using carry-less multiplication (xmul) with Barret reduction as a
//! constant-time alternative to lookup tables.
//!
//! Based on the explanation here:
//! https://blog.quarkslab.com/reversing-a-finite-field-multiplication-optimization.html
//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

use secret_u::*;
use std::iter;
use std::convert::TryFrom;

// Constants for Barret reduction
const GF256_P: u16 = 0x11b;
const GF256_P_INV: u16 = 0x11a; // xdiv(0x10000, p)

/// multiply in GF(256) using Barret reduction
fn gf256_mul(a: SecretP8x32, b: SecretP8x32) -> SecretP8x32 {
    let x = SecretP16x32::from(a) * SecretP16x32::from(b);
    let q = (x.clone() >> SecretU16x32::const_splat(8)) * SecretP16x32::const_splat(GF256_P_INV);
    SecretP8x32::from_cast((q >> SecretU16x32::const_splat(8))*SecretP16x32::const_splat(GF256_P) + x)
}

/// divide in GF(256) by multiplying against b's inverse
///
/// a/b = a*b^-1 = a*b^254
///
fn gf256_div(a: SecretP8x32, b: SecretP8x32) -> SecretP8x32 {
    let b2   = gf256_mul(b.clone(),    b.clone());
    let b3   = gf256_mul(b2.clone(),   b.clone());
    let b6   = gf256_mul(b3.clone(),   b3.clone());
    let b12  = gf256_mul(b6.clone(),   b6.clone());
    let b15  = gf256_mul(b12.clone(),  b3.clone());
    let b24  = gf256_mul(b12.clone(),  b12.clone());
    let b48  = gf256_mul(b24.clone(),  b24.clone());
    let b63  = gf256_mul(b48.clone(),  b15.clone());
    let b126 = gf256_mul(b63.clone(),  b63.clone());
    let b127 = gf256_mul(b126.clone(), b.clone());
    let b254 = gf256_mul(b127.clone(), b127.clone());

    gf256_mul(a, b254)
}

/// find f(0) using Lagrange interpolation
fn gf256_interpolate(xs: &[SecretP8], ys: &[SecretP8x32]) -> SecretP8x32 {
    assert!(xs.len() == ys.len());

    // lazily compiled functions
    #[lazy_compile]
    fn gf256_interpolate_step(li: SecretP8x32, x0: SecretP8, x1: SecretP8) -> SecretP8x32 {
        gf256_mul(li, gf256_div(SecretP8x32::splat(x1.clone()), SecretP8x32::splat(x0 + x1)))
    }

    #[lazy_compile]
    fn gf256_interpolate_sum(y: SecretP8x32, li: SecretP8x32, y0: SecretP8x32) -> SecretP8x32 {
        y + gf256_mul(li, y0)
    }

    let mut y = SecretP8x32::zero();
    for (i, (x0, y0)) in xs.iter().zip(ys).enumerate() {
        let mut li = SecretP8x32::one();
        for (j, (x1, _y1)) in xs.iter().zip(ys).enumerate() {
            if i != j {
                li = gf256_interpolate_step(li.clone(), x0.clone(), x1.clone());
            }
        }

        y = gf256_interpolate_sum(y, li, y0.clone());
    }

    y
}

/// reconstruct our secret
fn shares_reconstruct<S: AsRef<[SecretU8]>>(shares: &[S]) -> Vec<SecretU8> {
    let len = shares.iter().map(|s| s.as_ref().len()).min().unwrap_or(0);
    // rather than erroring, return empty secrets if input is malformed.
    // This matches the behavior of bad shares (random output) and simplifies
    // consumers.
    if len == 0 {
        return vec![];
    }

    let mut secret = vec![];

    // x is prepended to each share
    let xs: Vec<SecretP8> = shares.iter()
        .map(|v| SecretP8::from_cast(v.as_ref()[0].clone()))
        .collect();
    for i in (1..len).step_by(32) {
        // pad to 32 bytes if necessary
        let ys: Vec<SecretP8x32> = shares.iter()
            .map(|v| {
                let slice = &v.as_ref()[i..];
                SecretP8x32::try_from(
                    slice.iter()
                        .map(|v| SecretP8::from_cast(v.clone()))
                        .chain(iter::repeat(SecretP8::zero()))
                        .take(32)
                        .collect::<Vec<_>>()
                ).ok().unwrap()
            })
            .collect();
        secret.append(
            &mut gf256_interpolate(&xs, &ys).into_iter().collect()
        );
    }

    secret.truncate(len-1);
    secret.into_iter().map(|v| SecretU8::from_cast(v)).collect()
}

// entry point
fn main() {
    let shares = [
        b"\x01\xdc\x06\x1a\x7b\xda\xf7\x76\x16\xdd\x59\x15\xf3",
        b"\x02\x7f\x38\xe2\x7b\x5a\x02\xa2\x88\xd0\x64\x96\x53",
        b"\x03\xeb\x5b\x94\x6c\xef\xd5\x83\xf1\x7f\x51\xe7\x81",
    ];

    // convert to secret
    let shares = shares.iter()
        .map(|share| {
            share.iter()
                .map(|x| SecretU8::new(*x))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    // reconstruct secret
    let secret = shares_reconstruct(&shares);

    // declassify
    let secret = secret.into_iter()
        .map(|x| x.declassify())
        .collect::<Vec<_>>();

    let message = String::from_utf8_lossy(&secret);
    println!("{}", message);
    assert_eq!(message, "Hello World!");
}
