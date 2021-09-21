//! internal.rs depends on some environment variables to decide the limits
//! of type sizes, this build.rs just ensures the dependent crates will
//! recompile if these limits are changed

use std::env;
use std::cmp::min;


// Defaults if SECRET_U_MAX_NPW2/LNPW2 undefined, this is the limit of our
// internal encoding (4-bits)
const DEFAULT_MAX_NPW2: u8 = 15;  // 2^15 bytes = u262144
const DEFAULT_MAX_LNPW2: u8 = 15; // 2^15 lanes = 32768 lanes

// Defaults of engine's limb size, note the engine has some expectations of
// being able to fit u16/u32s into limbs, and needs a 2 x wide limb for
// multiplication, so I'm not sure what will happen if SECRET_U_LIMB_NPW2
// is < 2 or > 3
const DEFAULT_LIMB_NPW2: u8 = 3;  // 2^3 bytes = u64


fn npw2_env(name: &str, limit: u8) -> Option<u8> {
    match env::var(name) {
        Ok(x) => match x.parse::<u8>().ok().filter(|x| *x <= limit) {
            Some(x) => Some(x),
            None => panic!("Bad value for {}: {}", name, x),
        },
        Err(env::VarError::NotPresent) => None,
        Err(err) => panic!("Bad value for {}: {}", name, err),
    }
}

fn main() {
    println!("cargo:rerun-if-changed=src/");
    println!("cargo:rerun-if-env-changed=SECRET_U_MAX_NPW2");
    println!("cargo:rerun-if-env-changed=SECRET_U_MAX_LNPW2");
    println!("cargo:rerun-if-env-changed=SECRET_U_LIMB_NPW2");

    // allow explicit configuration through environment variables
    let mut max_npw2  = npw2_env("SECRET_U_MAX_NPW2", DEFAULT_MAX_NPW2);
    let mut max_lnpw2 = npw2_env("SECRET_U_MAX_LNPW2", DEFAULT_MAX_LNPW2);
    let limb_npw2 = npw2_env("SECRET_U_LIMB_NPW2", DEFAULT_MAX_NPW2);

    // find best npw2/lnpw2 based on feature flags
    if max_npw2.is_none() {
        for npw2 in (0..=DEFAULT_MAX_NPW2).rev() {
            if env::var(format!("CARGO_FEATURE_U{}", 8 << npw2)).is_ok() {
                max_npw2 = Some(npw2);
                break;
            }
        }
    }

    if max_lnpw2.is_none() {
        for lnpw2 in (0..=DEFAULT_MAX_LNPW2).rev() {
            if env::var(format!("CARGO_FEATURE_X{}", 1 << lnpw2)).is_ok() {
                max_lnpw2 = Some(lnpw2);
                break;
            }
        }
    }

    // default to defaults, note that a npw2/lnpw2 more conservative default
    // should always be set by secret-u's root crate
    let max_npw2 = max_npw2.unwrap_or(DEFAULT_MAX_NPW2);
    let max_lnpw2 = min(max_lnpw2.unwrap_or(DEFAULT_MAX_LNPW2), max_npw2);
    let limb_npw2 = limb_npw2.unwrap_or(DEFAULT_LIMB_NPW2);

    // make sure env variables are always defined
    println!("cargo:rustc-env=SECRET_U_MAX_NPW2={}", max_npw2);
    println!("cargo:rustc-env=SECRET_U_MAX_LNPW2={}", max_lnpw2);
    println!("cargo:rustc-env=SECRET_U_LIMB_NPW2={}", limb_npw2);
}
