//! Simple README example, tests for Heronian-Pythagorean triples

use secret_u::*;

#[lazy_compile]
fn is_hptriple(a: SecretU32, b: SecretU32, c: SecretU32) -> SecretBool {
    // is Pythagorean triple?
    (a.clone()*a.clone() + b.clone()*b.clone()).eq(c.clone()*c.clone())
        .select(
            // is Heronian triple?
            ((a + b) & SecretU32::const_(1)).eq(SecretU32::const_(1)),
            SecretBool::false_()
        )
}

// entry point
fn main() {
    let res = is_hptriple(
        &SecretU32::new(3),
        &SecretU32::new(4),
        &SecretU32::new(5)
    ).declassify();

    println!("is_hptriple(3, 4, 5) => {}", res);
    assert_eq!(res, true);
}
