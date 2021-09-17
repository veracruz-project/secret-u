//! internal.rs depends on some environment variables to decide the limits
//! of type sizes, this build.rs just ensures the dependent crates will
//! recompile if these limits are changed

fn main() {
    println!("cargo:rerun-if-changed=src/");
    println!("cargo:rerun-if-env-changed=SECRET_U_MAX_NPW2");
    println!("cargo:rerun-if-env-changed=SECRET_U_MAX_LNPW2");
}
