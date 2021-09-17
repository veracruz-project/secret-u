//! Engine linkage

use secret_u_opcode::Error;

// engine::exec declared here as an external symbol to allow parallel builds
// between these two crates. At least on my machine these both take
// ~20 minutes to compile with --release independently, so this is quite a
// valuable time savings
//
pub fn exec<'a>(
    bytecode: &[u64],
    state: &'a mut [u8]
) -> Result<&'a [u8], Error> {
    extern "Rust" {
        #[link_name="secret_u_engine_exec"]
        fn exec<'a>(
            bytecode: &[u64],
            state: &'a mut [u8]
        ) -> Result<&'a [u8], Error>;
    }

    unsafe {
        exec(bytecode, state)
    }
}
