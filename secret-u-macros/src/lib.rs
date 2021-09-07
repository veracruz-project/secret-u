
extern crate proc_macro;

use proc_macro::TokenStream;

mod tables;
mod compile;
mod internal;


/// Provides compile-time bitslicing of lookup tables
///
/// Unfortunately it becomes very difficult to ensure constant-time
/// when secret-dependent memory accesses become involved. Instead
/// we can use a technique called bitslicing, where we transform
/// a lookup table into a per-bit boolean logic.
///
/// This is more expensive than a lookup table, but can be improved
/// by operating on multiple inputs in parallel, operating on multiple
/// bits with each step in the boolean logic.
///
/// This macro converts a lookup table to boolean logic form,
/// runs Quine-McCluskey minimization (thanks to the
/// quine-mc_cluskey crate), and creates a function that operates on
/// secret-types
///
/// Usage:
/// ```
/// #[bitslice_table]
/// const table: [u8; 256] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in: SecretU8) -> SecretU8;
/// ```
/// 
/// With args:
/// ```
/// #[bitslice_table(parallel=4)]
/// const table: [u16; 6] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in: SecretU16x4) -> (SecretU16x4)
/// ```
///
#[proc_macro_attribute]
pub fn bitslice_table(args: TokenStream, input: TokenStream) -> TokenStream {
    tables::bitslice_table(args, input)
}


/// Provides compile-time shuffle-based lookup tables
///
/// This is a faster-to-compile, slower-to-execute (in theory?)
/// constant-time lookup table implementation. It can be dropped in
/// as an alternative to bitslice_table for better compile times.
///
/// It is effectively a brute-force hardcoded search for each value,
/// but using SIMD shuffle instructions to reduce the bottom half of
/// the tree. The current, simulated instruction set, allows up
/// to 128 byte lookup (2 u8x64s per shuffle). More realistically, in
/// Arm NEON, the tbl instruction allows 32 byte lookup (2 u8x16s) in
/// a constant number of cycles.
///
/// Performing a 256 byte lookup with 128 byte shuffles:
/// - 2 shuffles
/// - 1 select
///
/// Performing a 256 byte lookup with 32 byte shuffles:
/// - 8 shuffles
/// - 7 selects
///
/// Note that just like bitsliced tables, shuffle tables benefit from
/// parallelism since the shuffle instruction operates on multiple lanes
/// at a time.
///
/// Usage:
/// ```
/// #[shuffle_table]
/// const table: [u8; 256] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in: SecretU8) -> SecretU8;
/// ```
/// 
/// With args:
/// ```
/// #[shuffle_table(parallel=4)]
/// const table: [u16; 6] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in: SecretU16x4) -> (SecretU16x4)
/// ```
///
#[proc_macro_attribute]
pub fn shuffle_table(args: TokenStream, input: TokenStream) -> TokenStream {
    tables::shuffle_table(args, input)
}


/// A convenience wrapper for lazily compiling parameterized secret
/// expressions
///
/// See secret_u::lambda::compile for more information
///
/// Note! This does not compile that secret-u bytecode at compile-time,
/// it only provides a lazily compiled wrapper using thread_local for
/// convenience when declaring global secret functions
///
#[proc_macro_attribute]
pub fn lazy_compile(args: TokenStream, input: TokenStream) -> TokenStream {
    compile::lazy_compile(args, input)
}


/// A heavy-weight macro to generate variable number of secret-u items
///
/// Internal macro-like variables:
/// __secret_t - SecretU/I/Ux/Ix/Mx type
/// __secret_u - SecretU type with same width
/// __secret_i - SecretI type with same width
/// __secret_ux - unsigned secret type
/// __secret_ix - signed secret type
/// __secret_mx - masked secret type
/// __U - internal Ux type with same width
/// __lane_U - internal Ux type with lane width
/// __t - String containing either "u", "i", "ux", "ix", or "mx"
/// __npw2 - npw2(size) of the type
/// __lnpw2 - npw2(lanes) of the type
/// __lane_npw2 - npw(lane_size) of the type
/// __size - size in bytes of the type
/// __lane_size - size of each lane in bytes
/// __lanes - number of lanes
/// __has_lanes - wether or not the type has lanes
/// __lane_t - secret lane type
/// __lane_u - unsigned secret lane type
/// __lane_i - signed secret lane type
/// __has_prim - if it has a primitive type
/// __prim_t - primitive type, if it has one
/// __prim_u - unsigned primitive type, if it has one
/// __prim_i - signed primitive type, if it has one
///
/// Inside __for_lanes:
/// __a - arbitrary ident that can be used for arg names
/// __i - current lane number
///
#[proc_macro]
pub fn for_secret_t(input: TokenStream) -> TokenStream {
    internal::for_secret_t(input)
}

/// A heavy-weight macro to generate variable number of secret-u items
///
/// Two one generates all of the same macro-like variables, but in a nested
/// loop, giving you 2x secret types!
///
#[proc_macro]
pub fn for_secret_t_2(input: TokenStream) -> TokenStream {
    internal::for_secret_t_2(input)
}

/// Quick macro to get the engine's underlying limb type
#[proc_macro]
pub fn engine_limb_t(input: TokenStream) -> TokenStream {
    internal::engine_limb_t(input)
}

/// Quick macro to get the engine's underlying signed limb type
#[proc_macro]
pub fn engine_limbi_t(input: TokenStream) -> TokenStream {
    internal::engine_limbi_t(input)
}

/// Quick macro to get the engine's underlying wide limb type (used for mul)
#[proc_macro]
pub fn engine_limb2_t(input: TokenStream) -> TokenStream {
    internal::engine_limb2_t(input)
}

/// Internally used engine macro for generating short (non-limb) types
///
/// See engine.rs for more info.
///
#[proc_macro]
pub fn engine_for_short_t(input: TokenStream) -> TokenStream {
    internal::engine_for_short_t(input)
}

/// Internally used engine macro for generating match statements
///
/// Note, this is very unhygenic. See engine.rs for more info.
///
#[proc_macro]
pub fn engine_match(input: TokenStream) -> TokenStream {
    internal::engine_match(input)
}
