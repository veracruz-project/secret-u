//!
//! Copyright (c) 2021 Veracruz, a series of LF Projects, LLC.
//! SPDX-License-Identifier: MIT

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::parse_macro_input;
use syn::spanned::Spanned;
use syn::parse_quote;
use quote::quote;
use darling::FromMeta;
use std::iter;
use std::cmp::*;
use std::env;

use boolean_expression as be;

use crate::internal::MAX_NPW2;


fn crate_() -> proc_macro2::TokenStream {
    if env::var("CARGO_CRATE_NAME").unwrap() == "secret_u" {
        quote! { crate }
    } else {
        quote! { ::secret_u }
    }
}


// use the boolean_expression crate for bitexpr simplification

fn find_bitexpr(table: &[u128], width: usize, bit: usize) -> be::Expr<u8> {
    // build naive expr
    let mut ors = be::Expr::Const(false);
    for i in 0..table.len() {
        if table[i] & (1 << bit) == (1 << bit) {
            let mut ands = be::Expr::Const(true);
            for j in 0..width {
                if i & (1 << j) == (1 << j) {
                    ands &= be::Expr::Terminal(j as u8);
                } else {
                    ands &= be::Expr::not(be::Expr::Terminal(j as u8))
                }
            }
            ors |= ands;
        }
    }

    ors
}

fn simplify_bitexpr(expr: be::Expr<u8>) -> be::Expr<u8> {
    #[cfg(feature="bitslice-simplify-bdd")]
    let simplified = expr.simplify_via_bdd();
    #[cfg(all(feature="bitslice-simplify-identities", not(feature="bitslice-simplify-bdd")))]
    let simplified = expr.simplify_via_laws();
    #[cfg(all(not(feature="bitslice-simplify-identities"), not(feature="bitslice-simplify-bdd")))]
    let simplified = expr;

    simplified
}


macro_rules! ident {
    ($($fmt:tt)+) => {
        syn::Ident::new(&format!($($fmt)+), Span::call_site())
    }
}

macro_rules! lit {
    ($x:expr) => {
        syn::LitInt::new(&format!("{}", $x), Span::call_site())
    }
}

macro_rules! bail {
    (_, $($fmt:tt)+) => {
        return TokenStream::from(
            syn::Error::new(
                Span::call_site(),
                format!($($fmt)+)
            ).to_compile_error()
        )
    };
    ($s:expr, $($fmt:tt)+) => {
        return TokenStream::from(
            syn::Error::new(
                $s.span(),
                format!($($fmt)+)
            ).to_compile_error()
        )
    };
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Prim {
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    U256,
    U512,
    U1024,
    U2048,
    U4096,
    U8192,
    U16384,
    U32768,
    U65536,
    U131072,
    U262144,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    I512,
    I1024,
    I2048,
    I4096,
    I8192,
    I16384,
    I32768,
    I65536,
    I131072,
    I262144,
}

impl Prim {
    fn from_ident(ident: &str) -> Option<Prim> {
        match ident {
            "bool"    => Some(Prim::Bool),
            "u8"      => Some(Prim::U8),
            "u16"     => Some(Prim::U16),
            "u32"     => Some(Prim::U32),
            "u64"     => Some(Prim::U64),
            "u128"    => Some(Prim::U128),
            "u256"    => Some(Prim::U256),
            "u512"    => Some(Prim::U512),
            "u1024"   => Some(Prim::U1024),
            "u2048"   => Some(Prim::U2048),
            "u4096"   => Some(Prim::U4096),
            "u8192"   => Some(Prim::U8192),
            "u16384"  => Some(Prim::U16384),
            "u32768"  => Some(Prim::U32768),
            "u65536"  => Some(Prim::U65536),
            "u131072" => Some(Prim::U131072),
            "u262144" => Some(Prim::U262144),
            "i8"      => Some(Prim::I8),
            "i16"     => Some(Prim::I16),
            "i32"     => Some(Prim::I32),
            "i64"     => Some(Prim::I64),
            "i128"    => Some(Prim::I128),
            "i256"    => Some(Prim::I256),
            "i512"    => Some(Prim::I512),
            "i1024"   => Some(Prim::I1024),
            "i2048"   => Some(Prim::I2048),
            "i4096"   => Some(Prim::I4096),
            "i8192"   => Some(Prim::I8192),
            "i16384"  => Some(Prim::I16384),
            "i32768"  => Some(Prim::I32768),
            "i65536"  => Some(Prim::I65536),
            "i131072" => Some(Prim::I131072),
            "i262144" => Some(Prim::I262144),
            _      => None,
        }
    }

    fn from_len(len: usize) -> Prim {
        match len {
            0 => Prim::U8,
            len if len-1 <= u8::MAX as usize   => Prim::U8,
            len if len-1 <= u16::MAX as usize  => Prim::U16,
            len if len-1 <= u32::MAX as usize  => Prim::U32,
            len if len-1 <= u64::MAX as usize  => Prim::U64,
            len if len-1 <= u128::MAX as usize => Prim::U128,
            _ => panic!("len > u128?"),
        }
    }

    fn from_width(width: usize) -> Prim {
        match width {
            width if width <= 8      => Prim::U8,
            width if width <= 16     => Prim::U16,
            width if width <= 32     => Prim::U32,
            width if width <= 64     => Prim::U64,
            width if width <= 128    => Prim::U128,
            width if width <= 256    => Prim::U256,
            width if width <= 512    => Prim::U512,
            width if width <= 1024   => Prim::U1024,
            width if width <= 2048   => Prim::U2048,
            width if width <= 4096   => Prim::U4096,
            width if width <= 8192   => Prim::U8192,
            width if width <= 16384  => Prim::U16384,
            width if width <= 32768  => Prim::U32768,
            width if width <= 65536  => Prim::U65536,
            width if width <= 131072 => Prim::U131072,
            width if width <= 262144 => Prim::U262144,
            _ => panic!("width > u512?"),
        }
    }

    fn width(&self) -> usize {
        match self {
            Prim::Bool    => 1,
            Prim::U8      => 8,
            Prim::U16     => 16,
            Prim::U32     => 32,
            Prim::U64     => 64,
            Prim::U128    => 128,
            Prim::U256    => 256,
            Prim::U512    => 512,
            Prim::U1024   => 1024,
            Prim::U2048   => 2048,
            Prim::U4096   => 4096,
            Prim::U8192   => 8192,
            Prim::U16384  => 16384,
            Prim::U32768  => 32768,
            Prim::U65536  => 65536,
            Prim::U131072 => 131072,
            Prim::U262144 => 262144,
            Prim::I8      => 8,
            Prim::I16     => 16,
            Prim::I32     => 32,
            Prim::I64     => 64,
            Prim::I128    => 128,
            Prim::I256    => 256,
            Prim::I512    => 512,
            Prim::I1024   => 1024,
            Prim::I2048   => 2048,
            Prim::I4096   => 4096,
            Prim::I8192   => 8192,
            Prim::I16384  => 16384,
            Prim::I32768  => 32768,
            Prim::I65536  => 65536,
            Prim::I131072 => 131072,
            Prim::I262144 => 262144,
        }
    }

    fn prim_ty(&self) -> syn::Type {
        let ident = match self {
            Prim::Bool => ident!("bool"),
            Prim::U8   => ident!("u8"),
            Prim::U16  => ident!("u16"),
            Prim::U32  => ident!("u32"),
            Prim::U64  => ident!("u64"),
            Prim::U128 => ident!("u128"),
            Prim::I8   => ident!("i8"),
            Prim::I16  => ident!("i16"),
            Prim::I32  => ident!("i32"),
            Prim::I64  => ident!("i64"),
            Prim::I128 => ident!("i128"),
            _ => panic!("attempting to take prim of type > u128?"),
        };

        parse_quote! {
            #ident
        }
    }

    fn secret_ty(&self) -> syn::Type {
        let ident = match self {
            Prim::Bool    => ident!("SecretBool"),
            Prim::U8      => ident!("SecretU8"),
            Prim::U16     => ident!("SecretU16"),
            Prim::U32     => ident!("SecretU32"),
            Prim::U64     => ident!("SecretU64"),
            Prim::U128    => ident!("SecretU128"),
            Prim::U256    => ident!("SecretU256"),
            Prim::U512    => ident!("SecretU512"),
            Prim::U1024   => ident!("SecretU1024"),
            Prim::U2048   => ident!("SecretU2048"),
            Prim::U4096   => ident!("SecretU4096"),
            Prim::U8192   => ident!("SecretU8192"),
            Prim::U16384  => ident!("SecretU16384"),
            Prim::U32768  => ident!("SecretU32768"),
            Prim::U65536  => ident!("SecretU65536"),
            Prim::U131072 => ident!("SecretU131072"),
            Prim::U262144 => ident!("SecretU262144"),
            Prim::I8      => ident!("SecretI8"),
            Prim::I16     => ident!("SecretI16"),
            Prim::I32     => ident!("SecretI32"),
            Prim::I64     => ident!("SecretI64"),
            Prim::I128    => ident!("SecretI128"),
            Prim::I256    => ident!("SecretI256"),
            Prim::I512    => ident!("SecretI512"),
            Prim::I1024   => ident!("SecretI1024"),
            Prim::I2048   => ident!("SecretI2048"),
            Prim::I4096   => ident!("SecretI4096"),
            Prim::I8192   => ident!("SecretI8192"),
            Prim::I16384  => ident!("SecretI16384"),
            Prim::I32768  => ident!("SecretI32768"),
            Prim::I65536  => ident!("SecretI65536"),
            Prim::I131072 => ident!("SecretI131072"),
            Prim::I262144 => ident!("SecretI262144"),
        };

        let crate_ = crate_();
        parse_quote! {
            #crate_::types::#ident
        }
    }

    fn secret_parallel_ty(&self, parallel: usize) -> syn::Type {
        if parallel == 1 {
            return self.secret_ty();
        }

        let ident = match self {
            Prim::Bool    => ident!("SecretM8x{}",      parallel),
            Prim::U8      => ident!("SecretU8x{}",      parallel),
            Prim::U16     => ident!("SecretU16x{}",     parallel),
            Prim::U32     => ident!("SecretU32x{}",     parallel),
            Prim::U64     => ident!("SecretU64x{}",     parallel),
            Prim::U128    => ident!("SecretU128x{}",    parallel),
            Prim::U256    => ident!("SecretU256x{}",    parallel),
            Prim::U512    => ident!("SecretU512x{}",    parallel),
            Prim::U1024   => ident!("SecretU1024x{}",   parallel),
            Prim::U2048   => ident!("SecretU2048x{}",   parallel),
            Prim::U4096   => ident!("SecretU4096x{}",   parallel),
            Prim::U8192   => ident!("SecretU8192x{}",   parallel),
            Prim::U16384  => ident!("SecretU16384x{}",  parallel),
            Prim::U32768  => ident!("SecretU32768x{}",  parallel),
            Prim::U65536  => ident!("SecretU65536x{}",  parallel),
            Prim::U131072 => ident!("SecretU131072x{}", parallel),
            Prim::U262144 => ident!("SecretU262144x{}", parallel),
            Prim::I8      => ident!("SecretI8x{}",      parallel),
            Prim::I16     => ident!("SecretI16x{}",     parallel),
            Prim::I32     => ident!("SecretI32x{}",     parallel),
            Prim::I64     => ident!("SecretI64x{}",     parallel),
            Prim::I128    => ident!("SecretI128x{}",    parallel),
            Prim::I256    => ident!("SecretI256x{}",    parallel),
            Prim::I512    => ident!("SecretI512x{}",    parallel),
            Prim::I1024   => ident!("SecretI1024x{}",   parallel),
            Prim::I2048   => ident!("SecretI2048x{}",   parallel),
            Prim::I4096   => ident!("SecretI4096x{}",   parallel),
            Prim::I8192   => ident!("SecretI8192x{}",   parallel),
            Prim::I16384  => ident!("SecretI16384x{}",  parallel),
            Prim::I32768  => ident!("SecretI32768x{}",  parallel),
            Prim::I65536  => ident!("SecretI65536x{}",  parallel),
            Prim::I131072 => ident!("SecretI131072x{}", parallel),
            Prim::I262144 => ident!("SecretI262144x{}", parallel),
        };

        let crate_ = crate_();
        parse_quote! {
            #crate_::types::#ident
        }
    }

    fn secret_wide_ty(&self, parallel: usize) -> syn::Type {
        Self::from_width(max(self.width(), 8) * parallel).secret_ty()
    }
}

fn build_transpose(
    a: &syn::Ident,
    prim_ty: &syn::Type,
    secret_ty: &syn::Type,
    width: usize
) -> Vec<syn::Stmt> {
    let dim = width/2;
    let mask = lit!(
        1usize.checked_shl(dim as u32)
            .map_or(usize::MAX, |mask| mask - 1)
    );

    parse_quote! {
        let mut dim = #dim;
        let mut mask = #mask;
        while dim > 0 {
            let dim_s = #secret_ty::const_(dim as #prim_ty);
            let mask_s = #secret_ty::const_(mask);

            let mut i = 0;
            while i < #width {
                let x = mask_s.clone() & ((#a[i].clone() >> dim_s.clone()) ^ #a[i+dim].clone());
                #a[i]     ^= x.clone() << dim_s.clone();
                #a[i+dim] ^= x;

                i = (i+dim+1) & !dim;
            }

            dim /= 2;
            mask ^= mask << dim;
        }
    }
}

// this has a funny type in order to keep the expression-size small and avoid
// stack overflowing rustc, an array of bitwise-ors can be collapsed with
// build_bitexpr, allowing the top-layer bitwise-ors to be flattened into a
// sequence of statements
fn build_bitexpr_ors(
    prim_ty: &syn::Type,
    secret_ty: &syn::Type,
    expr: be::Expr<u8>,
    bit: usize
) -> Vec<proc_macro2::TokenStream> {
    match expr {
        be::Expr::Const(true) => {
            vec![quote! { #secret_ty::ones() }]
        },
        be::Expr::Const(false) => {
            vec![quote! { #secret_ty::zero() }]
        },
        be::Expr::Terminal(i) => {
            let a = ident!("a{}", i);
            vec![quote! { #a.clone() }]
        },
        be::Expr::Not(v) => {
            let x = build_bitexpr(prim_ty, secret_ty, *v, bit);
            vec![quote! { (!#x) }]
        },
        be::Expr::And(v0, v1) => {
            // this is to reduce parsing pressure
            let mut pending = vec![v0, v1];
            let mut xs = Vec::new();
            while let Some(x) = pending.pop() {
                if let be::Expr::And(v0, v1) = *x {
                    if let be::Expr::Const(true) = *v0 {
                        // skip
                    } else {
                        pending.push(v0);
                    }
                    if let be::Expr::Const(true) = *v1 {
                        // skip
                    } else {
                        pending.push(v1);
                    }
                } else {
                    xs.push(build_bitexpr(prim_ty, secret_ty, *x, bit));
                }
            }

            match xs.len() {
                0 => vec![quote! { #secret_ty::ones() }],
                _ => vec![quote! { (#(#xs)&*) }],
            }
        },
        be::Expr::Or(v0, v1) => {
            // this is to reduce parsing pressure
            let mut pending = vec![v0, v1];
            let mut xs = Vec::new();
            while let Some(x) = pending.pop() {
                if let be::Expr::Or(v0, v1) = *x {
                    if let be::Expr::Const(false) = *v0 {
                        // skip
                    } else {
                        pending.push(v0);
                    }
                    if let be::Expr::Const(false) = *v1 {
                        // skip
                    } else {
                        pending.push(v1);
                    }
                } else {
                    xs.push(build_bitexpr(prim_ty, secret_ty, *x, bit));
                }
            }

            xs
        },
    }
}

fn build_bitexpr(
    prim_ty: &syn::Type,
    secret_ty: &syn::Type,
    expr: be::Expr<u8>,
    bit: usize
) -> proc_macro2::TokenStream {
    let xs = build_bitexpr_ors(prim_ty, secret_ty, expr, bit);
    match xs.len() {
        0 => quote! { #secret_ty::zero() },
        _ => quote! { (#(#xs)|*) },
    }
}


// macro arguments and things
#[derive(Debug, FromMeta)]
struct TableArgs {
    #[darling(default)]
    parallel: Option<usize>,
    #[darling(default)]
    index_type: Option<String>,
}


pub fn bitslice_table(args: TokenStream, input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro bitslice_table <= {}", args);
        println!("proc-macro bitslice_table <= {}", input);
    }

    let args = parse_macro_input!(args as syn::AttributeArgs);
    let table = parse_macro_input!(input as syn::ItemConst);

    // parse args
    let args = match TableArgs::from_list(&args) {
        Ok(args) => args,
        Err(err) => {
            return TokenStream::from(err.write_errors());
        }
    };

    let index_ty = if let Some(arg) = args.index_type {
        match Prim::from_ident(&arg) {
            Some(index_ty) => Some(index_ty),
            None => bail!(_, "index_type must be a primitive"),
        }
    } else {
        None
    };

    // parse table
    let name = table.ident;
    let vis = table.vis;

    let ret_ty;
    let size;
    match *table.ty {
        syn::Type::Array(arr) => {
            // find array type
            let ident = match &*arr.elem {
                syn::Type::Path(path) => {
                    path.path.get_ident()
                        .map(|i| i.to_string())
                },
                _ => None,
            };
            ret_ty = match ident.and_then(|s| Prim::from_ident(&s)) {
                Some(ret_ty) => ret_ty,
                None => bail!(arr.elem, "bitslice_table requires a primitive type here"),
            };

            // find array size
            let lit = match &arr.len {
                syn::Expr::Lit(lit) => Some(&lit.lit),
                _ => None,
            };
            match lit {
                Some(syn::Lit::Byte(byte)) => {
                    size = byte.value() as usize;
                }
                Some(syn::Lit::Int(int)) => {
                    size = match int.base10_parse::<usize>() {
                        Ok(size) => size,
                        Err(err) => return TokenStream::from(err.to_compile_error()),
                    };
                }
                _ => bail!(arr.len, "bitslice_table requires a literal size"),
            };
        }
        _ => bail!(table.ty, "bitslice_table requires an array"),
    }

    // now find the array elements
    let mut elems = Vec::<u128>::new();
    match *table.expr {
        syn::Expr::Array(ref arr) => {
            for elem in &arr.elems {
                let lit = match &elem {
                    syn::Expr::Lit(lit) => Some(&lit.lit),
                    _ => None,
                };
                match lit {
                    Some(syn::Lit::Bool(bool_)) => {
                        elems.push(if bool_.value { 1 } else { 0 })
                    }
                    Some(syn::Lit::Byte(byte)) => {
                        elems.push(byte.value() as u128);
                    }
                    Some(syn::Lit::Int(int)) => {
                        match int.base10_parse::<u128>() {
                            Ok(size) => elems.push(size),
                            Err(err) => return TokenStream::from(err.to_compile_error()),
                        };
                    }
                    _ => bail!(elem, "bitslice_table requires literal elements"),
                };
            }
        }
        _ => bail!(table.expr, "bitslice_table requires an array"),
    }

    // check size
    if size != elems.len() {
        bail!(table.expr, "expected array of size {}, found one of size {}", size, elems.len());
    }

    if let Some(parallel) = args.parallel {
        if !parallel.is_power_of_two() {
            bail!(_, "parallel must be a power of two");
        }
    }

    // find best types
    let parallel = args.parallel.unwrap_or(1);
    let width_ty = Prim::from_len(elems.len());
    let mid_ty = Prim::from_width(max(max(width_ty.width(), ret_ty.width()), parallel));
    let index_ty = index_ty.unwrap_or(width_ty);

    // build function
    let prim_ty = mid_ty.prim_ty();
    let secret_ty = mid_ty.secret_ty();
    let index_secret_ty = index_ty.secret_parallel_ty(parallel);
    let ret_secret_ty = ret_ty.secret_parallel_ty(parallel);
    let ret_lane_secret_ty = ret_ty.secret_ty();
    //let a_width = find_in_width(&elems, parallel);
    //let b_width = find_out_width(&elems, parallel);
    let a_width = elems.len().next_power_of_two().trailing_zeros() as usize;
    // the width needs itself to be a power of two for our transpose to work
    let a_par_width = max(a_width, parallel).next_power_of_two();
    let b_width = (elems.iter().max().copied().unwrap_or(0) + 1)
        .next_power_of_two().trailing_zeros() as usize;
    // the width needs itself to be a power of two for our transpose to work
    let b_par_width = max(b_width, parallel).next_power_of_two();

    // create variables
    // TODO can we use simds throughout?
    // TODO can we use a shuffle to do majority of transpose?
    let a_args = (0..parallel)
        .map(|i| -> syn::Expr {
            let a: syn::Expr = if parallel == 1 {
                parse_quote! { a }
            } else {
                parse_quote! { a.clone().extract(#i) }
            };
            if mid_ty.width() > index_ty.width() {
                parse_quote! { #secret_ty::from(#a) }
            } else if mid_ty.width() < index_ty.width() {
                parse_quote! { #secret_ty::from_cast(#a) }
            } else {
                parse_quote! { #a }
            }
        })
        .chain(
            iter::repeat(parse_quote! { #secret_ty::zero() })
                .take(a_par_width - parallel)
        );
    let a_unpack = (0..a_par_width)
        .map(|i| -> syn::Stmt {
            let a = ident!("a{}", i);
            parse_quote! { let #a = a[#i].clone(); }
        });
    let b_pack = (0..b_par_width)
        .map(|i| -> syn::Expr {
            let b = ident!("b{}", i);
            parse_quote! { #b }
        });
    let b_rets = (0..parallel)
        .map(|i| -> syn::Expr {
            // mask off extra bits introduced by bitwise not
            let ret: syn::Expr = if b_par_width >= ret_ty.width() {
                let i = lit!(i);
                parse_quote! { b[#i].clone() }
            } else {
                let mask = lit!((1usize << b_par_width) - 1);
                let i = lit!(i);
                parse_quote! { #secret_ty::const_(#mask) & b[#i].clone() }
            };

            if ret_ty == Prim::Bool {
                parse_quote! { (#ret & #secret_ty::one()).eq(#secret_ty::one()) }
            } else if ret_ty.width() > mid_ty.width() {
                parse_quote! { #ret_lane_secret_ty::from(#ret) }
            } else if ret_ty.width() < mid_ty.width() {
                parse_quote! { #ret_lane_secret_ty::from_cast(#ret) }
            } else {
                parse_quote! { #ret }
            }
        });
    let ret: syn::Expr = if parallel > 1 {
        parse_quote! { 
            #ret_secret_ty::from([#(#b_rets),*])
        }
    } else {
        parse_quote! { 
            #(#b_rets)*
        }
    };

    // transposes
    let a_transpose = build_transpose(&ident!("a"), &prim_ty, &secret_ty, a_par_width);
    let b_transpose = build_transpose(&ident!("b"), &prim_ty, &secret_ty, b_par_width);

    // find exprs, simplify, and convert to quote
    let mut bitexprs = Vec::new();
    for i in 0..b_par_width {
        let expr = find_bitexpr(&elems, a_width, i);
        let expr = simplify_bitexpr(expr);
        
//        if cfg!(feature = "debug-proc-macros") {
//            println!("bit({}) = {:?}", i, expr);
//        }

        let b = ident!("b{}", i);
        let exprs = build_bitexpr_ors(&prim_ty, &secret_ty, expr, i);
        if exprs.len() == 0 {
            bitexprs.push(quote! { let #b = #secret_ty::zero(); });
        } else if exprs.len() == 1 {
            let x0 = &exprs[0];
            bitexprs.push(quote! { let #b = #x0; });
        } else {
            let x0 = &exprs[0];
            bitexprs.push(quote! { let mut #b = #x0; });
            for i in 1..exprs.len() {
                let x = &exprs[i];
                bitexprs.push(quote! { #b |= #x; });
            }
        }
    }

    let crate_ = crate_();
    let q = quote! {
        #[inline(never)]
        #[allow(non_snake_case)]
        #vis fn #name(a: #index_secret_ty) -> #ret_secret_ty {
            use #crate_::traits::FromCast;
            use #crate_::traits::Eq;
            use #crate_::traits::Classify;

            let mut a: [#secret_ty; #a_par_width] = [
                #(#a_args),*
            ];

            #(#a_transpose)*

            #(#a_unpack)*

            #(#bitexprs)*

            let mut b: [#secret_ty; #b_par_width] = [
                #(#b_pack),*
            ];

            #(#b_transpose)*

            (#ret)
        }
    };

    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro bitslice_table => {}", q);
    }

    TokenStream::from(q)
}


pub fn shuffle_table(args: TokenStream, input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro shuffle_table <= {}", args);
        println!("proc-macro shuffle_table <= {}", input);
    }

    let args = parse_macro_input!(args as syn::AttributeArgs);
    let table = parse_macro_input!(input as syn::ItemConst);

    // parse args
    let args = match TableArgs::from_list(&args) {
        Ok(args) => args,
        Err(err) => {
            return TokenStream::from(err.write_errors());
        }
    };

    let index_ty = if let Some(arg) = args.index_type {
        match Prim::from_ident(&arg) {
            Some(index_ty) => Some(index_ty),
            None => bail!(_, "index_type must be a primitive"),
        }
    } else {
        None
    };

    // parse table
    let name = table.ident;
    let vis = table.vis;

    let ret_ty;
    let size;
    match *table.ty {
        syn::Type::Array(arr) => {
            // find array type
            let ident = match &*arr.elem {
                syn::Type::Path(path) => {
                    path.path.get_ident()
                        .map(|i| i.to_string())
                },
                _ => None,
            };
            ret_ty = match ident.and_then(|s| Prim::from_ident(&s)) {
                Some(ret_ty) => ret_ty,
                None => bail!(arr.elem, "shuffle_table requires a primitive type here"),
            };

            // find array size
            let lit = match &arr.len {
                syn::Expr::Lit(lit) => Some(&lit.lit),
                _ => None,
            };
            match lit {
                Some(syn::Lit::Byte(byte)) => {
                    size = byte.value() as usize;
                }
                Some(syn::Lit::Int(int)) => {
                    size = match int.base10_parse::<usize>() {
                        Ok(size) => size,
                        Err(err) => return TokenStream::from(err.to_compile_error()),
                    };
                }
                _ => bail!(arr.len, "shuffle_table requires a literal size"),
            };
        }
        _ => bail!(table.ty, "shuffle_table requires an array"),
    }

    // now find the array elements
    let mut elems = Vec::<u128>::new();
    match *table.expr {
        syn::Expr::Array(ref arr) => {
            for elem in &arr.elems {
                let lit = match &elem {
                    syn::Expr::Lit(lit) => Some(&lit.lit),
                    _ => None,
                };
                match lit {
                    Some(syn::Lit::Bool(bool_)) => {
                        elems.push(if bool_.value { 1 } else { 0 })
                    }
                    Some(syn::Lit::Byte(byte)) => {
                        elems.push(byte.value() as u128);
                    }
                    Some(syn::Lit::Int(int)) => {
                        match int.base10_parse::<u128>() {
                            Ok(size) => elems.push(size),
                            Err(err) => return TokenStream::from(err.to_compile_error()),
                        };
                    }
                    _ => bail!(elem, "shuffle_table requires literal elements"),
                };
            }
        }
        _ => bail!(table.expr, "shuffle_table requires an array"),
    }

    // check size
    if size != elems.len() {
        bail!(table.expr, "expected array of size {}, found one of size {}", size, elems.len());
    }

    if let Some(parallel) = args.parallel {
        if !parallel.is_power_of_two() {
            bail!(_, "parallel must be a power of two");
        }
    }

    // find best types
    let parallel = args.parallel.unwrap_or(1);
    let width_ty = Prim::from_len(elems.len());
    let index_ty = index_ty.unwrap_or(width_ty);

    let index_secret_ty = index_ty.secret_parallel_ty(parallel);
    let ret_secret_ty = ret_ty.secret_parallel_ty(parallel);

    // build shuffles
    // TODO this should really leverage >256 shuffles, though it
    // would require quite a bit of a rewrite to use u16 indices
    #[allow(non_snake_case)]
    let MAX_SHUFFLE_SIZE: usize = min(2*(1 << MAX_NPW2), 256);
    let shuffle_size = min(
        MAX_SHUFFLE_SIZE,
        max(
            elems.len().next_power_of_two(),
            2*parallel
        )
    );

    let pack_secret_ty = Prim::U8.secret_parallel_ty(parallel);
    let pack_secret_wide_ty = Prim::U8.secret_wide_ty(parallel);
    let table_secret_ty = Prim::U8.secret_parallel_ty(shuffle_size/2);
    let table_secret_wide_ty = Prim::U8.secret_wide_ty(shuffle_size/2);
    let table_merge_secret_ty = Prim::U8.secret_parallel_ty(parallel);
    let table_merge_secret_wide_ty = Prim::U8.secret_wide_ty(parallel);
    let merge_ty = if ret_ty == Prim::Bool { Prim::U8 } else { ret_ty };
    let merge_secret_ty = merge_ty.secret_parallel_ty(parallel);
    let merge_secret_wide_ty = merge_ty.secret_wide_ty(parallel);

    let index_secret_ty_const: syn::Path = if parallel == 1 {
        parse_quote! { #index_secret_ty::const_ }
    } else {
        parse_quote! { #index_secret_ty::const_splat }
    };
    let table_secret_ty_const: syn::Path = if shuffle_size/2 == 1 {
        parse_quote! { #table_secret_ty::const_ }
    } else {
        parse_quote! { #table_secret_ty::const_splat }
    };
    let merge_secret_ty_const: syn::Path = if parallel == 1 {
        parse_quote! { #merge_secret_ty::const_ }
    } else {
        parse_quote! { #merge_secret_ty::const_splat }
    };

    // pad argument as needed
    //
    // NOTE, we're really just splitting into 8-comparisons between 6-bit
    // shuffles, this could be smarter but it would get quite a bit more
    // complicated
    if elems.len() > 256*MAX_SHUFFLE_SIZE as usize {
        bail!(_, "shuffle_table currently only supports up to 2^{} elements",
            (256*MAX_SHUFFLE_SIZE).next_power_of_two().trailing_zeros());
    }
    let mut packs = Vec::<syn::Stmt>::new();
    let mask = lit!(MAX_SHUFFLE_SIZE-1);
    //if shuffle_size/2 > parallel * index_ty.width()/8 {
    packs.push(parse_quote! {
        // extend unused lanes
        let a0 = #table_secret_ty::from_cast(
            #table_secret_wide_ty::from(
                #pack_secret_wide_ty::from_cast(
                    // truncate lanes
                    #pack_secret_ty::from_cast(
                        a.clone() & #index_secret_ty_const(#mask)
                    )
                )
            )
        );
    });
    if elems.len() > MAX_SHUFFLE_SIZE {
        let n = lit!(MAX_SHUFFLE_SIZE.next_power_of_two().trailing_zeros() as usize);
        //if shuffle_size/2 > parallel * index_ty.width()/8 {
        packs.push(parse_quote! {
            // extend unused lanes
            let a1 = #table_secret_ty::from_cast(
                #table_secret_wide_ty::from(
                    #pack_secret_wide_ty::from_cast(
                        // truncate lanes
                        #pack_secret_ty::from_cast(
                            a.clone() >> #index_secret_ty_const(#n)
                        )
                    )
                )
            );
        });
    }

    // build shuffles
    let mut shuffles = Vec::<syn::Stmt>::new();
    let out_bytes = max(ret_ty.width(), 8)/8;
    for out_byte in 0..out_bytes {
        for i in (0..elems.len()).step_by(shuffle_size) {
            // build the shuffle tables
            let prim_table1 = (i..i+shuffle_size/2).map(|j| {
                lit!((elems.get(j).copied().unwrap_or(0) >> (out_byte*8)) & 0xff)
            });
            let prim_table2 = (i+shuffle_size/2..i+shuffle_size).map(|j| {
                lit!((elems.get(j).copied().unwrap_or(0) >> (out_byte*8)) & 0xff)
            });

            let table1: syn::Expr;
            let table2: syn::Expr;
            if shuffle_size/2 == 1 {
                table1 = parse_quote! { #table_secret_ty::const_(#(#prim_table1),*) };
                table2 = parse_quote! { #table_secret_ty::const_(#(#prim_table2),*) };
            } else {
                table1 = parse_quote! { #table_secret_ty::const_([#(#prim_table1),*]) };
                table2 = parse_quote! { #table_secret_ty::const_([#(#prim_table2),*]) };
            }

            // select between shuffle tables
            let b = if out_bytes > 1 {
                ident!("b{}", out_byte)
            } else {
                ident!("b")
            };
            shuffles.push(
                if i == 0 && shuffle_size/2 == 1 {
                    parse_quote! {
                        let #b = a0.clone().lt(#table_secret_ty::one())
                            .select(#table1, #table2);
                    }
                } else if i == 0 {
                    parse_quote! {
                        let #b = a0.clone().shuffle2(#table1, #table2);
                    }
                } else {
                    let n = lit!(i / MAX_SHUFFLE_SIZE);
                    parse_quote! {
                        let #b = a1.clone().lt(#table_secret_ty_const(#n))
                            .select(
                                b.clone(),
                                a0.clone().shuffle2(#table1, #table2)
                            );
                    }
                }
            )
        }
    }

    // merge multi-byte lookup tables
    let mut unpack_and_merge = Vec::<syn::Stmt>::new();
    if out_bytes > 1 {
        for i in 0..out_bytes {
            let b = ident!("b{}", i);
            unpack_and_merge.push(parse_quote! {
                // extend lanes
                let #b = #merge_secret_ty::from(
                    // truncate unused lanes
                    #table_merge_secret_ty::from_cast(
                        #table_merge_secret_wide_ty::from_cast(
                            #table_secret_wide_ty::from_cast(#b)
                        )
                    )
                );
            });
        }

        let bs = (0..out_bytes)
            .map(|i| {
                let b = ident!("b{}", i);
                let n = lit!(i*8);
                quote! { (#b << #merge_secret_ty_const(#n)) }
            });
        unpack_and_merge.push(parse_quote! {
            let b = #(#bs)|*;
        });
    } else {
        unpack_and_merge.push(parse_quote! {
            // truncate unused lanes
            let b = #merge_secret_ty::from_cast(
                #merge_secret_wide_ty::from_cast(
                    #table_secret_wide_ty::from_cast(b)
                )
            );
        });
    }

    let ret: syn::Expr = if ret_ty == Prim::Bool {
        parse_quote! { b.ne(#merge_secret_ty::zero()) }
    } else {
        parse_quote! { b }
    };

    // quote
    let crate_ = crate_();
    let q = quote! {
        #[inline(never)]
        #[allow(non_snake_case)]
        #vis fn #name(a: #index_secret_ty) -> #ret_secret_ty {
            use #crate_::traits::FromCast;
            use #crate_::traits::Eq;
            use #crate_::traits::Ord;
            use #crate_::traits::Select;
            use #crate_::traits::Shuffle;
            use #crate_::traits::Shuffle2;
            use #crate_::traits::Classify;

            #(#packs)*

            #(#shuffles)*

            #(#unpack_and_merge)*
            #ret
        }
    };

    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro shuffle_table => {}", q);
    }

    TokenStream::from(q)
}
