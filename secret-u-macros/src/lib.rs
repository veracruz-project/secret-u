
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

fn crate_() -> proc_macro2::TokenStream {
    if env::var("CARGO_CRATE_NAME").unwrap() == "secret_u" {
        quote! { crate }
    } else {
        quote! { ::secret_u }
    }
}


// use the boolean_expression crate for bitexpr simplification

fn find_in_width(table: &[u128], parallel: usize) -> usize {
    let width = table.len().next_power_of_two().trailing_zeros() as usize;
    let width = max(width, parallel);
    // the width needs itself to be a power of two for our transpose to work
    width.next_power_of_two()
}

fn find_out_width(table: &[u128], parallel: usize) -> usize {
    let width = (table.iter().max().copied().unwrap_or(0) + 1)
        .next_power_of_two().trailing_zeros() as usize;
    let width = max(width, parallel);
    // the width needs itself to be a power of two for our transpose to work
    width.next_power_of_two()
}

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
    let expr = expr.simplify_via_bdd();
    #[cfg(all(feature="bitslice-simplify-identities", not(feature="bitslice-simplify-bdd")))]
    let expr = expr.simplify_via_laws();

    expr
}


// macro arguments and things
#[derive(Debug, FromMeta)]
struct BitSliceArgs {
    #[darling(default)]
    parallel: Option<usize>,
    #[darling(default)]
    index_type: Option<String>,
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
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl Prim {
    fn from_ident(ident: &str) -> Option<Prim> {
        match ident {
            "bool" => Some(Prim::Bool),
            "u8"   => Some(Prim::U8),
            "u16"  => Some(Prim::U16),
            "u32"  => Some(Prim::U32),
            "u64"  => Some(Prim::U64),
            "u128" => Some(Prim::U128),
            "i8"   => Some(Prim::I8),
            "i16"  => Some(Prim::I16),
            "i32"  => Some(Prim::I32),
            "i64"  => Some(Prim::I64),
            "i128" => Some(Prim::I128),
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

    fn width(&self) -> usize {
        match self {
            Prim::Bool => 1,
            Prim::U8   => 8,
            Prim::U16  => 16,
            Prim::U32  => 32,
            Prim::U64  => 64,
            Prim::U128 => 128,
            Prim::I8   => 8,
            Prim::I16  => 16,
            Prim::I32  => 32,
            Prim::I64  => 64,
            Prim::I128 => 128,
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
        };

        parse_quote! {
            #ident
        }
    }

    fn secret_ty(&self) -> syn::Type {
        let ident = match self {
            Prim::Bool => ident!("SecretBool"),
            Prim::U8   => ident!("SecretU8"),
            Prim::U16  => ident!("SecretU16"),
            Prim::U32  => ident!("SecretU32"),
            Prim::U64  => ident!("SecretU64"),
            Prim::U128 => ident!("SecretU128"),
            Prim::I8   => ident!("SecretI8"),
            Prim::I16  => ident!("SecretI16"),
            Prim::I32  => ident!("SecretI32"),
            Prim::I64  => ident!("SecretI64"),
            Prim::I128 => ident!("SecretI128"),
        };

        let crate_ = crate_();
        parse_quote! {
            #crate_::int::#ident
        }
    }
}

fn build_transpose(
    a: &syn::Ident,
    prim_ty: &syn::Type,
    secret_ty: &syn::Type,
    width: usize
) -> Vec<syn::Stmt> {
    let dim = width/2;
    let mask = lit!((1 << dim) - 1);

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

fn build_bitexpr(
    b: &syn::Ident,
    prim_ty: &syn::Type,
    secret_ty: &syn::Type,
    expr: be::Expr<u8>,
    bit: usize
) -> proc_macro2::TokenStream {
    match expr {
        be::Expr::Const(true) => {
            quote! { #secret_ty::ones() }
        },
        be::Expr::Const(false) => {
            quote! { #secret_ty::zero() }
        },
        be::Expr::Terminal(i) => {
            let i = lit!(i);
            quote! { #b[#i].clone() }
        },
        be::Expr::Not(v) => {
            let x = build_bitexpr(b, prim_ty, secret_ty, *v, bit);
            quote! { (!#x) }
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
                    xs.push(build_bitexpr(b, prim_ty, secret_ty, *x, bit));
                }
            }

            match xs.len() {
                0 => quote! { #secret_ty::ones() },
                _ => quote! { (#(#xs)&*) },
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
                    xs.push(build_bitexpr(b, prim_ty, secret_ty, *x, bit));
                }
            }

            match xs.len() {
                0 => quote! { #secret_ty::zero() },
                _ => quote! { (#(#xs)|*) },
            }
        },
    }
}


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
/// #[static_bitslice]
/// const table: [u8; 256] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in0: SecretU8) -> SecretU8;
/// ```
/// 
/// With args:
/// ```
/// #[static_bitslice(parallel=4)]
/// const table: [u16; 6] = [
///     ...
/// ];
/// ```
///
/// Result:
/// ```
/// fn table(in0: SecretU16, in1: SecretU16, in2: SecretU16, in3: SecretU16)
///     -> (SecretU16, SecretU16, SecretU16, SecretU16)
/// ```
///
#[proc_macro_attribute]
pub fn static_bitslice(args: TokenStream, input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro static_bitslice <= {}", args);
        println!("proc-macro static_bitslice <= {}", input);
    }

    let args = parse_macro_input!(args as syn::AttributeArgs);
    let table = parse_macro_input!(input as syn::ItemConst);

    // parse args
    let args = match BitSliceArgs::from_list(&args) {
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
                None => bail!(arr.elem, "static_bitslice requires a primitive type here"),
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
                _ => bail!(arr.len, "static_bitslice requires a literal size"),
            };
        }
        _ => bail!(table.ty, "static_bitslice requires an array"),
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
                    _ => bail!(elem, "static_bitslice requires literal elements"),
                };
            }
        }
        _ => bail!(table.expr, "static_bitslice requires an array"),
    }

    // check size
    if size != elems.len() {
        bail!(table.expr, "expected array of size {}, found one of size {}", size, elems.len());
    }

    // find best types
    let elem_ty = Prim::from_len(elems.len());
    let mid_ty = max_by_key(elem_ty, ret_ty, |x| x.width());
    let index_ty = index_ty.unwrap_or(elem_ty);

    // build function
    let parallel = args.parallel.unwrap_or(1);
    let prim_ty = mid_ty.prim_ty();
    let secret_ty = mid_ty.secret_ty();
    let index_secret_ty = index_ty.secret_ty();
    let ret_secret_ty = ret_ty.secret_ty();
    let a_width = find_in_width(&elems, parallel);
    let b_width = find_out_width(&elems, parallel);

    let arg_tys = (0..parallel).map(|i| -> syn::FnArg {
        let a = ident!("a{}", i);
        parse_quote! { #a: #index_secret_ty }
    });
    let ret_tys = (0..parallel).map(|_| -> syn::Type {
        parse_quote! { #ret_secret_ty }
    });

    // create variables
    let a_args = (0..parallel)
        .map(|i| -> syn::Expr {
            let a = ident!("a{}", i);
            if mid_ty.width() > index_ty.width() {
                parse_quote! { #secret_ty::from(#a) }
            } else if mid_ty.width() < index_ty.width() {
                parse_quote! { #secret_ty::cast(#a) }
            } else {
                parse_quote! { #a }
            }
        })
        .chain(
            iter::repeat(parse_quote! { #secret_ty::zero() })
                .take(a_width - parallel)
        );
    let b_rets = (0..parallel)
        .map(|i| -> syn::Expr {
            // mask off extra bits introduced by bitwise not
            let ret: syn::Expr = if b_width == ret_ty.width() {
                let i = lit!(i);
                parse_quote! { b[#i].clone() }
            } else {
                let mask = lit!((1 << b_width) - 1);
                let i = lit!(i);
                parse_quote! { #secret_ty::const_(#mask) & b[#i].clone() }
            };

            if ret_ty == Prim::Bool {
                parse_quote! { (#ret & #secret_ty::one()).eq(#secret_ty::one()) }
            } else if ret_ty.width() > mid_ty.width() {
                parse_quote! { #ret_secret_ty::from(#ret) }
            } else if ret_ty.width() < mid_ty.width() {
                parse_quote! { #ret_secret_ty::cast(#ret) }
            } else {
                parse_quote! { #ret }
            }
        });

    // transposes
    let a_transpose = build_transpose(&ident!("a"), &prim_ty, &secret_ty, a_width);
    let b_transpose = build_transpose(&ident!("b"), &prim_ty, &secret_ty, b_width);

    // find exprs, simplify, and convert to quote
    let mut bitexprs = Vec::new();
    for i in 0..b_width {
        let expr = find_bitexpr(&elems, a_width, i);
        let expr = simplify_bitexpr(expr);
        
//        if cfg!(feature = "debug-proc-macros") {
//            println!("bit({}) = {:?}", i, expr);
//        }

        bitexprs.push(build_bitexpr(&ident!("a"), &prim_ty, &secret_ty, expr, i))
    }

    let crate_ = crate_();
    let q = quote! {
        #[allow(non_snake_case)]
        #vis fn #name(#(#arg_tys),*) -> (#(#ret_tys),*) {
            use #crate_::int::Cast;
            use #crate_::int::SecretEq;

            let mut a: [#secret_ty; #a_width] = [
                #(#a_args),*
            ];

            #(#a_transpose)*

            let mut b: [#secret_ty; #b_width] = [
                #(#bitexprs),*
            ];

            #(#b_transpose)*

            (#(#b_rets),*)
        }
    };

    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro static_bitslice => {}", q);
    }

    TokenStream::from(q)
}
