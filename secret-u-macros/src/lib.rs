
extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::parse_macro_input;
use syn::spanned::Spanned;
use syn::parse_quote;
use quote::quote;
use darling::FromMeta;
use std::iter;

use quine_mc_cluskey as qmc;


// Quine-McCluskey boolean reduction

fn npw2(x: u128) -> usize {
    match x {
        0 => 0,
        x => 128 - (x-1).leading_zeros() as usize,
    }
}

fn find_in_width(table: &[u128]) -> usize {
    let width = npw2(table.len() as u128);
    // the width needs itself to be a power of two for our transpose to work
    width.next_power_of_two()
}

fn find_out_width(table: &[u128]) -> usize {
    let width = npw2(table.iter().max().copied().unwrap_or(0) + 1);
    // the width needs itself to be a power of two for our transpose to work
    width.next_power_of_two()
}

fn find_bitexpr(table: &[u128], width: usize, bit: usize) -> qmc::Bool {
    // build naive expr
    let mut ors = Vec::new();
    for i in 0..table.len() {
        if table[i] & (1 << bit) == (1 << bit) {
            let mut ands = Vec::new();
            for j in 0..width {
                ands.push(
                    if i & (1 << j) == (1 << j) {
                        qmc::Bool::Term(j as u8)
                    } else {
                        qmc::Bool::Not(Box::new(
                            qmc::Bool::Term(j as u8)
                        ))
                    }
                );
            }
            ors.push(qmc::Bool::And(ands));
        }
    }

    match ors.len() {
        0 => qmc::Bool::False,
        1 => ors[0].clone(),
        _ => qmc::Bool::Or(ors),
    }
}

fn simplify_bitexpr(expr: qmc::Bool) -> qmc::Bool {
    // solve using qmc, arbitrarily choose the first form
    // (all results have the same len)
    let mut expr = expr.simplify();
    expr.swap_remove(0)
}


// macro arguments and things
#[derive(Debug, FromMeta)]
struct BitSliceArgs {
    #[darling(default)]
    parallel: Option<usize>,
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
    ($s:expr, $($fmt:tt)+) => {
        return TokenStream::from(
            syn::Error::new(
                $s.span(),
                format!($($fmt)+)
            ).to_compile_error()
        )
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Prim {
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
    fn width(&self) -> usize {
        match self {
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

        parse_quote! {
            secret_u::int::#ident
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
            println!("dim {}", dim);
            let dim_s = #secret_ty::constant(dim as #prim_ty);
            let mask_s = #secret_ty::constant(mask);

            let mut i = 0;
            while i < #width {
                println!("i {}", i);
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
    expr: qmc::Bool,
    bit: usize
) -> syn::Expr {
    match expr {
        qmc::Bool::True  => parse_quote! {
            #secret_ty::constant(#prim_ty::MAX)
        },
        qmc::Bool::False => parse_quote! {
            #secret_ty::constant(0)
        },
        qmc::Bool::Term(i) => {
            let i = lit!(i);
            parse_quote! { #b[#i].clone() }
        },
        qmc::Bool::Not(v) => {
            let x = build_bitexpr(b, prim_ty, secret_ty, *v, bit);
            parse_quote! { (!#x) }
        },
        qmc::Bool::And(vs) => {
            let xs = vs.into_iter()
                .map(|v| build_bitexpr(b, prim_ty, secret_ty, v, bit))
                .collect::<Vec<_>>();
            parse_quote! { (#(#xs)&*) }
        },
        qmc::Bool::Or(vs) => {
            let xs = vs.into_iter()
                .map(|v| build_bitexpr(b, prim_ty, secret_ty, v, bit))
                .collect::<Vec<_>>();
            parse_quote! { (#(#xs)|*) }
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
/// #[bitslice]
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
/// #[attr(parallel=4)]
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
pub fn bitslice(args: TokenStream, input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-proc-macro") {
        println!("proc-macro bitslice <= {}", args);
        println!("proc-macro bitslice <= {}", input);
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

    // parse table
    let name = table.ident;
    let vis = table.vis;

    let prim;
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
            prim = match ident.as_ref().map(|s| s.as_str()) {
                Some("u8")   => Prim::U8,
                Some("u16")  => Prim::U16,
                Some("u32")  => Prim::U32,
                Some("u64")  => Prim::U64,
                Some("u128") => Prim::U128,
                Some("i8")   => Prim::I8,
                Some("i16")  => Prim::I16,
                Some("i32")  => Prim::I32,
                Some("i64")  => Prim::I64,
                Some("i128") => Prim::I128,
                _ => bail!(arr.elem, "bitslice requires a primitive type here"),
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
                _ => bail!(arr.len, "bitslice requires a literal size"),
            };
        }
        _ => bail!(table.ty, "bitslice requires an array"),
    }

    // now find the array elements
    let mut elems = Vec::<u128>::new();
    match *table.expr {
        syn::Expr::Array(arr) => {
            for elem in arr.elems {
                let lit = match &elem {
                    syn::Expr::Lit(lit) => Some(&lit.lit),
                    _ => None,
                };
                match lit {
                    Some(syn::Lit::Byte(byte)) => {
                        elems.push(byte.value() as u128);
                    }
                    Some(syn::Lit::Int(int)) => {
                        match int.base10_parse::<u128>() {
                            Ok(size) => elems.push(size),
                            Err(err) => return TokenStream::from(err.to_compile_error()),
                        };
                    }
                    _ => bail!(elem, "bitslice requires literal elements"),
                };
            }
        }
        _ => bail!(table.expr, "bitslice requires an array"),
    }

    println!("args = {:?}", args);
    println!("prim = {:?}", prim);
    println!("size = {:?}", size);
    println!("elems = {:?}", elems);

    // build function
    let prim_ty = prim.prim_ty();
    let secret_ty = prim.secret_ty();
    let a_width = find_in_width(&elems);
    let b_width = find_out_width(&elems);

    // create variables
    let parallel = args.parallel.unwrap_or(1);
    let a_args = (0..parallel)
        .map(|i| -> syn::Expr {
            let a = ident!("a{}", i);
            parse_quote! { #a }
        })
        .chain(
            iter::repeat(parse_quote! { #secret_ty :: constant(0) })
                .take(a_width - parallel)
        );
    let b_rets = (0..parallel)
        .map(|i| -> syn::Expr {
            // mask off extra bits introduced by bitwise not
            if b_width == prim.width() {
                let i = lit!(i);
                parse_quote! { b[#i].clone() }
            } else {
                let mask = lit!((1 << b_width) - 1);
                let i = lit!(i);
                parse_quote! { #secret_ty::constant(#mask) & b[#i].clone() }
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
        
        if cfg!(feature = "debug-proc-macro") {
            println!("bit({}) = {:?}", i, expr);
        }

        bitexprs.push(build_bitexpr(&ident!("a"), &prim_ty, &secret_ty, expr, i))
    }

    let q = quote! {
        #vis fn #name(a0: #secret_ty) -> #secret_ty {
            let mut a: [#secret_ty; #a_width] = [
                #(#a_args),*
            ];

            #(#a_transpose)*

            let mut b: [#secret_ty; #b_width] = [
                #(#bitexprs),*
            ];

            #(#b_transpose)*

            ( #(#b_rets),* )
        }
    };

    if cfg!(feature = "debug-proc-macro") {
        println!("proc-macro bitslice => {}", q);
    }

    TokenStream::from(q)
}
