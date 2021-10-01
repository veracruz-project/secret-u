
extern crate proc_macro;

use proc_macro::TokenStream;
use syn::parse_macro_input;
use syn::spanned::Spanned;
use quote::quote;
use std::env;
use std::ops::Deref;


fn crate_() -> proc_macro2::TokenStream {
    if env::var("CARGO_CRATE_NAME").unwrap() == "secret_u" {
        quote! { crate }
    } else {
        quote! { ::secret_u }
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


pub fn lazy_compile(args: TokenStream, input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro lazy_compile <= {}", args);
        println!("proc-macro lazy_compile <= {}", input);
    }

    let _args = parse_macro_input!(args as syn::AttributeArgs);
    let fn_ = parse_macro_input!(input as syn::ItemFn);

    // find things
    let attrs = fn_.attrs;
    let vis   = fn_.vis;
    let block = fn_.block;
    let constness = fn_.sig.constness.iter();
    let asyncness = fn_.sig.asyncness.iter();
    let unsafety  = fn_.sig.unsafety.iter();
    let abi       = fn_.sig.abi.iter();

    let fn_name  = fn_.sig.ident;

    let mut arg_muts = Vec::new();
    let mut arg_names = Vec::new();
    let mut arg_types = Vec::new();
    for input in fn_.sig.inputs {
        match input {
            syn::FnArg::Typed(arg) => {
                arg_types.push(arg.ty);
                match arg.pat.deref() {
                    syn::Pat::Ident(ident) => {
                        arg_muts.push(ident.mutability);
                        arg_names.push(ident.ident.clone());
                    }
                    x => {
                        bail!(x, "did not expect this here");
                    }
                }
            }
            x => {
                bail!(x, "did not expect this here");
            }
        }
    }

    let ret_type = match fn_.sig.output {
        syn::ReturnType::Type(_, ty) => {
            ty
        }
        x => {
            bail!(x, "did not expect this here");
        }
    };

    // quote
    let crate_ = crate_();
    let q = quote! {
        #(#attrs)*
        #vis fn #(#constness)* #(#asyncness)* #(#unsafety)* #(#abi)*
        #fn_name(#(#arg_names: #arg_types),*) -> #ret_type {
            use #crate_::compile;

            thread_local! {
                static LAZY_CLOSURE: Box<
                    dyn Fn(#(#arg_types),*) -> #ret_type
                > = {
                    Box::new(compile!(
                        |#(#arg_muts #arg_names: #arg_types),*| -> #ret_type {
                            #block
                        }
                    ))
                };
            }

            LAZY_CLOSURE.with(|f| f(#(#arg_names),*))
        }
    };

    if cfg!(feature = "debug-proc-macros") {
        println!("proc-macro lazy_compile => {}", q);
    }

    TokenStream::from(q)
}

