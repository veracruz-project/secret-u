
extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro::TokenTree;
use proc_macro::Ident;
use proc_macro::Group;
use proc_macro::Literal;
use proc_macro2::Span;
use quote::quote_spanned;
use std::ops::Deref;
use std::collections::HashMap;
use std::iter::FromIterator;

use evalexpr;


fn token_replace(input: TokenStream, map: &HashMap<String, TokenTree>) -> TokenStream {
    input.into_iter()
        .map(|tt| {
            match tt {
                TokenTree::Ident(ident) => {
                    match map.get(ident.to_string().deref()) {
                        Some(to) => {
                            let mut to = to.clone();
                            to.set_span(ident.span());
                            to
                        }
                        None => {
                            TokenTree::Ident(ident)
                        }
                    }
                },
                TokenTree::Group(group) => {
                    let mut ngroup = Group::new(
                        group.delimiter(),
                        token_replace(group.stream(), map),
                    );
                    ngroup.set_span(group.span());
                    TokenTree::Group(ngroup)
                },
                _ => tt,
            }
        })
        .collect()
}

fn token_if(input: TokenStream) -> TokenStream {
    let mut output = Vec::new();
    let mut stream = input.into_iter();
    while let Some(tt) = stream.next() {
        match tt {
            TokenTree::Ident(ident) => {
                if ident.to_string() == "__if" {
                    // grab rest of conditional
                    let cond = match stream.next().unwrap() {
                        TokenTree::Group(group) => group,
                        _ => panic!("expected group?"),
                    };
                    let block = match stream.next().unwrap() {
                        TokenTree::Group(group) => group,
                        _ => panic!("expected group?"),
                    };

                    // eval
                    let res = evalexpr::eval_boolean(&format!("{}", cond));

                    // output?
                    match res {
                        Ok(true) => {
                            // make sure to recurse inside __if!
                            let stream = block.stream();
                            let stream = token_if(stream);
                            output.extend(stream)
                        }
                        Ok(false) => {
                            // do nothing
                        }
                        Err(err) => {
                            let err = format!("{}", err);
                            output.extend(TokenStream::from(quote_spanned! {
                                Span::from(cond.span()) => compile_error!(#err);
                            }).into_iter());
                        }
                    }
                } else {
                    output.push(TokenTree::Ident(ident));
                }
            }
            TokenTree::Group(group) => {
                let mut ngroup = Group::new(
                    group.delimiter(),
                    token_if(group.stream()),
                );
                ngroup.set_span(group.span());
                output.push(TokenTree::Group(ngroup));
            }
            _ => {
                output.push(tt);
            }
        }
    }

    output.into_iter().collect()
}

fn token_for_lanes(input: TokenStream, lanes: usize) -> TokenStream {
    let mut output = Vec::new();
    let mut stream = input.into_iter();
    while let Some(tt) = stream.next() {
        match tt {
            TokenTree::Ident(ident) => {
                if ident.to_string() == "__for_lanes" {
                    // grab block
                    let block = match stream.next().unwrap() {
                        TokenTree::Group(group) => group,
                        _ => panic!("expected group?"),
                    };

                    for i in 0..lanes {
                        // replace hard-coded iterator names, don't bother
                        // to recurse, that would require a significant rewrite
                        let stream = block.stream();
                        let stream = token_replace(stream, &HashMap::from_iter([
                            (format!("__a"), 
                                TokenTree::Ident(Ident::new(&format!("a{}", i), proc_macro::Span::call_site()))),
                            (format!("__i"),
                                TokenTree::Literal(Literal::usize_unsuffixed(i))),
                        ]));
                        output.extend(stream)
                    }
                } else {
                    output.push(TokenTree::Ident(ident));
                }
            }
            TokenTree::Group(group) => {
                let mut ngroup = Group::new(
                    group.delimiter(),
                    token_for_lanes(group.stream(), lanes),
                );
                ngroup.set_span(group.span());
                output.push(TokenTree::Group(ngroup));
            }
            _ => {
                output.push(tt);
            }
        }
    }

    output.into_iter().collect()
}

// core generator for secret types
fn secret_t_map<'a>(
    suffix: &'a str
) -> impl Iterator<Item=(u8, u8, HashMap<String, TokenTree>)> + 'a {
    (0..=6).map(move |npw2| {
        std::array::IntoIter::new(["u", "i", "ux", "ix", "mx"]).map(move |t| {
            let has_lanes = t == "ux" || t == "ix" || t == "mx";
            (0 ..= if has_lanes { npw2 } else { 0 }).map(move |lnpw2| {
                fn ident(s: &str) -> TokenTree {
                    TokenTree::Ident(Ident::new(s, proc_macro::Span::call_site()))
                }

                (npw2, lnpw2, HashMap::from_iter([
                    (format!("__secret_t{}", suffix),
                        if has_lanes {
                            ident(&format!("Secret{}{}x{}",
                                t.chars().next().unwrap().to_uppercase(),
                                8 << npw2-lnpw2,
                                1 << lnpw2))
                        } else {
                            ident(&format!("Secret{}{}",
                                t.to_uppercase(),
                                8 << npw2))
                        }),
                    (format!("__secret_u{}", suffix),
                        ident(&format!("SecretU{}", 8 << npw2))),
                    (format!("__secret_i{}", suffix),
                        ident(&format!("SecretI{}", 8 << npw2))),
                    (format!("__secret_ux{}", suffix),
                        ident(&format!("SecretU{}x{}", 8 << npw2-lnpw2, 1 << lnpw2))),
                    (format!("__secret_ix{}", suffix),
                        ident(&format!("SecretI{}x{}", 8 << npw2-lnpw2, 1 << lnpw2))),
                    (format!("__secret_mx{}", suffix),
                        ident(&format!("SecretM{}x{}", 8 << npw2-lnpw2, 1 << lnpw2))),
                    (format!("__U{}", suffix),
                        ident(&format!("U{}", 8 << npw2))),
                    (format!("__lane_U{}", suffix),
                        ident(&format!("U{}", 8 << (npw2-lnpw2)))),
                    (format!("__t{}", suffix),
                        TokenTree::Literal(Literal::string(t))),
                    (format!("__npw2{}", suffix),
                        TokenTree::Literal(Literal::u8_unsuffixed(npw2))),
                    (format!("__lnpw2{}", suffix),
                        TokenTree::Literal(Literal::u8_unsuffixed(lnpw2))),
                    (format!("__lane_npw2{}", suffix),
                        TokenTree::Literal(Literal::u8_unsuffixed(npw2-lnpw2))),
                    (format!("__size{}", suffix),
                        TokenTree::Literal(Literal::usize_unsuffixed(1 << npw2))),
                    (format!("__lane_size{}", suffix),
                        TokenTree::Literal(Literal::usize_unsuffixed(1 << (npw2-lnpw2)))),
                    (format!("__lanes{}", suffix),
                        TokenTree::Literal(Literal::usize_unsuffixed(1 << lnpw2))),
                    (format!("__has_lanes{}", suffix),
                        ident(&format!("{}", has_lanes))),
                    (format!("__lane_t{}", suffix),
                        ident(&format!("Secret{}{}",
                            t.chars().next().unwrap().to_uppercase(),
                            8 << (npw2-lnpw2)))),
                    (format!("__lane_u{}", suffix),
                        ident(&format!("SecretU{}", 8 << (npw2-lnpw2)))),
                    (format!("__lane_i{}", suffix),
                        ident(&format!("SecretI{}", 8 << (npw2-lnpw2)))),
                    (format!("__has_prim{}", suffix),
                        ident(&format!("{}", (8 << (npw2-lnpw2)) <= 128))),
                    (format!("__prim_t{}", suffix),
                        ident(&format!("{}{}",
                            t.chars().next().unwrap(),
                            8 << (npw2-lnpw2)))),
                    (format!("__prim_u{}", suffix),
                        ident(&format!("u{}", 8 << (npw2-lnpw2)))),
                    (format!("__prim_i{}", suffix),
                        ident(&format!("i{}", 8 << (npw2-lnpw2)))),
                ]))
            })
        })
    })
        .flatten()
        .flatten()
}


pub fn for_secret_t(input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro for_secret_t <= {}", input);
    }

    let mut output = Vec::new();
    for (_, lnpw2, map) in secret_t_map("") {
        let tokens = input.clone();
        let tokens = token_replace(tokens, &map);
        let tokens = token_for_lanes(tokens, 1usize << lnpw2);
        let tokens = token_if(tokens);
        output.push(tokens);
    }
    let output = output.into_iter().collect();

    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro for_secret_t => {}", output);
    }

    output
}

pub fn for_secret_t_2(input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro for_secret_t_2 <= {}", input);
    }

    let mut output = Vec::new();
    for (_, _, mut map) in secret_t_map("") {
        for (_, _, map_2) in secret_t_map("_2") {
            map.extend(map_2);
            let tokens = input.clone();
            let tokens = token_replace(tokens, &map);
            let tokens = token_if(tokens);
            output.push(tokens);
        }
    }
    let output = output.into_iter().collect();

    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro for_secret_t_2 => {}", output);
    }

    output
}
