
extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro::TokenTree;
use proc_macro::Ident;
use proc_macro::Group;
use proc_macro::Delimiter;
use proc_macro::Literal;
use proc_macro2::Span;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote_spanned;
use std::ops::Deref;
use std::collections::HashMap;
use std::iter::FromIterator;
use quote::quote;
use quote::ToTokens;
use syn::parse_macro_input;
use std::cmp::min;

use evalexpr;

const MAX_NPW2: u8 = 6;   // 2^6 bytes = u512
const MAX_LNPW2: u8 = 6;  // 2^6 lanes = 64 lanes
const LIMB_NPW2: u8 = 3;  // 2^3 bytes = u64

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
    (0..=MAX_NPW2).map(move |npw2| {
        std::array::IntoIter::new(["u", "i", "ux", "ix", "mx"]).map(move |t| {
            let has_lanes = t == "ux" || t == "ix" || t == "mx";
            (0 ..= if has_lanes { min(MAX_LNPW2, npw2) } else { 0 }).map(move |lnpw2| {
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

/// Build the type mapping to the given npw2, either a primitive type (u16)
/// for limb type ([u16;4]) depending on LIMB_NPW2 for the cutoff
fn engine_t(npw2: u8) -> TokenTree {
    if npw2 <= LIMB_NPW2 {
        TokenTree::Ident(Ident::new(
            &format!("u{}", 8 << npw2),
            proc_macro::Span::call_site()
        ))
    } else {
        let word = TokenStream2::from(TokenStream::from(TokenTree::Ident(Ident::new(
            &format!("u{}", 8 << LIMB_NPW2),
            proc_macro::Span::call_site()
        ))));
        let n = 1usize << npw2-LIMB_NPW2;
        TokenTree::Group(Group::new(
            Delimiter::None,
            TokenStream::from(quote!{[#word;#n]})
        ))
    }
}

pub fn engine_for_t(input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro engine_for_t <= {}", input);
    }

    let mut output = Vec::new();
    for npw2 in 0 ..= MAX_NPW2 {
        for lnpw2 in 0 ..= min(MAX_LNPW2, npw2) {
            fn ident(s: &str) -> TokenTree {
                TokenTree::Ident(Ident::new(s, proc_macro::Span::call_site()))
            }

            // replace word/lane types
            let u = engine_t(npw2);
            let l = engine_t(npw2-lnpw2);

            let has_lanes = lnpw2 > 0;
            let has_limbs = npw2 > LIMB_NPW2;

            let tokens = input.clone();
            let tokens = token_replace(tokens, &HashMap::from_iter([
                (format!("U"), u),
                (format!("L"), l),
                (format!("__npw2"),      TokenTree::Literal(Literal::u8_unsuffixed(npw2))),
                (format!("__lnpw2"),     TokenTree::Literal(Literal::u8_unsuffixed(lnpw2))),
                (format!("__size"),      TokenTree::Literal(Literal::usize_unsuffixed(1 << npw2))),
                (format!("__has_lanes"), ident(&format!("{}", has_lanes))),
                (format!("__lane_npw2"), TokenTree::Literal(Literal::u8_unsuffixed(npw2-lnpw2))),
                (format!("__lane_size"), TokenTree::Literal(Literal::usize_unsuffixed(1 << (npw2-lnpw2)))),
                (format!("__lanes"),     TokenTree::Literal(Literal::usize_unsuffixed(1 << lnpw2))),
                (format!("__has_limbs"), ident(&format!("{}", has_limbs))),
                (format!("__limb_t"),    ident(&format!("u{}", 8 << LIMB_NPW2))),
                (format!("__limb_i"),    ident(&format!("i{}", 8 << LIMB_NPW2))),
                (format!("__limb2_t"),   ident(&format!("u{}", 16 << LIMB_NPW2))), // double width for mul
                (format!("__limb_size"), TokenTree::Literal(Literal::usize_unsuffixed(1 << LIMB_NPW2))),
                (format!("__limbs"),     TokenTree::Literal(Literal::usize_unsuffixed(
                    if has_limbs { 1 << npw2-LIMB_NPW2 } else { 0 }))),
                (format!("__has_prim"),  ident(&format!("{}", !has_limbs))),
                (format!("__prim_t"),    ident(&format!("u{}", 8 << npw2-lnpw2))),
                (format!("__prim_i"),    ident(&format!("i{}", 8 << npw2-lnpw2))),
            ]));
            let tokens = token_if(tokens);
            output.push(tokens);
        }
    }
    let output = output.into_iter().collect();

    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro engine_for_t => {}", output);
    }

    output
}

pub fn engine_match(input: TokenStream) -> TokenStream {
    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro engine_match <= {}", input);
    }

    // this is to parse out just the match arms
    let input = TokenStream2::from(input);
    let input = quote!{match eh {#input}};
    let input = TokenStream::from(input);
    let match_ = parse_macro_input!(input as syn::ExprMatch);
    let mut arms = Vec::new();
    for arm in match_.arms {
        let pat = arm.pat;
        let guard = arm.guard.map(|(_, guard)| guard).into_iter().collect::<Vec<_>>();
        let body = arm.body;

        // generate arms for all npw2/lnpw2 combinations
        let mut matches = Vec::new();
        for npw2 in 0 ..= MAX_NPW2 {
            for lnpw2 in 0 ..= min(MAX_LNPW2, npw2) {
                // replace word/lane types
                let u = engine_t(npw2);
                let l = engine_t(npw2-lnpw2);

                let body = TokenStream2::from(token_replace(
                    TokenStream::from(body.to_token_stream()),
                    &HashMap::from_iter([
                        (format!("U"), u),
                        (format!("L"), l),
                        (format!("__npw2"),  TokenTree::Literal(Literal::u8_unsuffixed(npw2))),
                        (format!("__lnpw2"), TokenTree::Literal(Literal::u8_unsuffixed(lnpw2))),
                    ])
                ));

                let npw2 = syn::LitInt::new(&format!("{}", npw2), Span::call_site());
                let lnpw2 = syn::LitInt::new(&format!("{}", lnpw2), Span::call_site());
                matches.push(quote! {
                    (#npw2, #lnpw2) #(if #guard)* => {
                        #body
                    }
                });
            }
        }

        arms.push(quote! {
            #pat => {
                match (npw2, lnpw2) {
                    #(#matches)*

                    // unknown instructions?
                    _ => Err(Error::InvalidOpcode(ins))?
                }
            }
        });
    }

    let output = quote! {
        match opc {
            #(#arms)*

            // unknown instructions?
            _ => Err(Error::InvalidOpcode(ins))?
        }
    };

    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro engine_match => {}", output);
    }

    TokenStream::from(output)
}
