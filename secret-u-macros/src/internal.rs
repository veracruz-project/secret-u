
extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro::TokenTree;
use proc_macro::Ident;
use proc_macro::Group;
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

macro_rules! ident {
    ($($fmt:tt)+) => {
        TokenTree::Ident(Ident::new(&format!($($fmt)+), proc_macro::Span::call_site()))
    }
}

macro_rules! lit {
    ($lit:expr) => {
        TokenTree::Literal($lit)
    }
}

fn token_replace(input: TokenStream, map: &HashMap<String, TokenTree>) -> TokenStream {
    // helper function to set span recursively
    fn token_setspan(tt: &mut TokenTree, span: proc_macro::Span) {
        tt.set_span(span);
        if let TokenTree::Group(group) = tt {
            let mut ngroup = Group::new(
                group.delimiter(),
                group.stream().into_iter().map(|mut tt| {
                    token_setspan(&mut tt, span);
                    tt
                }).collect()
            );
            ngroup.set_span(group.span());
            *tt = TokenTree::Group(ngroup)
        }
    }

    input.into_iter()
        .map(|tt| {
            match tt {
                TokenTree::Ident(ident) => {
                    match map.get(ident.to_string().deref()) {
                        Some(to) => {
                            let mut to = to.clone();
                            token_setspan(&mut to, ident.span());
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

// core generator for secret types
fn secret_t_map<'a>(
    suffix: &'a str
) -> impl Iterator<Item=(u8, u8, HashMap<String, TokenTree>)> + 'a {
    (0..=MAX_NPW2).map(move |npw2| {
        std::array::IntoIter::new(["u", "i", "ux", "ix", "mx"]).map(move |t| {
            let has_lanes = t == "ux" || t == "ix" || t == "mx";
            (0 ..= if has_lanes { min(MAX_LNPW2, npw2) } else { 0 }).map(move |lnpw2| {
                (npw2, lnpw2, HashMap::from_iter([
                    (format!("__secret_t{}", suffix),
                        if has_lanes {
                            ident!("Secret{}{}x{}",
                                t.chars().next().unwrap().to_uppercase(),
                                8 << npw2-lnpw2,
                                1 << lnpw2)
                        } else {
                            ident!("Secret{}{}",
                                t.to_uppercase(),
                                8 << npw2)
                        }),
                    (format!("__secret_u{}", suffix),   ident!("SecretU{}", 8 << npw2)),
                    (format!("__secret_i{}", suffix),   ident!("SecretI{}", 8 << npw2)),
                    (format!("__secret_ux{}", suffix),  ident!("SecretU{}x{}", 8 << npw2-lnpw2, 1 << lnpw2)),
                    (format!("__secret_ix{}", suffix),  ident!("SecretI{}x{}", 8 << npw2-lnpw2, 1 << lnpw2)),
                    (format!("__secret_mx{}", suffix),  ident!("SecretM{}x{}", 8 << npw2-lnpw2, 1 << lnpw2)),
                    (format!("__U{}", suffix),          ident!("U{}", 8 << npw2)),
                    (format!("__lane_U{}", suffix),     ident!("U{}", 8 << (npw2-lnpw2))),
                    (format!("__t{}", suffix),          lit!(Literal::string(t))),
                    (format!("__npw2{}", suffix),       lit!(Literal::u8_unsuffixed(npw2))),
                    (format!("__lnpw2{}", suffix),      lit!(Literal::u8_unsuffixed(lnpw2))),
                    (format!("__lane_npw2{}", suffix),  lit!(Literal::u8_unsuffixed(npw2-lnpw2))),
                    (format!("__size{}", suffix),       lit!(Literal::usize_unsuffixed(1 << npw2))),
                    (format!("__lane_size{}", suffix),  lit!(Literal::usize_unsuffixed(1 << (npw2-lnpw2)))),
                    (format!("__lanes{}", suffix),      lit!(Literal::usize_unsuffixed(1 << lnpw2))),
                    (format!("__has_lanes{}", suffix),  ident!("{}", has_lanes)),
                    (format!("__lane_t{}", suffix),
                        ident!("Secret{}{}",
                            t.chars().next().unwrap().to_uppercase(),
                            8 << (npw2-lnpw2))),
                    (format!("__lane_u{}", suffix),     ident!("SecretU{}", 8 << (npw2-lnpw2))),
                    (format!("__lane_i{}", suffix),     ident!("SecretI{}", 8 << (npw2-lnpw2))),
                    (format!("__has_prim{}", suffix),   ident!("{}", (8 << (npw2-lnpw2)) <= 128)),
                    (format!("__prim_t{}", suffix),
                        ident!("{}{}",
                            t.chars().next().unwrap(),
                            8 << (npw2-lnpw2))),
                    (format!("__prim_u{}", suffix),     ident!("u{}", 8 << (npw2-lnpw2))),
                    (format!("__prim_i{}", suffix),     ident!("i{}", 8 << (npw2-lnpw2))),
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
    for (_, _, map) in secret_t_map("") {
        let tokens = input.clone();
        let tokens = token_replace(tokens, &map);
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

// quick macros to get configurable limb types
pub fn engine_limb_t(_input: TokenStream) -> TokenStream {
    TokenStream::from(ident!("u{}", 8 << LIMB_NPW2))
}

pub fn engine_limbi_t(_input: TokenStream) -> TokenStream {
    TokenStream::from(ident!("i{}", 8 << LIMB_NPW2))
}

pub fn engine_limb2_t(_input: TokenStream) -> TokenStream {
    TokenStream::from(ident!("u{}", 2*8 << LIMB_NPW2))
}

/// Build the type mapping to the given npw2, either a primitive type (u16)
/// or limb type ([u16]) depending on LIMB_NPW2 for the cutoff
fn engine_t(npw2: u8) -> TokenTree {
    if npw2 <= LIMB_NPW2 {
        ident!("u{}", 8 << npw2)
    } else {
        let limb = TokenStream2::from(TokenStream::from(ident!("u{}", 8 << LIMB_NPW2)));
        TokenStream::from(quote!{ [#limb] }).into_iter().next().unwrap()
    }
}

fn engine_short_map<'a>() -> impl Iterator<Item=(u8, HashMap<String, TokenTree>)> + 'a {
    (0 ..= LIMB_NPW2).map(move |npw2| {
        (npw2, HashMap::from_iter([
            (format!("__prim_t"),    ident!("u{}", 8 << npw2)),
            (format!("__primi_t"),   ident!("i{}", 8 << npw2)),

            (format!("__npw2"),      lit!(Literal::u8_unsuffixed(npw2))),
            (format!("__size"),      lit!(Literal::usize_unsuffixed(1 << npw2))),
        ]))
    })
}

pub fn engine_for_short_t(input: TokenStream) -> TokenStream {
    if cfg!(featurefor_t = "debug-internal-proc-macros") {
        println!("proc-macro engine_for_short_t <= {}", input);
    }

    let mut output = Vec::new();
    for (_, map) in engine_short_map() {
        let tokens = input.clone();
        let tokens = token_replace(tokens, &map);
        let tokens = token_if(tokens);
        output.push(tokens);
    }
    let output = output.into_iter().collect();

    if cfg!(feature = "debug-internal-proc-macros") {
        println!("proc-macro engine_for_short_t => {}", output);
    }

    output
}

fn engine_map<'a>() -> impl Iterator<Item=(u8, u8, HashMap<String, TokenTree>)> + 'a {
    (0 ..= LIMB_NPW2+1).map(move |npw2| {
        (0 ..= min(LIMB_NPW2+1, npw2)).map(move |lane_npw2| {
            // these macros map to state access
            let (rd, ra, rb, rx, ld, la, lb, lx, rd_0);
            if npw2 <= LIMB_NPW2 {
                let t = TokenStream2::from(TokenStream::from(engine_t(npw2)));
                rd = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.short_reg_mut::<#t>(d)?) });
                ra = TokenStream::from(quote!{ (unsafe {&    *s.get()}.short_reg::<#t>(a)?) });
                rb = TokenStream::from(quote!{ (unsafe {&    *s.get()}.short_reg::<#t>(b)?) });
                rx = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.short_scratch::<#t>()) });
            } else {
                rd = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.long_reg_mut(d, npw2)?) });
                ra = TokenStream::from(quote!{ (unsafe {&    *s.get()}.long_reg(a, npw2)?) });
                rb = TokenStream::from(quote!{ (unsafe {&    *s.get()}.long_reg(b, npw2)?) });
                rx = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.long_scratch(npw2)) });
            }
            if lane_npw2 <= LIMB_NPW2 {
                let t = TokenStream2::from(TokenStream::from(engine_t(lane_npw2)));
                ld   = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.short_reg_mut::<#t>(d)?) });
                la   = TokenStream::from(quote!{ (unsafe {&    *s.get()}.short_reg::<#t>(a)?) });
                lb   = TokenStream::from(quote!{ (unsafe {&    *s.get()}.short_reg::<#t>(b)?) });
                lx   = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.short_scratch::<#t>()) });
                rd_0 = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.short_reg_mut::<#t>(d << lnpw2)?) });
            } else {
                ld   = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.long_reg_mut(d, npw2-lnpw2)?) });
                la   = TokenStream::from(quote!{ (unsafe {&    *s.get()}.long_reg(a, npw2-lnpw2)?) });
                lb   = TokenStream::from(quote!{ (unsafe {&    *s.get()}.long_reg(b, npw2-lnpw2)?) });
                lx   = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.long_scratch(npw2-lnpw2)) });
                rd_0 = TokenStream::from(quote!{ (unsafe {&mut *s.get()}.long_reg_mut(d << lnpw2, npw2-lnpw2)?) });
            }

            (npw2, lane_npw2, HashMap::from_iter([
                (format!("__t"),         engine_t(npw2)),
                (format!("__lane_t"),    engine_t(lane_npw2)),
                (format!("__has_limbs"), ident!("{}", npw2 > LIMB_NPW2)),
                (format!("__lane_has_limbs"), ident!("{}", lane_npw2 > LIMB_NPW2)),

                // these macros map to state access
                (format!("__rd"),   rd.into_iter().next().unwrap()),
                (format!("__ra"),   ra.into_iter().next().unwrap()),
                (format!("__rb"),   rb.into_iter().next().unwrap()),
                (format!("__rx"),   rx.into_iter().next().unwrap()),
                (format!("__ld"),   ld.into_iter().next().unwrap()),
                (format!("__la"),   la.into_iter().next().unwrap()),
                (format!("__lb"),   lb.into_iter().next().unwrap()),
                (format!("__lx"),   lx.into_iter().next().unwrap()),
                (format!("__rd_0"), rd_0.into_iter().next().unwrap()),
            ]))
        })
    })
        .flatten()
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
        let body = arm.body;

        // generate arms for npw2/lnpw2 combinations
        for (npw2, lane_npw2, map) in engine_map() {
            // replace tokens in body
            let tokens = TokenStream::from(body.to_token_stream());
            let tokens = token_replace(tokens, &map);
            let body = TokenStream2::from(tokens);

            let npw2_pat = TokenStream2::from(TokenStream::from(
                if npw2 <= LIMB_NPW2 {
                    lit!(Literal::u8_unsuffixed(npw2))
                } else {
                    ident!("_")
                }
            ));

            let lane_npw2_pat = TokenStream2::from(TokenStream::from(
                if lane_npw2 <= LIMB_NPW2 {
                    lit!(Literal::u8_unsuffixed(lane_npw2))
                } else {
                    ident!("_")
                }
            ));

            arms.push(quote! {
                (#pat, #npw2_pat, #lane_npw2_pat) => {
                    #body
                }
            });
        }
    }

    let output = quote! {
        #[allow(unused_parens)]
        match (op, npw2, npw2-lnpw2) {
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
