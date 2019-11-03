#![recursion_limit = "128"]
#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]
#![warn(unused_extern_crates)]

//! # plex, a parser and lexer generator
//! See README.md for documentation.

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;
extern crate redfa;
#[macro_use]
extern crate syn;

mod lexer;

use proc_macro::TokenStream;

/// Defines a lexer.
#[proc_macro]
pub fn lexer(tok: TokenStream) -> TokenStream {
    lexer::lexer(tok)
}
