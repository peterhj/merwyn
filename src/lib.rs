#![feature(non_ascii_idents)]
#![feature(proc_macro_hygiene)]
//#![feature(use_extern_macros)]

//#[macro_use] extern crate lalrpop_util;
//#[macro_use] extern crate lazy_static;
//extern crate parking_lot;
extern crate plex;

//lalrpop_mod!(pub grammar);

//pub mod experimental;
pub mod lang;
//pub mod repl;
pub mod vm;
