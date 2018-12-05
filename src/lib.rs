#![feature(non_ascii_idents)]
#![feature(proc_macro_hygiene)]

//#[macro_use] extern crate lazy_static;
//extern crate parking_lot;
extern crate plex;
extern crate rand;
extern crate rand_chacha;
extern crate rdrand;

pub mod ir;
pub mod lang;
//pub mod repl;
pub mod rngs;
pub mod vm;
