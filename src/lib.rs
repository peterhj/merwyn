#![feature(non_ascii_idents)]
#![feature(proc_macro_hygiene)]

extern crate envy;
//#[macro_use] extern crate lazy_static;
//extern crate parking_lot;
extern crate plex;
extern crate rand;
extern crate rand_chacha;
extern crate rdrand;
extern crate serde;
#[macro_use] extern crate serde_derive;

pub mod cfg;
pub mod ir;
pub mod lang;
//pub mod repl;
pub mod rngs;
pub mod vm;
