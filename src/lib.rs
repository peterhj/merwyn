// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(non_ascii_idents)]
#![feature(proc_macro_hygiene)]

extern crate envy;
extern crate fixedbitset;
//#[macro_use] extern crate lazy_static;
//extern crate parking_lot;
extern crate plex;
extern crate rand;
extern crate rand_chacha;
extern crate rdrand;
extern crate serde;
#[macro_use] extern crate serde_derive;
extern crate vertreap;

pub mod cfg;
pub mod ir;
pub mod lang;
//pub mod repl;
pub mod rngs;
pub mod stdlib;
pub mod vm;
