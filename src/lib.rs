// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(non_ascii_idents)]
#![feature(proc_macro_hygiene)]
#![feature(ptr_offset_from)]

extern crate byteorder;
//extern crate envy;
//extern crate fixedbitset;
//extern crate lazycell;
//#[macro_use] extern crate lazy_static;
extern crate libc;
//extern crate parking_lot;
extern crate plex;
extern crate rand_core;
//extern crate rearray;
extern crate rpds;
extern crate serde;
#[macro_use] extern crate serde_derive;
extern crate termion;

pub mod build;
pub mod builtins;
pub mod cffi;
pub mod cfg;
pub mod coll;
pub mod ir2;
pub mod lang;
pub mod mach;
pub mod mach_io;
pub mod num_util;
pub mod repl;
pub mod rngs;
