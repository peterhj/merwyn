// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate merwyn;

use merwyn::mach_io::{MachIOState, IOEntropyStream, IOEntropyReplay};

use std::io::{Read};

#[test]
fn test_mach_io_entropy() {
  println!();
  let mut buf: [u8; 16] = [0; 16];
  let mut state = MachIOState::new();
  {
    let mut entropy = IOEntropyStream::open(&mut state);
    entropy.read(&mut buf).unwrap();
    println!("DEBUG: (fresh)  entropy bytes: {:?}", buf);
    entropy.read(&mut buf).unwrap();
    println!("DEBUG: (fresh)  entropy bytes: {:?}", buf);
  }
  //println!("DEBUG: replay: {:?}", state._replay());
  {
    let mut entropy = IOEntropyReplay::open(&mut state);
    entropy.read(&mut buf).unwrap();
    println!("DEBUG: (replay) entropy bytes: {:?}", buf);
    entropy.read(&mut buf).unwrap();
    println!("DEBUG: (replay) entropy bytes: {:?}", buf);
  }
}
