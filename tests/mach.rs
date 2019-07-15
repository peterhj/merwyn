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
