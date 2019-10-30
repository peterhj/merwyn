//extern crate byteorder;
extern crate merwyn;
extern crate rand_core;

use merwyn::io_util::{WriteBytesExt, LE};
use merwyn::rngs::{ChaCha20State};
use rand_core::block::{BlockRngCore};

use std::io::{Cursor};

/// https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04#section-2.1.1
#[test]
fn test_chacha20_ietf_test_vector_2_1_1() {
  let mut a: u32 = 0x11111111;
  let mut b: u32 = 0x01020304;
  let mut c: u32 = 0x9b8d6f43;
  let mut d: u32 = 0x01234567;
  ChaCha20State::_quarter_round(&mut a, &mut b, &mut c, &mut d);
  assert_eq!(a, 0xea2a92f4);
  assert_eq!(b, 0xcb1cf8ce);
  assert_eq!(c, 0x4581472e);
  assert_eq!(d, 0x5881c4bb);
}

/// https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04#section-2.3.1
#[test]
fn test_chacha20_ietf_test_vector_2_3_1() {
  let mut constant_buf: [u8; 16] = [0; 16];
  {
    let mut constant_writer = Cursor::new(&mut constant_buf as &mut [_]);
    constant_writer.write_u32::<LE>(0x61707865).unwrap();
    constant_writer.write_u32::<LE>(0x3320646e).unwrap();
    constant_writer.write_u32::<LE>(0x79622d32).unwrap();
    constant_writer.write_u32::<LE>(0x6b206574).unwrap();
  }
  let counter = 0x0900_0000_0000_0001;
  let nonce = 0x0000_0000_4a00_0000;
  let key_buf: &[u8; 32] = b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f";
  let mut state = ChaCha20State::zeroed();
  assert!(state.initialize(
      Some(&constant_buf),
      counter,
      nonce,
      &mut Cursor::new(&key_buf),
  ).is_ok());
  let mut output: [u32; 16] = [0; 16];
  state.generate(&mut output);
  let mut output_buf: [u8; 64] = [0; 64];
  {
    let mut output_writer = Cursor::new(&mut output_buf as &mut [_]);
    for &u in output.iter() {
      output_writer.write_u32::<LE>(u).unwrap();
    }
  }
  assert_eq!(&output_buf[ 0 ..  8], b"\x10\xf1\xe7\xe4\xd1\x3b\x59\x15");
  assert_eq!(&output_buf[ 8 .. 16], b"\x50\x0f\xdd\x1f\xa3\x20\x71\xc4");
  assert_eq!(&output_buf[16 .. 24], b"\xc7\xd1\xf4\xc7\x33\xc0\x68\x03");
  assert_eq!(&output_buf[24 .. 32], b"\x04\x22\xaa\x9a\xc3\xd4\x6c\x4e");
  assert_eq!(&output_buf[32 .. 40], b"\xd2\x82\x64\x46\x07\x9f\xaa\x09");
  assert_eq!(&output_buf[40 .. 48], b"\x14\xc2\xd7\x05\xd9\x8b\x02\xa2");
  assert_eq!(&output_buf[48 .. 56], b"\xb5\x12\x9c\xd1\xde\x16\x4e\xb9");
  assert_eq!(&output_buf[56 .. 64], b"\xcb\xd0\x83\xe8\xa2\x50\x3c\x4e");
}
