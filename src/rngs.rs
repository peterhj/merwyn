// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use byteorder::{ReadBytesExt, WriteBytesExt, LE};
use rand_core::{RngCore, Error as RandError};
use rand_core::block::{BlockRngCore, BlockRng, BlockRng64};

use std::io::{Read, Write, Error as IoError, Cursor};

#[derive(Clone, Copy)]
pub struct ChaCha20State {
  state:    [u32; 16],
}

impl ChaCha20State {
  pub fn zeroed() -> ChaCha20State {
    ChaCha20State{
      state:    [0; 16],
    }
  }

  pub fn initialize<R: Read>(&mut self, constant: Option<&[u8; 16]>, counter: u64, nonce: u64, key: &mut R) -> Result<(), IoError> {
    assert!(counter != 0);
    let mut constant = Cursor::new(match constant {
      None => b"Reproducibility!",
      Some(c) => c,
    });
    self.state[0]  = constant.read_u32::<LE>()?;
    self.state[1]  = constant.read_u32::<LE>()?;
    self.state[2]  = constant.read_u32::<LE>()?;
    self.state[3]  = constant.read_u32::<LE>()?;
    self.state[4]  = key.read_u32::<LE>()?;
    self.state[5]  = key.read_u32::<LE>()?;
    self.state[6]  = key.read_u32::<LE>()?;
    self.state[7]  = key.read_u32::<LE>()?;
    self.state[8]  = key.read_u32::<LE>()?;
    self.state[9]  = key.read_u32::<LE>()?;
    self.state[10] = key.read_u32::<LE>()?;
    self.state[11] = key.read_u32::<LE>()?;
    self.state[12] = (counter & 0xffff_ffff_u64) as u32;
    self.state[13] = ((counter >> 32) & 0xffff_ffff_u64) as u32;
    self.state[14] = (nonce & 0xffff_ffff_u64) as u32;
    self.state[15] = ((nonce >> 32) & 0xffff_ffff_u64) as u32;
    Ok(())
  }

  pub fn restore<R: Read>(&mut self, buf: &mut R) -> Result<usize, IoError> {
    self.state[0]  = buf.read_u32::<LE>()?;
    self.state[1]  = buf.read_u32::<LE>()?;
    self.state[2]  = buf.read_u32::<LE>()?;
    self.state[3]  = buf.read_u32::<LE>()?;
    self.state[4]  = buf.read_u32::<LE>()?;
    self.state[5]  = buf.read_u32::<LE>()?;
    self.state[6]  = buf.read_u32::<LE>()?;
    self.state[7]  = buf.read_u32::<LE>()?;
    self.state[8]  = buf.read_u32::<LE>()?;
    self.state[9]  = buf.read_u32::<LE>()?;
    self.state[10] = buf.read_u32::<LE>()?;
    self.state[11] = buf.read_u32::<LE>()?;
    self.state[12] = buf.read_u32::<LE>()?;
    self.state[13] = buf.read_u32::<LE>()?;
    self.state[14] = buf.read_u32::<LE>()?;
    self.state[15] = buf.read_u32::<LE>()?;
    Ok(64)
  }

  pub fn save<W: Write>(&self, buf: &mut W) -> Result<usize, IoError> {
    buf.write_u32::<LE>(self.state[0])?;
    buf.write_u32::<LE>(self.state[1])?;
    buf.write_u32::<LE>(self.state[2])?;
    buf.write_u32::<LE>(self.state[3])?;
    buf.write_u32::<LE>(self.state[4])?;
    buf.write_u32::<LE>(self.state[5])?;
    buf.write_u32::<LE>(self.state[6])?;
    buf.write_u32::<LE>(self.state[7])?;
    buf.write_u32::<LE>(self.state[8])?;
    buf.write_u32::<LE>(self.state[9])?;
    buf.write_u32::<LE>(self.state[10])?;
    buf.write_u32::<LE>(self.state[11])?;
    buf.write_u32::<LE>(self.state[12])?;
    buf.write_u32::<LE>(self.state[13])?;
    buf.write_u32::<LE>(self.state[14])?;
    buf.write_u32::<LE>(self.state[15])?;
    Ok(64)
  }
}

impl ChaCha20State {
  #[inline]
  pub fn _quarter_round(a: &mut u32, b: &mut u32, c: &mut u32, d: &mut u32) {
    *a += *b; *d = (*d ^ *a).rotate_left(16);
    *c += *d; *b = (*b ^ *c).rotate_left(12);
    *a += *b; *d = (*d ^ *a).rotate_left(8);
    *c += *d; *b = (*b ^ *c).rotate_left(7);
  }
}

impl BlockRngCore for ChaCha20State {
  type Item = u32;
  type Results = [u32; 16];

  #[inline]
  fn generate(&mut self, results: &mut [u32; 16]) {
    unsafe {
      let mut x0 = *self.state.get_unchecked(0);
      let mut x1 = *self.state.get_unchecked(1);
      let mut x2 = *self.state.get_unchecked(2);
      let mut x3 = *self.state.get_unchecked(3);
      let mut x4 = *self.state.get_unchecked(4);
      let mut x5 = *self.state.get_unchecked(5);
      let mut x6 = *self.state.get_unchecked(6);
      let mut x7 = *self.state.get_unchecked(7);
      let mut x8 = *self.state.get_unchecked(8);
      let mut x9 = *self.state.get_unchecked(9);
      let mut x10 = *self.state.get_unchecked(10);
      let mut x11 = *self.state.get_unchecked(11);
      let mut x12 = *self.state.get_unchecked(12);
      let mut x13 = *self.state.get_unchecked(13);
      let mut x14 = *self.state.get_unchecked(14);
      let mut x15 = *self.state.get_unchecked(15);
      let mut counter = (x12 as u64) | ((x13 as u64) << 32);
      assert!(counter != 0);
      for _ in 0 .. 10 {
        ChaCha20State::_quarter_round(&mut x0, &mut x4, &mut x8, &mut x12);
        ChaCha20State::_quarter_round(&mut x1, &mut x5, &mut x9, &mut x13);
        ChaCha20State::_quarter_round(&mut x2, &mut x6, &mut x10, &mut x14);
        ChaCha20State::_quarter_round(&mut x3, &mut x7, &mut x11, &mut x15);
        ChaCha20State::_quarter_round(&mut x0, &mut x5, &mut x10, &mut x15);
        ChaCha20State::_quarter_round(&mut x1, &mut x6, &mut x11, &mut x12);
        ChaCha20State::_quarter_round(&mut x2, &mut x7, &mut x8, &mut x13);
        ChaCha20State::_quarter_round(&mut x3, &mut x4, &mut x9, &mut x14);
      }
      x0 += *self.state.get_unchecked(0);
      x1 += *self.state.get_unchecked(1);
      x2 += *self.state.get_unchecked(2);
      x3 += *self.state.get_unchecked(3);
      x4 += *self.state.get_unchecked(4);
      x5 += *self.state.get_unchecked(5);
      x6 += *self.state.get_unchecked(6);
      x7 += *self.state.get_unchecked(7);
      x8 += *self.state.get_unchecked(8);
      x9 += *self.state.get_unchecked(9);
      x10 += *self.state.get_unchecked(10);
      x11 += *self.state.get_unchecked(11);
      x12 += *self.state.get_unchecked(12);
      x13 += *self.state.get_unchecked(13);
      x14 += *self.state.get_unchecked(14);
      x15 += *self.state.get_unchecked(15);
      counter += 1;
      *self.state.get_unchecked_mut(12) = (counter & 0xffff_ffff_u64) as u32;
      *self.state.get_unchecked_mut(13) = ((counter >> 32) & 0xffff_ffff_u64) as u32;
      *results.get_unchecked_mut(0) = x0;
      *results.get_unchecked_mut(1) = x1;
      *results.get_unchecked_mut(2) = x2;
      *results.get_unchecked_mut(3) = x3;
      *results.get_unchecked_mut(4) = x4;
      *results.get_unchecked_mut(5) = x5;
      *results.get_unchecked_mut(6) = x6;
      *results.get_unchecked_mut(7) = x7;
      *results.get_unchecked_mut(8) = x8;
      *results.get_unchecked_mut(9) = x9;
      *results.get_unchecked_mut(10) = x10;
      *results.get_unchecked_mut(11) = x11;
      *results.get_unchecked_mut(12) = x12;
      *results.get_unchecked_mut(13) = x13;
      *results.get_unchecked_mut(14) = x14;
      *results.get_unchecked_mut(15) = x15;
    }
  }
}

#[derive(Clone)]
pub struct ChaCha20Rng {
  rng:  BlockRng<ChaCha20State>,
}

impl ChaCha20Rng {
  pub fn zeroed() -> ChaCha20Rng {
    ChaCha20Rng{
      rng:  BlockRng::new(ChaCha20State::zeroed()),
    }
  }

  pub fn state(&self) -> &ChaCha20State {
    &self.rng.core
  }

  pub fn state_mut(&mut self) -> &mut ChaCha20State {
    &mut self.rng.core
  }
}

impl RngCore for ChaCha20Rng {
  #[inline]
  fn next_u32(&mut self) -> u32 {
    self.rng.next_u32()
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    self.rng.next_u64()
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.rng.fill_bytes(dst);
  }

  #[inline]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RandError> {
    self.rng.try_fill_bytes(dst)
  }
}

#[derive(Clone, Copy)]
pub struct Xoshirostarstar256State {
  state: [u64; 4],
}

impl Xoshirostarstar256State {
  pub fn zeroed() -> Xoshirostarstar256State {
    Xoshirostarstar256State{
      state:    [0; 4],
    }
  }

  pub fn save<W: Write>(&self, buf: &mut W) -> Result<usize, IoError> {
    buf.write_u64::<LE>(self.state[0])?;
    buf.write_u64::<LE>(self.state[1])?;
    buf.write_u64::<LE>(self.state[2])?;
    buf.write_u64::<LE>(self.state[3])?;
    Ok(32)
  }

  pub fn restore<R: Read>(&mut self, buf: &mut R) -> Result<usize, IoError> {
    self.state[0] = buf.read_u64::<LE>()?;
    self.state[1] = buf.read_u64::<LE>()?;
    self.state[2] = buf.read_u64::<LE>()?;
    self.state[3] = buf.read_u64::<LE>()?;
    Ok(32)
  }

  pub fn validate(&self) -> bool {
    !(self.state[0] == 0
        && self.state[1] == 0
        && self.state[2] == 0
        && self.state[3] == 0)
  }
}

impl BlockRngCore for Xoshirostarstar256State {
  type Item = u64;
  type Results = [u64; 1];

  #[inline]
  fn generate(&mut self, results: &mut [u64; 1]) {
    unsafe {
      *results.get_unchecked_mut(0) = (*self.state.get_unchecked(1) * 5).rotate_left(7) * 9;
      let t = *self.state.get_unchecked(1) << 17;
      *self.state.get_unchecked_mut(2) ^= *self.state.get_unchecked(0);
      *self.state.get_unchecked_mut(3) ^= *self.state.get_unchecked(1);
      *self.state.get_unchecked_mut(1) ^= *self.state.get_unchecked(2);
      *self.state.get_unchecked_mut(0) ^= *self.state.get_unchecked(3);
      *self.state.get_unchecked_mut(2) ^= t;
      *self.state.get_unchecked_mut(3) = (*self.state.get_unchecked(3)).rotate_left(45);
    }
  }
}

#[derive(Clone)]
pub struct Xoshirostarstar256Rng {
  rng:  BlockRng64<Xoshirostarstar256State>,
}

impl Xoshirostarstar256Rng {
  pub fn zeroed() -> Xoshirostarstar256Rng {
    Xoshirostarstar256Rng{
      rng:  BlockRng64::new(Xoshirostarstar256State::zeroed()),
    }
  }

  pub fn state(&self) -> &Xoshirostarstar256State {
    &self.rng.core
  }

  pub fn state_mut(&mut self) -> &mut Xoshirostarstar256State {
    &mut self.rng.core
  }
}

impl RngCore for Xoshirostarstar256Rng {
  #[inline]
  fn next_u32(&mut self) -> u32 {
    self.rng.next_u32()
  }

  #[inline]
  fn next_u64(&mut self) -> u64 {
    self.rng.next_u64()
  }

  #[inline]
  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.rng.fill_bytes(dst);
  }

  #[inline]
  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), RandError> {
    self.rng.try_fill_bytes(dst)
  }
}
