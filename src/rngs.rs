// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rand::prelude::*;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use rdrand::{RdRand};

use std::num::{Wrapping};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
type HwRngImpl = RdRand;

pub struct HwRng {
  inner:    HwRngImpl,
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
impl Default for HwRng {
  fn default() -> HwRng {
    let inner = match RdRand::new() {
      Err(_) => panic!("failed to initialize rdrand-based rng"),
      Ok(rng) => rng,
    };
    HwRng{inner}
  }
}

impl RngCore for HwRng where HwRngImpl: RngCore {
  fn next_u32(&mut self) -> u32 {
    self.inner.next_u32()
  }

  fn next_u64(&mut self) -> u64 {
    self.inner.next_u64()
  }

  fn fill_bytes(&mut self, dst: &mut [u8]) {
    self.inner.fill_bytes(dst)
  }

  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), rand::Error> {
    self.inner.try_fill_bytes(dst)
  }
}

#[derive(Clone)]
pub struct Xorshiftplus128Rng {
  state: [u64; 2],
}

impl Xorshiftplus128Rng {
  pub fn fill_state(&self, state_buf: &mut [u64]) {
    state_buf[ .. 2].copy_from_slice(&self.state);
  }

  pub fn set_state(&mut self, state_buf: &[u64]) {
    self.state.copy_from_slice(&state_buf[ .. 2]);
  }
}

impl RngCore for Xorshiftplus128Rng {
  fn next_u32(&mut self) -> u32 {
    (self.next_u64() >> 32) as u32
  }

  fn next_u64(&mut self) -> u64 {
    let mut s1 = unsafe { *self.state.get_unchecked(0) };
    let s0 = unsafe { *self.state.get_unchecked(1) };
    s1 ^= s1 << 23;
    s1 = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    unsafe { *self.state.get_unchecked_mut(0) = s0 };
    unsafe { *self.state.get_unchecked_mut(1) = s1 };
    (Wrapping(s1) + Wrapping(s0)).0
  }

  fn fill_bytes(&mut self, dst: &mut [u8]) {
    // TODO
    unimplemented!();
  }

  fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), rand::Error> {
    // TODO
    unimplemented!();
  }
}
