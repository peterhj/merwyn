// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rand::prelude::*;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use rdrand::{RdRand};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub type HwRngImpl = RdRand;

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
