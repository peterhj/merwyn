// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::ops::{Add, Sub, Mul, Div, Rem, Neg};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct Checked<T>(T);

pub fn checked<T>(val: T) -> Checked<T> where Checked<T>: From<T> {
  Checked::from(val)
}

impl From<i64> for Checked<i64> {
  fn from(val: i64) -> Checked<i64> {
    Checked(val)
  }
}

impl Into<i64> for Checked<i64> {
  fn into(self) -> i64 {
    self.0
  }
}

impl Add for Checked<i64> {
  type Output = Checked<i64>;

  fn add(self, rhs: Checked<i64>) -> Checked<i64> {
    match self.0.checked_add(rhs.0) {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}

impl Sub for Checked<i64> {
  type Output = Checked<i64>;

  fn sub(self, rhs: Checked<i64>) -> Checked<i64> {
    match self.0.checked_sub(rhs.0) {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}

impl Mul for Checked<i64> {
  type Output = Checked<i64>;

  fn mul(self, rhs: Checked<i64>) -> Checked<i64> {
    match self.0.checked_mul(rhs.0) {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}

impl Div for Checked<i64> {
  type Output = Checked<i64>;

  fn div(self, rhs: Checked<i64>) -> Checked<i64> {
    match self.0.checked_div(rhs.0) {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}

impl Rem for Checked<i64> {
  type Output = Checked<i64>;

  fn rem(self, rhs: Checked<i64>) -> Checked<i64> {
    match self.0.checked_rem(rhs.0) {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}

impl Neg for Checked<i64> {
  type Output = Checked<i64>;

  fn neg(self) -> Checked<i64> {
    match self.0.checked_neg() {
      None => panic!(),
      Some(x) => Checked(x)
    }
  }
}
