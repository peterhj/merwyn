// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{RBTreeMap, RBTreeSet};

use std::fmt::{Debug as FmtDebug, Error as FmtError, Formatter};
use std::ops::{Deref};

#[derive(Clone, Default)]
pub struct DebugRBTreeMap<K: Ord, V>(RBTreeMap<K, V>);

impl<K: Ord, V> From<RBTreeMap<K, V>> for DebugRBTreeMap<K, V> {
  fn from(inner: RBTreeMap<K, V>) -> DebugRBTreeMap<K, V> {
    DebugRBTreeMap(inner)
  }
}

impl<K: Ord, V> Deref for DebugRBTreeMap<K, V> {
  type Target = RBTreeMap<K, V>;

  fn deref(&self) -> &RBTreeMap<K, V> {
    &self.0
  }
}

impl<K: Ord + FmtDebug, V: FmtDebug> FmtDebug for DebugRBTreeMap<K, V> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    write!(f, "{{")?;
    for (i, (k, v)) in self.0.iter().enumerate() {
      k.fmt(f)?;
      write!(f, " => ")?;
      v.fmt(f)?;
      if i != self.0.size() - 1 {
        write!(f, ", ")?;
      }
    }
    write!(f, "}}")?;
    Ok(())
  }
}

#[derive(Clone, Default)]
pub struct DebugRBTreeSet<K: Ord>(RBTreeSet<K>);

impl<K: Ord> From<RBTreeSet<K>> for DebugRBTreeSet<K> {
  fn from(inner: RBTreeSet<K>) -> DebugRBTreeSet<K> {
    DebugRBTreeSet(inner)
  }
}

impl<K: Ord> Deref for DebugRBTreeSet<K> {
  type Target = RBTreeSet<K>;

  fn deref(&self) -> &RBTreeSet<K> {
    &self.0
  }
}

impl<K: Ord + FmtDebug> FmtDebug for DebugRBTreeSet<K> {
  fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
    write!(f, "{{")?;
    for (i, k) in self.0.iter().enumerate() {
      k.fmt(f)?;
      if i != self.0.size() - 1 {
        write!(f, ", ")?;
      }
    }
    write!(f, "}}")?;
    Ok(())
  }
}
