// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use self::hashtreap::{
  HashTreapMap, HashTreapSet,
  InlineHashTreapMap, InlineHashTreapSet,
};

use rpds::{
  HashTrieMap, HashTrieSet,
  RedBlackTreeMap,
};

use std::fmt::{Debug as FmtDebug, Error as FmtError, Formatter};
use std::ops::{Deref};

pub mod hashtreap;

pub type HTreapMap<K, V> = HashTreapMap<K, V>;
pub type HTreapSet<K> = HashTreapSet<K>;

pub type IHTreapMap<K, V> = InlineHashTreapMap<K, V>;
pub type IHTreapSet<K> = InlineHashTreapSet<K>;

pub type HTrieMap<K, V> = HashTrieMap<K, V>;
pub type HTrieSet<K> = HashTrieSet<K>;

pub type RBTreeMap<K, V> = RedBlackTreeMap<K, V>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
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

impl<K: FmtDebug + Ord, V: FmtDebug> FmtDebug for DebugRBTreeMap<K, V> {
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
