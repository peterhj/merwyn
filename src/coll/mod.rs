// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use self::hashtreap::{
  HashTreapMap, HashTreapSet,
  InlineHashTreapMap, InlineHashTreapSet,
};
/*pub use self::rbtree_util::{
  DebugRBTreeMap, DebugRBTreeSet,
};*/

/*use rpds::{
  HashTrieMap, HashTrieSet,
  RedBlackTreeMap, RedBlackTreeSet,
};*/

pub mod hashtreap;
/*pub mod rbtree_util;*/

pub type HTreapMap<K, V> = HashTreapMap<K, V>;
pub type HTreapSet<K> = HashTreapSet<K>;

pub type IHTreapMap<K, V> = InlineHashTreapMap<K, V>;
pub type IHTreapSet<K> = InlineHashTreapSet<K>;

/*pub type HTrieMap<K, V> = HashTrieMap<K, V>;
pub type HTrieSet<K> = HashTrieSet<K>;

pub type RBTreeMap<K, V> = RedBlackTreeMap<K, V>;
pub type RBTreeSet<K> = RedBlackTreeSet<K>;*/
