// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::borrow::{Borrow};
use std::cmp::{Ordering};
use std::collections::hash_map::{RandomState};
//use std::fmt::{Debug, Error as FmtError, Formatter};
use std::hash::{BuildHasher, Hasher, Hash};
use std::marker::{PhantomData};
use std::mem::{swap};
use std::ops::{Deref};
use std::rc::{Rc};

thread_local! {
  static TL_GEN: RandomState = RandomState::new();
}

#[derive(Clone, Hash)]
pub struct HashTreapMap<K, V> {
  root: HTNodeRef<K, RecordRef<K, V>>,
}

impl<K, V> Default for HashTreapMap<K, V> {
  fn default() -> HashTreapMap<K, V> {
    HashTreapMap{
      root: None,
    }
  }
}

impl<K, V> HashTreapMap<K, V> {
  pub fn new() -> HashTreapMap<K, V> {
    HashTreapMap::default()
  }
}

impl<K: Ord + Hash, V> HashTreapMap<K, V> {
  pub fn insert(&self, key: K, value: V) -> HashTreapMap<K, V> {
    let data = Record{key, value}.into();
    let (new_root, _) = HTNode::insert(self.root.clone(), data);
    HashTreapMap{root: Some(new_root.into())}
  }

  pub fn insert_mut(&mut self, key: K, value: V) {
    let data = Record{key, value}.into();
    let (new_root, _) = HTNode::insert(self.root.take(), data);
    self.root = Some(new_root.into());
  }
}

impl<K: Ord, V> HashTreapMap<K, V> {
  pub fn get(&self, key: &K) -> Option<&V> {
    match self.root.as_ref() {
      None => None,
      Some(root) => HTNode::search(root, key).map(|data| &(**data).value)
    }
  }

  pub fn contains_key(&self, key: &K) -> bool {
    match self.root.as_ref() {
      None => false,
      Some(root) => HTNode::search(root, key).is_some()
    }
  }

  pub fn remove(&self, key: &K) -> HashTreapMap<K, V> {
    let (new_root, _) = HTNode::remove(self.root.clone(), key);
    HashTreapMap{root: new_root}
  }

  pub fn remove_mut(&mut self, key: &K) {
    let (new_root, _) = HTNode::remove(self.root.take(), key);
    self.root = new_root;
  }
}

#[inline]
fn hash_priority<K: Eq + Hash>(this: &K) -> u64 {
  TL_GEN.with(|gen| {
    let mut state = gen.build_hasher();
    this.hash(&mut state);
    state.finish()
  })
}

#[derive(Hash)]
struct RecordRef<K, V>(Rc<Record<K, V>>);

#[derive(Copy, Hash)]
struct Record<K, V> {
  key:      K,
  value:    V,
}

impl<K, V> From<Record<K, V>> for RecordRef<K, V> {
  #[inline(always)]
  fn from(data: Record<K, V>) -> RecordRef<K, V> {
    RecordRef(Rc::new(data))
  }
}

impl<K, V> Deref for RecordRef<K, V> {
  type Target = Record<K, V>;

  #[inline(always)]
  fn deref(&self) -> &Record<K, V> {
    &*self.0
  }
}

impl<K, V> Clone for RecordRef<K, V> {
  #[inline]
  fn clone(&self) -> RecordRef<K, V> {
    RecordRef(self.0.clone())
  }
}

impl<K: Clone, V: Clone> Clone for Record<K, V> {
  #[inline]
  fn clone(&self) -> Record<K, V> {
    Record{key: self.key.clone(), value: self.value.clone()}
  }
}

impl<K, V> Borrow<K> for RecordRef<K, V> {
  #[inline(always)]
  fn borrow(&self) -> &K {
    &self.0.key
  }
}

impl<K, V> Borrow<K> for Record<K, V> {
  #[inline(always)]
  fn borrow(&self) -> &K {
    &self.key
  }
}

type HTNodeRef<K, Item> = Option<Rc<HTNode<K, Item>>>;

#[derive(Hash)]
struct HTNode<K, Item> {
  lhs:      HTNodeRef<K, Item>,
  rhs:      HTNodeRef<K, Item>,
  priority: u64,
  data:     Item,
  _phantom: PhantomData<K>,
}

impl<K, Item: Clone> Clone for HTNode<K, Item> {
  #[inline]
  fn clone(&self) -> HTNode<K, Item> {
    HTNode{
      lhs:      self.lhs.clone(),
      rhs:      self.rhs.clone(),
      priority: self.priority,
      data:     self.data.clone(),
      _phantom: PhantomData,
    }
  }
}

impl<K: Eq + Hash, Item: Borrow<K>> HTNode<K, Item> {
  #[inline(always)]
  fn new(data: Item) -> HTNode<K, Item> {
    let priority = hash_priority(data.borrow());
    HTNode::new2(data, priority)
  }
}

impl<K, Item> HTNode<K, Item> {
  #[inline(always)]
  fn new2(data: Item, priority: u64) -> HTNode<K, Item> {
    HTNode{lhs: None, rhs: None, priority, data, _phantom: PhantomData}
  }
}

impl<K: Ord, Item: Borrow<K>> HTNode<K, Item> {
  fn search<'r>(root: &'r HTNode<K, Item>, key: &K) -> Option<&'r Item> {
    match key.cmp(root.data.borrow()) {
      Ordering::Less => {
        root.lhs.as_ref().and_then(|lhs| HTNode::search(lhs, key))
      }
      Ordering::Greater => {
        root.rhs.as_ref().and_then(|rhs| HTNode::search(rhs, key))
      }
      Ordering::Equal => {
        Some(&root.data)
      }
    }
  }
}

impl<K, Item: Clone> HTNode<K, Item> {
  fn join(mut lhs: HTNodeRef<K, Item>, mut rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    HTNode::_join(
        //lhs.as_mut().map(|x| Rc::make_mut(x)),
        //rhs.as_mut().map(|x| Rc::make_mut(x))
        lhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone())),
        rhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()))
    //).map(|x| x.clone().into())
    ).map(|x| x.into())
  }

  //fn _join<'r>(lhs: Option<&'r mut HTNode<K, Item>>, rhs: Option<&'r mut HTNode<K, Item>>) -> Option<&'r mut HTNode<K, Item>> {
  fn _join(lhs: Option<HTNode<K, Item>>, rhs: Option<HTNode<K, Item>>) -> Option<HTNode<K, Item>> {
    match (lhs, rhs) {
      (None, None) => None,
      (None, rhs) => rhs,
      (lhs, None) => lhs,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority >= rhs.priority {
          lhs.rhs = HTNode::_join(
              //lhs.rhs.as_mut().map(|x| Rc::make_mut(x)),
              lhs.rhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone())),
              Some(rhs)
          //).map(|x| x.clone().into());
          ).map(|x| x.into());
          Some(lhs)
        } else {
          rhs.lhs = HTNode::_join(
              Some(lhs),
              //rhs.lhs.as_mut().map(|x| Rc::make_mut(x))
              rhs.lhs.map(|x| Rc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()))
          //).map(|x| x.clone().into());
          ).map(|x| x.into());
          Some(rhs)
        }
      }
    }
  }
}

impl<K: Ord + Hash, Item: Clone + Borrow<K>> HTNode<K, Item> {
  fn insert(root: HTNodeRef<K, Item>, mut data: Item) -> (HTNode<K, Item>, Option<Item>) {
    match root {
      None => (HTNode::new(data), None),
      Some(root) => {
        let mut root = match Rc::try_unwrap(root) {
          Ok(r) => r,
          Err(rr) => (*rr).clone(),
        };
        match data.borrow().cmp(root.data.borrow()) {
          Ordering::Less => {
            let (mut new_lhs, old_data) = HTNode::insert(root.lhs, data);
            if new_lhs.priority <= root.priority {
              root.lhs = Some(new_lhs.into());
              (root, old_data)
            } else {
              root.lhs = new_lhs.rhs;
              new_lhs.rhs = Some(root.into());
              (new_lhs, old_data)
            }
          }
          Ordering::Greater => {
            let (mut new_rhs, old_data) = HTNode::insert(root.rhs, data);
            if new_rhs.priority <= root.priority {
              root.rhs = Some(new_rhs.into());
              (root, old_data)
            } else {
              root.rhs = new_rhs.lhs;
              new_rhs.lhs = Some(root.into());
              (new_rhs, old_data)
            }
          }
          Ordering::Equal => {
            swap(&mut root.data, &mut data);
            (root, Some(data))
          }
        }
      }
    }
  }
}

impl<K: Ord, Item: Clone + Borrow<K>> HTNode<K, Item> {
  fn split(root: HTNodeRef<K, Item>, key: &K) -> (HTNodeRef<K, Item>, HTNodeRef<K, Item>, Option<HTNode<K, Item>>) {
    let mut lhs = None;
    let mut rhs = None;
    let query = HTNode::_split(root, &mut lhs, &mut rhs, key);
    (lhs, rhs, query)
  }

  fn _split<'r>(root: HTNodeRef<K, Item>, lhs: &'r mut HTNodeRef<K, Item>, rhs: &'r mut HTNodeRef<K, Item>, key: &K) -> Option<HTNode<K, Item>> {
    match root {
      None => {
        *lhs = None;
        *rhs = None;
        None
      }
      Some(root) => {
        let r = match Rc::try_unwrap(root) {
          Ok(r) => r,
          Err(rr) => (*rr).clone(),
        };
        let mut new_root = HTNode::new2(r.data, r.priority);
        match key.cmp(new_root.data.borrow()) {
          Ordering::Less => {
            let query = HTNode::_split(r.lhs, lhs, &mut new_root.lhs, key);
            *rhs = Some(new_root.into());
            query
          }
          Ordering::Greater => {
            let query = HTNode::_split(r.rhs, &mut new_root.rhs, rhs, key);
            *lhs = Some(new_root.into());
            query
          }
          Ordering::Equal => {
            *lhs = r.lhs;
            *rhs = r.rhs;
            Some(new_root)
          }
        }
      }
    }
  }

  fn remove(root: HTNodeRef<K, Item>, key: &K) -> (HTNodeRef<K, Item>, Option<Item>) {
    let (new_lhs, new_rhs, query) = HTNode::split(root.clone(), key);
    match query {
      None => (root, None),
      Some(query) => {
        (HTNode::join(new_lhs, new_rhs), Some(query.data))
      }
    }
  }

  fn symm_diff(lhs: HTNodeRef<K, Item>, rhs: HTNodeRef<K, Item>) -> HTNodeRef<K, Item> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::symm_diff(lhs.lhs.clone(), lss);
        let new_rhs = HTNode::symm_diff(lhs.rhs.clone(), gtr);
        match query {
          None => {
            let new_root = HTNode{
              lhs:      new_lhs,
              rhs:      new_rhs,
              priority: lhs.priority,
              data:     lhs.data.clone(),
              _phantom: PhantomData,
            };
            Some(new_root.into())
          }
          Some(_) => HTNode::join(new_lhs, new_rhs),
        }
      }
    }
  }
}

impl<K: Clone + Ord, V: Clone> HTNode<K, RecordRef<K, V>> {
  fn intersect_ref<F: FnMut(V, V) -> W, W>(lhs: HTNodeRef<K, RecordRef<K, V>>, rhs: HTNodeRef<K, RecordRef<K, V>>, f: &mut F) -> HTNodeRef<K, RecordRef<K, W>> {
    match (lhs, rhs) {
      (None, None) |
      (None, _) |
      (_, None) => None,
      (Some(mut lhs), Some(mut rhs)) => {
        if lhs.priority < rhs.priority {
          swap(&mut lhs, &mut rhs);
        }
        let (lss, gtr, query) = HTNode::split(Some(rhs), lhs.data.borrow());
        let new_lhs = HTNode::intersect_ref(lhs.lhs.clone(), lss, f);
        let new_rhs = HTNode::intersect_ref(lhs.rhs.clone(), gtr, f);
        match query {
          None => HTNode::join(new_lhs, new_rhs),
          Some(query) => {
            let priority = lhs.priority;
            let key = lhs.data.key.clone();
            let lvalue = lhs.data.value.clone();
            let rvalue = query.data.value.clone();
            let value = (f)(lvalue, rvalue);
            let new_data = Record{key, value};
            let new_root = HTNode{
              lhs:      new_lhs,
              rhs:      new_rhs,
              priority,
              data:     new_data.into(),
              _phantom: PhantomData,
            };
            Some(new_root.into())
          }
        }
      }
    }
  }
}
