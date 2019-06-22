// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};

use rpds::{HashTrieMap};

use std::collections::{HashMap, VecDeque};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LLabel(u64);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LHash(u64);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LVar(u64);

#[derive(Default)]
pub struct LBuilder {
  label_ctr:    u64,
  hash_ctr:     u64,
  var_ctr:      u64,
  name_to_hash: HashMap<String, LHash>,
  hash_to_name: HashMap<LHash, String>,
}

impl LBuilder {
  pub fn fresh_label(&mut self) -> LLabel {
    self.label_ctr += 1;
    assert!(self.label_ctr != 0);
    LLabel(self.label_ctr)
  }

  pub fn fresh_var(&mut self) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    LVar(self.var_ctr)
  }

  pub fn lookup_name(&mut self, name: &str) -> LHash {
    let &mut LBuilder{
      ref mut hash_ctr,
      ref mut name_to_hash,
      ref mut hash_to_name, ..} = self;
    name_to_hash.entry(name.to_owned()).or_insert_with(|| {
      *hash_ctr += 1;
      assert!(*hash_ctr != 0);
      let new_hash = LHash(*hash_ctr);
      hash_to_name.insert(new_hash.clone(), name.to_owned());
      new_hash
    }).clone()
  }

  pub fn compile(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LCode {
    // TODO
    let ltree = self._lower(htree, ctx);
    //let ltree = self._lower_with_toplevel(htree, ctx);
    let ltree = self._normalize(ltree);
    let ltree = self._rederive_ctxs(ltree);
    // TODO: take the final ctxtree and convert it into an end ctx, if possible.
    //unimplemented!();
    LCode{
      tree: ltree,
      ctx:  None,
    }
  }
}

impl LBuilder {
  pub fn _lower_pat_rec(&mut self, htree: Rc<HExpr>, bindings: ()) -> () {
    // TODO
    unimplemented!();
  }

  pub fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_hash(&op_hash) {
      Some(v) => v,
      None => {
        println!("error: unknown var '{}'", op_name);
        self.fresh_var()
      }
    };
    let op_label = self.fresh_label();
    let op_e = LExpr {
      label:    op_label.clone(),
      term:     LTerm::Lookup(op_var)
    };
    let op_ = LRel::new(op_label, pos + 1, pos);
    let mut curr_pos = pos + 2;
    let (arg_label, next_pos) = self._lower_rec(arg, ctx.clone(), stack, curr_pos);
    let arg_ = LRel::new(arg_label, curr_pos, pos);
    curr_pos = next_pos;
    let label = self.fresh_label();
    let e = LExpr{
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![arg_])
    };
    stack.push_front((op_e, ctx.clone(), pos + 1));
    stack.push_front((e, ctx, pos));
    (label, curr_pos)
  }

  pub fn _lower_binop(&mut self, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    //let op_var = ctx.lookup_hash(&op_hash);
    let op_var = match ctx.lookup_hash(&op_hash) {
      Some(v) => v,
      None => {
        println!("error: unknown var '{}'", op_name);
        self.fresh_var()
      }
    };
    let op_label = self.fresh_label();
    let op_e = LExpr {
      label:    op_label.clone(),
      term:     LTerm::Lookup(op_var)
    };
    let op_ = LRel::new(op_label, pos + 1, pos);
    let mut curr_pos = pos + 2;
    let (lhs_label, next_pos) = self._lower_rec(lhs, ctx.clone(), stack, curr_pos);
    let lhs_ = LRel::new(lhs_label, curr_pos, pos);
    curr_pos = next_pos;
    let (rhs_label, next_pos) = self._lower_rec(rhs, ctx.clone(), stack, curr_pos);
    let rhs_ = LRel::new(rhs_label, curr_pos, pos);
    curr_pos = next_pos;
    let label = self.fresh_label();
    let e = LExpr{
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![lhs_, rhs_])
    };
    stack.push_front((op_e, ctx.clone(), pos + 1));
    stack.push_front((e, ctx, pos));
    (label, curr_pos)
  }

  pub fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, /*ltree: &mut LTree, ctxtree: &mut LCtxTree,*/ pos: usize) -> (LLabel, usize) {
    // TODO
    match &*htree {
      &HExpr::End => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::End
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Lambda(ref params, ref body) => {
        let mut param_vars = Vec::with_capacity(params.len());
        let mut body_ctx = ctx.clone();
        for p in params.iter() {
          let p_name = match &**p {
            &HExpr::Ident(ref p_name) => p_name,
            _ => panic!(),
          };
          let p_hash = self.lookup_name(p_name);
          let p_var = self.fresh_var();
          body_ctx.bind_mut(p_hash, p_var.clone());
          param_vars.push(p_var);
        }
        let body_pos = pos + 1;
        let (body_label, next_pos) = self._lower_rec(body.clone(), body_ctx, stack, body_pos);
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::Lambda(param_vars, LRel::new(body_label, body_pos, pos))
        };
        stack.push_front((e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::Apply(ref head, ref args) => {
        let mut curr_pos = pos + 1;
        let (head_label, next_pos) = self._lower_rec(head.clone(), ctx.clone(), stack, curr_pos);
        let head_ = LRel::new(head_label, curr_pos, pos);
        curr_pos = next_pos;
        let mut args_: Vec<_> = Vec::with_capacity(args.len());
        for arg in args.iter() {
          let (arg_label, next_pos) = self._lower_rec(arg.clone(), ctx.clone(), stack, curr_pos);
          args_.push(LRel::new(arg_label, curr_pos, pos));
          curr_pos = next_pos;
        }
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::Apply(head_, args_)
        };
        stack.push_front((e, ctx, pos));
        (label, curr_pos)
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        let mut rest_ctx = ctx.clone();
        let name = match &**lhs {
          &HExpr::Ident(ref name) => name,
          _ => unimplemented!(),
        };
        let n_hash = self.lookup_name(name);
        let n_var = self.fresh_var();
        rest_ctx.bind_mut(n_hash, n_var.clone());
        let body_pos = pos + 1;
        let (body_label, next_pos) = self._lower_rec(body.clone(), ctx.clone(), stack, body_pos);
        let body_ = LRel::new(body_label, body_pos, pos);
        let rest_pos = next_pos;
        let (rest_label, next_pos) = self._lower_rec(rest.clone(), rest_ctx, stack, rest_pos);
        let rest_ = LRel::new(rest_label, rest_pos, pos);
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::Let(n_var, body_, rest_)
        };
        stack.push_front((e, ctx, pos));
        (label, next_pos)
      }
      /*&HExpr::LetFun(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        // FIXME
        unimplemented!();
      }*/
      &HExpr::LetMatch(ref lhs, ref body, ref rest) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::Switch(ref pred, ref top, ref bot) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::Match(ref query, ref pat_arms) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::NilSTupLit => {
        // FIXME
        unimplemented!();
      }
      &HExpr::STuple(ref elems) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::NilTupLit => {
        // FIXME
        unimplemented!();
      }
      &HExpr::Tuple(ref elems) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::BotLit => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::BitLit(false)
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::TeeLit => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::BitLit(true)
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::IntLit(x) => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::IntLit(x)
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::FloLit(x) => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::FloLit(x)
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.lookup_name(name);
        let name_var = ctx.lookup_hash(&name_hash);
        let name_var = match ctx.lookup_hash(&name_hash) {
          Some(v) => v,
          None => {
            println!("error: unknown var '{}'", name);
            self.fresh_var()
          }
        };
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::Lookup(name_var)
        };
        stack.push_front((e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::PathLookup(ref lhs, ref rhs_name) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::PathIndex(ref lhs, ref rhs_idx) => {
        // FIXME
        unimplemented!();
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        self._lower_binop("add", lhs.clone(), rhs.clone(), ctx, stack, pos)
      }
      &HExpr::Mul(ref lhs, ref rhs) => {
        self._lower_binop("mul", lhs.clone(), rhs.clone(), ctx, stack, pos)
      }
      &HExpr::Neg(ref rhs) => {
        self._lower_unop("neg", rhs.clone(), ctx, stack, pos)
      }
      &HExpr::Sub(ref lhs, ref rhs) => {
        self._lower_binop("sub", lhs.clone(), rhs.clone(), ctx, stack, pos)
      }
      &HExpr::Div(ref lhs, ref rhs) => {
        self._lower_binop("div", lhs.clone(), rhs.clone(), ctx, stack, pos)
      }
      &HExpr::Eq(ref lhs, ref rhs) => {
        self._lower_binop("eq", lhs.clone(), rhs.clone(), ctx, stack, pos)
      }
      _ => {
        unimplemented!();
      }
    }
  }

  pub fn _lower_with_toplevel(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LTree {
    // FIXME
    unimplemented!();
  }

  pub fn _lower(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LTree {
    let mut stack = VecDeque::new();
    // FIXME
    self._lower_rec(htree, ctx, &mut stack, /*&mut queue,*/ 0);
    let mut cache = HashMap::new();
    let mut ltree = LTree::default();
    loop {
      match stack.pop_front() {
        None => break,
        Some((e, ctx, pos)) => {
          let q = ltree.exps.len();
          if q == pos {
            ltree.exps.push(e);
            ltree.ctxs.push(ctx);
          } else {
            if cache.contains_key(&q) {
              let (e, ctx) = cache.remove(&q).unwrap();
              ltree.exps.push(e);
              ltree.ctxs.push(ctx);
            }
            cache.insert(pos, (e, ctx));
          }
        }
      }
    }
    while !cache.is_empty() {
      let q = ltree.exps.len();
      if cache.contains_key(&q) {
        let (e, ctx) = cache.remove(&q).unwrap();
        ltree.exps.push(e);
        ltree.ctxs.push(ctx);
      } else {
        // FIXME: better error handling!
        panic!();
      }
    }
    ltree
  }
}

impl LBuilder {
  pub fn _rederive_ctxs(&mut self, ltree: LTree) -> LTree {
    // FIXME
    //unimplemented!();
    ltree
  }
}

impl LBuilder {
  pub fn _normalize(&mut self, ltree: LTree) -> LTree {
    // FIXME
    //unimplemented!();
    ltree
  }
}

pub struct LCode {
  pub tree: LTree,
  pub ctx:  Option<LCtxRef>,
}

#[derive(Clone)]
pub enum LCtxBinder {
  Fresh,
  Hash(LHash),
}

#[derive(Clone, Default)]
pub struct LCtxRef {
  hash_to_var:  HashTrieMap<LHash, LVar>,
  var_to_bind:  HashTrieMap<LVar, LCtxBinder>,
}

impl LCtxRef {
  pub fn lookup_hash(&self, hash: &LHash) -> Option<LVar> {
    match self.hash_to_var.get(hash) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  pub fn bind_mut(&mut self, hash: LHash, var: LVar) {
    self.hash_to_var.insert_mut(hash.clone(), var.clone());
    self.var_to_bind.insert_mut(var, LCtxBinder::Hash(hash));
  }
}

#[derive(Clone, Default)]
pub struct LTyctxRef {
}

pub enum LTy {
}

/*#[derive(Default)]
pub struct LTyTree {
  pub tys:      Vec<LTy>,
}*/

#[derive(Default)]
pub struct LTree {
  pub mlib:     Vec<LMExpr>,
  pub exps:     Vec<LExpr>,
  pub ctxs:     Vec<LCtxRef>,
  //pub tctxs:    Vec<LTyctxRef>,
}

pub struct LRel {
  pub label:    LLabel,
  pub offset:   usize,
}

impl LRel {
  pub fn new(label: LLabel, pos: usize, this_pos: usize) -> LRel {
    assert!(pos > this_pos);
    LRel{
      label,
      offset:   pos - this_pos,
    }
  }
}

pub struct LMIdx {
  pub label:    LLabel,
  pub index:    usize,
}

pub struct LExpr {
  // TODO
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Debug)]
pub enum LPat {
  Cons(LPatRef, LPatRef),
  Concat(LPatRef, LPatRef),
  STuple(Vec<LPatRef>),
  Tuple(Vec<LPatRef>),
  BitLit(bool),
  IntLit(i64),
  Place,
  Var(LVar),
  Alias(LPatRef, LVar),
}

#[derive(Debug)]
pub struct LPatRef {
  inner:    Rc<LPat>,
}

impl LPatRef {
  pub fn new(pat: LPat) -> LPatRef {
    LPatRef{inner: Rc::new(pat)}
  }
}

impl Clone for LPatRef {
  fn clone(&self) -> LPatRef {
    LPatRef{inner: self.inner.clone()}
  }
}

impl Deref for LPatRef {
  type Target = LPat;

  fn deref(&self) -> &LPat {
    &*self.inner
  }
}

pub enum LTerm<E=LRel> {
  End,
  Module(Vec<E>, E),
  Break(E),
  Apply(E, Vec<E>),
  Lambda(Vec<LVar>, E),
  D(E),
  //DAdj(E),
  //DTng(E),
  Adj(E),
  //Tng(E),
  Let(LVar, E, E),
  Fix(LVar, E),
  Match(E, Vec<(LPat, E)>),
  Cons(E, E),
  Concat(E, E),
  STuple(Vec<E>),
  Tuple(Vec<E>),
  BitLit(bool),
  IntLit(i64),
  FloLit(f64),
  Lookup(LVar),
  Reclaim(LVar, E),
  MExt(LMIdx),
}

pub struct LMExpr {
  pub label:    LLabel,
  pub mterm:    LMTerm,
}

pub enum LMTerm {
  Deref,
  BLambda,
  //CLambda,
}
