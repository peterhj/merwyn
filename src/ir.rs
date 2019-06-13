// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::builtins::toplevel_prelude::*;
use crate::lang::{HExpr};
use crate::vm::{VMAddr, VMBoxCode};

use fixedbitset::{FixedBitSet};
use lazycell::{LazyCell};
use serde::{Serialize, Serializer};
//use serde::ser::{SerializeStruct};
//use vertreap::{VertreapMap};

//use std::cell::{RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
//use std::collections::hash_map::{Entry};
use std::fmt::{self, Debug};
use std::io::{Write, stdout};
use std::iter::{FromIterator};
use std::mem::{size_of};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LLDepth(pub usize);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LDBIdx(pub usize);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LVar(pub u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LHash(pub u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LLabel(pub u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LBoxty(pub u64);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LVarSet {
  inner:    FixedBitSet,
}

impl FromIterator<LVar> for LVarSet {
  fn from_iter<I: IntoIterator<Item=LVar>>(var_iter: I) -> LVarSet {
    assert!(size_of::<u64>() <= size_of::<usize>());
    LVarSet{
      inner:    FixedBitSet::from_iter(var_iter.into_iter().map(|var| var.0 as usize)),
    }
  }
}

impl<'v> FromIterator<&'v LVar> for LVarSet {
  fn from_iter<I: IntoIterator<Item=&'v LVar>>(var_iter: I) -> LVarSet {
    assert!(size_of::<u64>() <= size_of::<usize>());
    LVarSet{
      inner:    FixedBitSet::from_iter(var_iter.into_iter().map(|var| var.0 as usize)),
    }
  }
}

impl LVarSet {
  pub fn empty() -> LVarSet {
    LVarSet{
      inner:    FixedBitSet::with_capacity(32),
    }
  }

  pub fn iter<'a>(&'a self) -> impl Iterator<Item=LVar> + 'a {
    self.inner.ones().map(|v| LVar(v as u64))
  }

  pub fn insert(&mut self, var: LVar) {
    assert!(size_of::<u64>() <= size_of::<usize>());
    let v = var.0 as usize;
    if v >= self.inner.len() {
      self.inner.grow(v + 1);
    }
    self.inner.insert(v);
  }

  pub fn union(&self, other: &LVarSet) -> LVarSet {
    LVarSet{
      inner:    FixedBitSet::from_iter(self.inner.union(&other.inner)),
    }
  }

  pub fn difference(&self, other: &LVarSet) -> LVarSet {
    LVarSet{
      inner:    FixedBitSet::from_iter(self.inner.difference(&other.inner)),
    }
  }
}

/*#[derive(Debug)]
pub enum LTyvar {
  Unk(u64),
}

pub type LTyvarRef = Rc<LTyvar>;*/

#[derive(Debug)]
pub enum LTy {
  // TODO
}

pub type LTyRef = Rc<LTy>;

#[derive(Clone, Debug, Serialize)]
//#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum LPat {
  Cons(LPatRef, LPatRef),
  Concat(LPatRef, LPatRef),
  STuple(Vec<LPatRef>),
  Tuple(Vec<LPatRef>),
  UnitLit,
  BitLit(bool),
  IntLit(i64),
  //FloLit(f64),
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

impl Serialize for LPatRef {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    (&*self.inner).serialize(serializer)
  }
}

impl LPat {
  fn _vars(&self, vars_set: &mut HashSet<LVar>, vars_buf: &mut Vec<LVar>) {
    match self {
      &LPat::Cons(ref lhs, ref rhs) => {
        lhs._vars(vars_set, vars_buf);
        rhs._vars(vars_set, vars_buf);
      }
      &LPat::Concat(ref lhs, ref rhs) => {
        lhs._vars(vars_set, vars_buf);
        rhs._vars(vars_set, vars_buf);
      }
      &LPat::STuple(ref elems) => {
        for e in elems.iter() {
          e._vars(vars_set, vars_buf);
        }
      }
      &LPat::Tuple(ref elems) => {
        for e in elems.iter() {
          e._vars(vars_set, vars_buf);
        }
      }
      &LPat::Var(ref v) => {
        assert!(!vars_set.contains(v));
        vars_set.insert(v.clone());
        vars_buf.push(v.clone());
      }
      &LPat::Alias(ref t, ref v) => {
        t._vars(vars_set, vars_buf);
        assert!(!vars_set.contains(v));
        vars_set.insert(v.clone());
        vars_buf.push(v.clone());
      }
      _ => {}
    }
  }

  pub fn vars(&self) -> Vec<LVar> {
    let mut vars_buf = vec![];
    let mut vars_set = HashSet::new();
    self._vars(&mut vars_set, &mut vars_buf);
    vars_buf
  }
}

/*#[derive(Clone, Debug, Serialize)]
//#[derive(Debug, Serialize, Deserialize)]
pub struct LPat {
  pub term: LPatRef,
}*/

impl LPat {
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum LEnvKey {
  Var(LVar),
  Param(usize),
}

pub struct LVMBCLambdaDef {
  // TODO
  pub ar:   usize,
  pub ty:   Option<Rc<dyn Fn(&mut LBuilder) -> (Vec<LTy>, LTy)>>,
  pub adj:  Option<Rc<dyn Fn(&mut LBuilder, Vec<LVar>, LVar) -> LExpr>>,
  pub cg:   Option<Rc<dyn Fn() -> VMBoxCode>>,
}

pub enum LVMExt {
  Deref(VMAddr),
  BCLambda(Vec<LVar>, LVMBCLambdaDef),
}

impl Debug for LVMExt {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    // TODO
    match self {
      &LVMExt::Deref(..) => write!(f, "Deref(...)"),
      &LVMExt::BCLambda(..) => write!(f, "BCLambda(...)"),
    }
  }
}

pub enum LTermVMExt {
  BCLambda(Vec<LVar>, VMBoxCode),
}

impl Debug for LTermVMExt {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    // TODO
    write!(f, "BCLambda(...)")
  }
}

#[derive(Debug)]
//#[derive(Debug, Serialize)]
pub enum LTerm<E=LExpr, X=LVMExt> {
  End,
  Break(E),
  Trace(E),
  NoRet,
  NonSmooth,
  Apply(E, Vec<E>),
  OldEnv(Vec<(Option<LHash>, LVar, E)>),
  AdjEnv(Vec<(LVar, E)>),
  AEnv(Vec<(LEnvKey, E)>),
  ACons(LEnvKey, E, E),
  AConcat(E, E),
  AApp(Vec<LVar>, Vec<LVar>, E),
  ERet(Vec<LVar>, E),
  EHashSelect(E, LHash),
  ESelect(E, LVar),
  EImport(E, E),
  Lambda(Vec<LVar>, E),
  LambdaEnv(Vec<(Option<LHash>, LVar)>, LVar, Vec<LVar>, E),
  D(E),
  Adj(E),
  //AdjEnv(Vec<(Option<LHash>, LVar)>, E),
  Tng(E),
  Let(LVar, E, E),
  Fix(LVar, E),
  Switch(E, E, E),
  Match(E, Vec<(LPat, E)>),
  Cons(E, E),
  Concat(E, E),
  STuple(Vec<E>),
  Tuple(Vec<E>),
  UnitLit,
  BitLit(bool),
  IntLit(i64),
  FloLit(f64),
  Lookup(LVar),
  Reclaim(LVar, E),
  VMExt(X),
}

#[derive(Debug)]
pub struct LTermRef<E=LExpr, X=LVMExt> {
  inner:    Rc<LTerm<E, X>>,
}

impl<E, X> Clone for LTermRef<E, X> {
  fn clone(&self) -> LTermRef<E, X> {
    LTermRef{inner: self.inner.clone()}
  }
}

impl<E, X> Deref for LTermRef<E, X> {
  type Target = LTerm<E, X>;

  fn deref(&self) -> &LTerm<E, X> {
    &*self.inner
  }
}

impl<E: Serialize, X: Serialize> Serialize for LTermRef<E, X> where LTerm<E, X>: Serialize {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    (&*self.inner).serialize(serializer)
  }
}

impl<E, X> LTermRef<E, X> {
  pub fn new(term: LTerm<E, X>) -> LTermRef<E, X> {
    LTermRef{inner: Rc::new(term)}
  }
}

#[derive(Clone, Debug)]
pub struct LTyInf {
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub label:    LLabel,
  pub term:     LTermRef,
  //pub tyinf:    LTyInf,
}

impl LExpr {
  pub fn with_gen_rec(&self, _new_gen: u64) -> LExpr {
    self.clone()
  }

  /*pub fn with_gen_rec(&self, new_gen: u64) -> LExpr {
    if self.gen == new_gen {
      return self.clone();
    }
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Apply(
              head.with_gen_rec(new_gen),
              args.iter().map(|a| a.with_gen_rec(new_gen)).collect(),
          ))
        }
      }
      &LTerm::Adj(ref sink) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Adj(
              sink.with_gen_rec(new_gen),
          ))
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Lambda(
              params.clone(),
              body.with_gen_rec(new_gen),
          ))
        }
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Let(
              name.clone(),
              body.with_gen_rec(new_gen),
              rest.with_gen_rec(new_gen),
          ))
        }
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Fix(
              fixname.clone(),
              fixbody.with_gen_rec(new_gen),
          ))
        }
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Switch(
              pred.with_gen_rec(new_gen),
              top.with_gen_rec(new_gen),
              bot.with_gen_rec(new_gen),
          ))
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Match(
              query.with_gen_rec(new_gen),
              pat_arms.iter().map(|&(ref p, ref a)| (p.clone(), a.with_gen_rec(new_gen))).collect(),
          ))
        }
      }
      &LTerm::Tuple(ref elems) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     LTermRef::new(LTerm::Tuple(
              elems.iter().map(|e| e.with_gen_rec(new_gen)).collect(),
          ))
        }
      }
      &LTerm::UnitLit   |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        LExpr{
          gen:      new_gen,
          label:    self.label.clone(),
          term:     self.term.clone(),
        }
      }
      &LTerm::EHashSelect(..) => {
        // FIXME
        unimplemented!();
      }
      &LTerm::ESelect(..) => {
        // FIXME
        unimplemented!();
      }
      e => {
        panic!("with_gen_rec: unimplemented ltree expr: {:?}", e);
      }
    }
  }*/
}

#[derive(Debug)]
pub struct LTreeEnvInfo {
  //pub gen:  u64,
  pub data: HashMap<LLabel, LEnv>,
}

impl LExpr {
  pub fn _env_info_pass(&self, env: LEnv, info: &mut LTreeEnvInfo) {
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        info.data.insert(self.label.clone(), env.clone());
        head._env_info_pass(env.clone(), info);
        for arg in args.iter() {
          arg._env_info_pass(env.clone(), info);
        }
      }
      &LTerm::Adj(ref sink) => {
        info.data.insert(self.label.clone(), env.clone());
        sink._env_info_pass(env.clone(), info);
      }
      &LTerm::Lambda(ref params, ref body) => {
        info.data.insert(self.label.clone(), env.clone());
        let mut body_env = env;
        for param in params.iter() {
          body_env = body_env.fork_bvar(param.clone());
        }
        body._env_info_pass(body_env, info);
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        info.data.insert(self.label.clone(), env.clone());
        body._env_info_pass(env.clone(), info);
        let rest_env = env.fork(name.clone(), body.clone());
        rest._env_info_pass(rest_env, info);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        // FIXME
        /*let fix_env = env.fork_fixed(ltree.label.clone(), fixname.clone(), fixbody.term.clone(), Some(env.clone()));
        let fixbody = self._env_info_pass(fix_env, fixbody.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
        }*/
        unimplemented!();
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        info.data.insert(self.label.clone(), env.clone());
        pred._env_info_pass(env.clone(), info);
        top._env_info_pass(env.clone(), info);
        bot._env_info_pass(env.clone(), info);
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        info.data.insert(self.label.clone(), env.clone());
        query._env_info_pass(env.clone(), info);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut arm_env = env.clone();
          for pv in pat.vars().into_iter() {
            arm_env = arm_env.fork_bvar(pv);
          }
          arm._env_info_pass(arm_env, info);
        }
      }
      &LTerm::Tuple(ref elems) => {
        info.data.insert(self.label.clone(), env.clone());
        for elem in elems.iter() {
          elem._env_info_pass(env.clone(), info);
        }
      }
      &LTerm::UnitLit   |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        info.data.insert(self.label.clone(), env);
      }
      &LTerm::EHashSelect(..) => {
        // FIXME
        unimplemented!();
      }
      &LTerm::ESelect(..) => {
        // FIXME
        unimplemented!();
      }
      e => {
        panic!("env info pass: unimplemented ltree expr: {:?}", e);
      }
    }
  }

  pub fn env<'root>(&self, ltree: &'root LTree) -> &'root LEnv {
    let root = ltree.root.clone();
    //assert_eq!(self.gen, root.gen);
    let env_info = ltree.info.env.borrow_with(move || {
      let mut env_info = LTreeEnvInfo{
        //gen:  root.gen,
        data: HashMap::new(),
      };
      root._env_info_pass(LEnv::default(), &mut env_info);
      env_info
    });
    //assert_eq!(self.gen, env_info.gen);
    match env_info.data.get(&self.label) {
      None => panic!(),
      Some(env) => env,
    }
  }

  pub fn maybe_env<'root>(&self, ltree: &'root LTree) -> Option<&'root LEnv> {
    ltree.info.env.borrow()
      .and_then(|info| info.data.get(&self.label))
  }
}

#[derive(Debug)]
pub struct LTreeFreeEnvInfo {
  //pub gen:  u64,
  pub data: HashMap<LLabel, LVarSet>,
}

impl LExpr {
  pub fn _free_env_info_pass_init(&self, info: &mut LTreeFreeEnvInfo) {
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        head._free_env_info_pass_init(info);
        for arg in args.iter() {
          arg._free_env_info_pass_init(info);
        }
      }
      &LTerm::Adj(ref sink) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        sink._free_env_info_pass_init(info);
      }
      &LTerm::Lambda(ref _params, ref body) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        body._free_env_info_pass_init(info);
      }
      &LTerm::Let(ref _name, ref body, ref rest) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        body._free_env_info_pass_init(info);
        rest._free_env_info_pass_init(info);
      }
      /*&LTerm::Fix(..) => {
      }*/
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        pred._free_env_info_pass_init(info);
        top._free_env_info_pass_init(info);
        bot._free_env_info_pass_init(info);
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
        query._free_env_info_pass_init(info);
        for &(_, ref arm) in pat_arms.iter() {
          arm._free_env_info_pass_init(info);
        }
      }
      &LTerm::UnitLit   |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) => {
        info.data.insert(self.label.clone(), LVarSet::empty());
      }
      &LTerm::Lookup(ref var) => {
        let mut this_uses = LVarSet::empty();
        this_uses.insert(var.clone());
        info.data.insert(self.label.clone(), this_uses);
      }
      _ => unimplemented!(),
    }
  }

  pub fn _free_env_info_pass_step(&self, info: &mut LTreeFreeEnvInfo) -> bool {
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        let this_free_env = self._free_env(info).clone();
        let mut changed = head._free_env_info_pass_step(info);
        let head_free_env = head._free_env(info).clone();
        //this_free_env_new = this_free_env_new.union(&head_free_env);
        let mut this_free_env_new = head_free_env;
        for arg in args.iter() {
          changed |= arg._free_env_info_pass_step(info);
          let arg_free_env = arg._free_env(info).clone();
          this_free_env_new = this_free_env_new.union(&arg_free_env);
        }
        let this_changed = this_free_env != this_free_env_new;
        info.data.insert(self.label.clone(), this_free_env_new);
        changed | this_changed
      }
      &LTerm::Adj(ref sink) => {
        let sink_changed = sink._free_env_info_pass_step(info);
        let sink_free_env = sink._free_env(info).clone();
        let this_free_env = self._free_env(info).clone();
        //let this_free_env_new = this_free_env.union(&sink_free_env);
        let this_free_env_new = sink_free_env;
        let this_changed = this_free_env_new != this_free_env;
        info.data.insert(self.label.clone(), this_free_env_new);
        let changed = sink_changed | this_changed;
        changed
      }
      &LTerm::Lambda(ref params, ref body) => {
        // NOTE: Equation: this.free_env U= body.free_env \ bindvars.
        let body_changed = body._free_env_info_pass_step(info);
        let bindvars = LVarSet::from_iter(params.iter());
        let body_free_env = body._free_env(info).clone();
        let nonbind_body_free_env = body_free_env.difference(&bindvars);
        let this_free_env = self._free_env(info).clone();
        //let this_free_env_new = this_free_env.union(&nonbind_body_free_env);
        let this_free_env_new = nonbind_body_free_env;
        let this_changed = this_free_env_new != this_free_env;
        info.data.insert(self.label.clone(), this_free_env_new);
        let changed = body_changed | this_changed;
        changed
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        // NOTE: Equation: this.free_env U= body.free_env U (rest.free_env \ {name}).
        let body_changed = body._free_env_info_pass_step(info);
        let rest_changed = rest._free_env_info_pass_step(info);
        let bindvars = LVarSet::from_iter(&[name.clone()]);
        let body_free_env = body._free_env(info).clone();
        let rest_free_env = rest._free_env(info).clone();
        let nonbind_rest_free_env = rest_free_env.difference(&bindvars);
        let this_free_env = self._free_env(info).clone();
        //let this_free_env_new = this_free_env.union(&body_free_env.union(&nonbind_rest_free_env));
        let this_free_env_new = body_free_env.union(&nonbind_rest_free_env);
        let this_changed = this_free_env_new != this_free_env;
        info.data.insert(self.label.clone(), this_free_env_new);
        let changed = body_changed | rest_changed | this_changed;
        changed
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        // NOTE: Equation: this.free_env U= fixbody.free_env \ {fixname}.
        let fixbody_changed = fixbody._free_env_info_pass_step(info);
        let bindvars = LVarSet::from_iter(&[fixname.clone()]);
        let fixbody_free_env = fixbody._free_env(info).clone();
        let nonbind_fixbody_free_env = fixbody_free_env.difference(&bindvars);
        let this_free_env = self._free_env(info).clone();
        //let this_free_env_new = this_free_env.union(&nonbind_fixbody_free_env);
        let this_free_env_new = nonbind_fixbody_free_env;
        let this_changed = this_free_env_new != this_free_env;
        info.data.insert(self.label.clone(), this_free_env_new);
        let changed = fixbody_changed | this_changed;
        changed
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        let this_free_env_old = self._free_env(info).clone();
        let mut changed = false;
        //let mut this_free_env_new = this_free_env_old.clone();
        changed |= pred._free_env_info_pass_step(info);
        let pred_free_env = pred._free_env(info).clone();
        //this_free_env_new = this_free_env_new.union(&pred_free_env);
        let mut this_free_env_new = pred_free_env;
        changed |= top._free_env_info_pass_step(info);
        let top_free_env = top._free_env(info).clone();
        this_free_env_new = this_free_env_new.union(&top_free_env);
        changed |= bot._free_env_info_pass_step(info);
        let bot_free_env = bot._free_env(info).clone();
        this_free_env_new = this_free_env_new.union(&bot_free_env);
        changed |= this_free_env_old != this_free_env_new;
        info.data.insert(self.label.clone(), this_free_env_new);
        changed
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let this_free_env_old = self._free_env(info).clone();
        let mut changed = false;
        //let mut this_free_env_new = this_free_env_old.clone();
        changed |= query._free_env_info_pass_step(info);
        let query_free_env = query._free_env(info).clone();
        //this_free_env_new = this_free_env_new.union(&query_free_env);
        let mut this_free_env_new = query_free_env;
        for &(ref pat, ref arm) in pat_arms.iter() {
          let pat_bindvars = LVarSet::from_iter(pat.vars().into_iter());
          changed |= arm._free_env_info_pass_step(info);
          let arm_free_env = arm._free_env(info).clone();
          let nonbind_arm_free_env = arm_free_env.difference(&pat_bindvars);
          this_free_env_new = this_free_env_new.union(&nonbind_arm_free_env);
        }
        changed |= this_free_env_old != this_free_env_new;
        info.data.insert(self.label.clone(), this_free_env_new);
        changed
      }
      &LTerm::UnitLit   |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        false
      }
      _ => unimplemented!(),
    }
  }

  pub fn _free_env_info_pass(&self, free_env_info: &mut LTreeFreeEnvInfo) {
    self._free_env_info_pass_init(free_env_info);
    let _ = self._free_env_info_pass_step(free_env_info);
    loop {
      let changed = self._free_env_info_pass_step(free_env_info);
      if !changed {
        return;
      }
    }
  }

  pub fn _free_env<'root>(&self, info: &'root LTreeFreeEnvInfo) -> &'root LVarSet {
    match info.data.get(&self.label) {
      None => panic!(),
      Some(free_env) => free_env,
    }
  }

  pub fn free_env<'root>(&self, ltree: &'root LTree) -> &'root LVarSet {
    let root = ltree.root.clone();
    //assert_eq!(self.gen, root.gen);
    let free_env_info = ltree.info.free_env.borrow_with(move || {
      let mut free_env_info = LTreeFreeEnvInfo{
        //gen:  root.gen,
        data: HashMap::new(),
      };
      root._free_env_info_pass(&mut free_env_info);
      free_env_info
    });
    //assert_eq!(self.gen, free_env_info.gen);
    match free_env_info.data.get(&self.label) {
      None => panic!(),
      Some(free_env) => free_env,
    }
  }

  pub fn maybe_free_env<'root>(&self, ltree: &'root LTree) -> Option<&'root LVarSet> {
    ltree.info.free_env.borrow()
      .and_then(|info| info.data.get(&self.label))
  }
}

#[derive(Debug)]
pub struct LTreeTypeckInfo {
  //pub gen:  u64,
  // FIXME
  //pub data: HashMap<LLabel, ()>,
}

#[derive(Debug)]
pub struct LTreeTmpAdjInfo {
  //pub gen:      u64,
  pub sink:     Option<LVar>,
  pub sink_def: Option<LLabel>,
  //pub work_set: HashSet<LVar>,
  //pub data: HashMap<LLabel, LExpr>,
}

impl LExpr {
  /*pub fn _tmp_adj_info_pass_kont_seq(mut queue: VecDeque<LExpr>, free_env: &LTreeFreeEnvInfo, info: &mut LTreeTmpAdjInfo, kont: &mut dyn FnMut(&LTreeFreeEnvInfo, &mut LTreeTmpAdjInfo)) {
    match queue.pop_front() {
      Some(ltree) => {
        ltree._tmp_adj_info_pass_kont(free_env, info, &mut |free_env, info| {
          LExpr::_tmp_adj_info_pass_kont_seq(queue.clone(), free_env, info, kont);
        });
      }
      None => {
        kont(free_env, info);
      }
    }
  }

  pub fn _tmp_adj_info_pass_kont(&self, free_env: &LTreeFreeEnvInfo, info: &mut LTreeTmpAdjInfo, kont: &mut dyn FnMut(&LTreeFreeEnvInfo, &mut LTreeTmpAdjInfo)) {
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        head._tmp_adj_info_pass_kont(free_env, info, &mut |free_env, info| {
          LExpr::_tmp_adj_info_pass_kont_seq(VecDeque::from(args.clone()), free_env, info, &mut |free_env, info| {
            kont(free_env, info);
          });
        });
      }
      &LTerm::Adj(ref sink) => {
        sink._tmp_adj_info_pass_kont(free_env, info, &mut |free_env, info| {
          //unimplemented!();
          kont(free_env, info);
        });
      }
      &LTerm::Lambda(ref params, ref body) => {
        body._tmp_adj_info_pass_kont(free_env, info, &mut |free_env, info| {
          //unimplemented!();
          kont(free_env, info);
        });
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        body._tmp_adj_info_pass_kont(free_env, info, &mut |free_env, info| {
          //unimplemented!();
          rest._tmp_adj_info_pass_kont(free_env, info, kont);
          if info.work_set.contains(name) {
            // FIXME: depending on the rhs type, generate the augmented expr.
            for fv in self._free_env(free_env).iter() {
              info.work_set.insert(fv.clone());
            }
          }
        });
      }
      _ => unimplemented!(),
    }
  }*/

  pub fn _tmp_adj_info_pass_init_sink(&self, /*free_env: &LTreeFreeEnvInfo,*/ info: &mut LTreeTmpAdjInfo) {
    match &*self.term {
      &LTerm::Adj(ref sink) => {
        match &*sink.term {
          &LTerm::Lookup(ref sink) => {
            if info.sink.is_none() {
              info.sink = Some(sink.clone());
            }
          }
          &LTerm::UnitLit |
          &LTerm::BitLit(_) |
          &LTerm::IntLit(_) |
          &LTerm::FloLit(_) => {}
          _ => {
            panic!("bug: tmp adj info: requires normalized ltree");
          }
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        head._tmp_adj_info_pass_init_sink(info);
        for a in args.iter() {
          a._tmp_adj_info_pass_init_sink(info);
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        body._tmp_adj_info_pass_init_sink(info);
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        body._tmp_adj_info_pass_init_sink(info);
        rest._tmp_adj_info_pass_init_sink(info);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        unimplemented!();
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        query._tmp_adj_info_pass_init_sink(info);
        for &(_, ref a) in pat_arms.iter() {
          a._tmp_adj_info_pass_init_sink(info);
        }
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {}
      _ => {
        unimplemented!();
      }
    }
  }

  pub fn _tmp_adj_info_pass_sink(&self, /*free_env: &LTreeFreeEnvInfo,*/ info: &mut LTreeTmpAdjInfo) {
    match &*self.term {
      &LTerm::Apply(ref head, ref args) => {
        head._tmp_adj_info_pass_sink(info);
        for a in args.iter() {
          a._tmp_adj_info_pass_sink(info);
        }
      }
      &LTerm::Adj(ref sink) => {
        sink._tmp_adj_info_pass_sink(info);
      }
      &LTerm::Lambda(ref params, ref body) => {
        for p in params.iter() {
          if p == info.sink.as_ref().unwrap() {
            if info.sink_def.is_none() {
              info.sink_def = Some(self.label.clone());
            } else {
              panic!("bug: adj sink should have one and only one def");
            }
          }
        }
        body._tmp_adj_info_pass_sink(info);
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        if name == info.sink.as_ref().unwrap() {
          if info.sink_def.is_none() {
            info.sink_def = Some(self.label.clone());
          } else {
            panic!("bug: adj sink should have one and only one def");
          }
        }
        body._tmp_adj_info_pass_sink(info);
        rest._tmp_adj_info_pass_sink(info);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        unimplemented!();
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {}
      _ => {
        unimplemented!();
      }
    }
  }
}

#[derive(Clone, Debug)]
pub struct LTreeInfo {
  pub env:      Rc<LazyCell<LTreeEnvInfo>>,
  pub free_env: Rc<LazyCell<LTreeFreeEnvInfo>>,
  //pub typeck:   Rc<LazyCell<LTreeTypeckInfo>>,
  //pub tmp_adj:  Rc<LazyCell<LTreeTmpAdjInfo>>,
}

impl Default for LTreeInfo {
  fn default() -> LTreeInfo {
    LTreeInfo{
      env:      Rc::new(LazyCell::new()),
      free_env: Rc::new(LazyCell::new()),
      //typeck:   Rc::new(LazyCell::new()),
      //adj:      Rc::new(LazyCell::new()),
    }
  }
}

#[derive(Clone, Debug)]
pub struct LTree {
  pub info: LTreeInfo,
  pub root: LExpr,
}

impl LTree {
  /*pub fn _pretty_print(&self) {
    LTreePrettyPrinter{}.print(self.clone());
  }*/

  pub fn with_env_info(self) -> LTree {
    self.root.env(&self);
    self
  }

  pub fn with_free_env_info(self) -> LTree {
    self.root.free_env(&self);
    self
  }
}

#[derive(Clone, Debug)]
pub enum LDef {
  BVar,
  Code(LExpr),
  // TODO
  Fixpoint(LLabel, LVar, LTermRef, /*LEnvInfo,*/ Option<LEnv>),
}

/*#[derive(Clone, Default)]
pub struct LEnvNew {
  pub bindings: VertreapMap<LVar, (LLDepth, LHash, LDef)>,
  pub hashes:   VertreapMap<LHash, LVar>,
  pub vars:     VertreapMap<usize, LVar>,
}*/

#[derive(Clone, Default, Debug)]
pub struct LEnv {
  //pub bindings: HashMap<LVar, (usize, Rc<LExpr>)>,
  pub bindings: HashMap<LVar, (LLDepth, LDef)>,
  //pub vars:     Vec<(LVar, usize)>,
  pub vars:     Vec<LVar>,
  pub names:    HashMap<String, LVar>,
  //pub hashes:   HashMap<LHash, LVar>,
}

impl LEnv {
  pub fn _bind_bvar(&mut self, var: LVar) {
    let left_depth = self.vars.len();
    self.bindings.insert(var.clone(), (LLDepth(left_depth), LDef::BVar));
    self.vars.push(var);
  }

  pub fn _bind_free(&mut self, var: LVar, code: LExpr) {
    let left_depth = self.vars.len();
    self.bindings.insert(var.clone(), (LLDepth(left_depth), LDef::Code(code)));
    self.vars.push(var);
  }

  pub fn _bind_fixed(&mut self, label: LLabel, fixvar: LVar, fixbody: LTermRef, env: Option<LEnv>) {
    let left_depth = self.vars.len();
    self.bindings.insert(fixvar.clone(), (LLDepth(left_depth), LDef::Fixpoint(label, fixvar.clone(), fixbody, env)));
    self.vars.push(fixvar);
  }

  pub fn _bind_named(&mut self, name: String, var: LVar, body: LExpr) {
    let left_depth = self.vars.len();
    self.bindings.insert(var.clone(), (LLDepth(left_depth), LDef::Code(body)));
    self.names.insert(name, var.clone());
    self.vars.push(var);
  }

  /*pub fn _lookup_name(&self, name: String) -> (LVar, LExpr) {
    match self.names.get(&name) {
      Some(var) => {
        match self.bindings.get(var) {
          Some(&(_, LDef::BVar)) => {
            // FIXME
            /*let code = LExpr{
              gen:      0,
              label:    label.clone(),
              term:     LTermRef::new(LTerm::Lookup(var.clone())),
              info:     LExprInfo::default(),
            };
            (var.clone(), code.clone())*/
            unimplemented!();
          }
          Some(&(_, LDef::Code(ref code))) => {
            (var.clone(), code.clone())
          }
          Some(&(_, LDef::Fixpoint(ref label, ref fixvar, ref fixbody, ref maybe_env))) => {
            // TODO: in the case of static env info, need to make sure that
            // the returned `LExpr` knows about itself... hence the fixpoint!
            // FIXME: initializing an empty expr info seems wrong.
            let mut info = LExprInfo::default();
            if let &Some(ref env) = maybe_env {
              let fix_env = env.fork_fixed(label.clone(), fixvar.clone(), fixbody.clone(), maybe_env.clone());
              info.env = Some(fix_env.clone());
            }
            let code = LExpr{
              // FIXME: correct gen number.
              gen:      0,
              label:    label.clone(),
              term:     fixbody.clone(),
              info,
            };
            (var.clone(), code)
          }
          None => panic!(),
        }
      }
      None => panic!(),
    }
  }*/

  pub fn fork_bvar(&self, var: LVar) -> LEnv {
    let mut new_env = self.clone();
    new_env._bind_bvar(var);
    new_env
  }

  pub fn fork(&self, /*hash: LHash,*/ var: LVar, body: LExpr) -> LEnv {
    let mut new_env = self.clone();
    new_env._bind_free(var, body);
    new_env
  }

  pub fn fork_fixed(&self, label: LLabel, /*hash: LHash,*/ fixname: LVar, fixbody: LTermRef, env: Option<LEnv>) -> LEnv {
    let mut new_env = self.clone();
    new_env._bind_fixed(label, fixname, fixbody, env);
    new_env
  }
}

#[derive(Default)]
pub struct LBoxtyBuilder {
  id_ctr:   u64,
}

impl LBoxtyBuilder {
  pub fn fresh(&mut self) -> LBoxty {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    let new_boxty = LBoxty(id);
    new_boxty
  }
}

#[derive(Debug)]
pub enum LBindKey {
  Fresh,
  Name(String),
  Hash(LHash),
  //IntLit(i64),
  //FloLit(f64),
}

#[derive(Default)]
pub struct LVarBuilder {
  //n_to_id:  HashMap<String, LVar>,
  h_to_id:  HashMap<LHash, LVar>,
  id_to_k:  HashMap<LVar, LBindKey>,
  id_ctr:   u64,
}

impl LVarBuilder {
  pub fn _debug_dump_vars(&self) {
    println!("DEBUG: vars: {:?}", self.id_to_k);
  }

  pub fn maybe_rev_lookup(&self, var: LVar) -> Option<LHash> {
    match self.id_to_k.get(&var) {
      Some(LBindKey::Hash(ref hash)) => {
        Some(hash.clone())
      }
      _ => None,
    }
  }

  //pub fn rev_lookup(&mut self, var: LVar) -> String {
  pub fn rev_lookup(&self, var: LVar) -> LHash {
    match self.id_to_k.get(&var) {
      //Some(LBindKey::Name(ref name)) => {
      Some(LBindKey::Hash(ref hash)) => {
        //name.clone()
        hash.clone()
      }
      Some(_) => panic!(),
      None => panic!(),
    }
  }

  //pub fn lookup(&mut self, name: String) -> LVar {
  pub fn lookup(&self, hash: LHash) -> LVar {
    match self.h_to_id.get(&hash) {
      Some(var) => var.clone(),
      None => panic!(),
    }
  }

  /*pub fn insert(&mut self, name: String) {
    let _ = self.bind(name);
  }*/

  pub fn fresh(&mut self) -> LVar {
    let &mut LVarBuilder{ref mut id_ctr, ..} = self;
    *id_ctr += 1;
    let id = *id_ctr;
    assert!(id != 0);
    let new_var = LVar(id);
    new_var
  }

  //pub fn bind(&mut self, name: String) -> (String, LVar, Option<LVar>) {
  pub fn bind(&mut self, hash: LHash) -> (LHash, LVar, Option<LVar>) {
    let &mut LVarBuilder{
      //ref mut n_to_id,
      ref mut h_to_id,
      ref mut id_to_k,
      ref mut id_ctr} = self;
    *id_ctr += 1;
    let id = *id_ctr;
    assert!(id != 0);
    let new_var = LVar(id);
    //let old_var = n_to_id.insert(name.clone(), new_var.clone());
    let old_var = h_to_id.insert(hash.clone(), new_var.clone());
    //id_to_k.insert(new_var.clone(), LBindKey::Name(name.clone()));
    id_to_k.insert(new_var.clone(), LBindKey::Hash(hash.clone()));
    //(name, new_var, old_var)
    (hash, new_var, old_var)
  }

  //pub fn unbind(&mut self, name: String, new_var: LVar, old_var: Option<LVar>) {
  pub fn unbind(&mut self, hash: LHash, new_var: LVar, old_var: Option<LVar>) {
    let pop_var = if let Some(old_var) = old_var {
      //self.n_to_id.insert(name, old_var)
      self.h_to_id.insert(hash, old_var)
    } else {
      //self.n_to_id.remove(&name)
      self.h_to_id.remove(&hash)
    };
    match pop_var {
      Some(pop_var) => assert_eq!(pop_var, new_var),
      None => panic!(),
    }
  }
}

#[derive(Default)]
pub struct LHashBuilder {
  n_to_id:  HashMap<String, LHash>,
  id_to_n:  HashMap<LHash, String>,
  id_ctr:   u64,
}

impl LHashBuilder {
  pub fn rev_lookup(&self, hash: LHash) -> String {
    match self.id_to_n.get(&hash) {
      Some(name) => name.clone(),
      None => panic!(),
    }
  }

  pub fn lookup(&mut self, name: String) -> LHash {
    let &mut LHashBuilder{
      ref mut n_to_id,
      ref mut id_to_n,
      ref mut id_ctr} = self;
    n_to_id.entry(name.clone()).or_insert_with(|| {
      *id_ctr += 1;
      let id = *id_ctr;
      assert!(id != 0);
      let new_hash = LHash(id);
      id_to_n.insert(new_hash.clone(), name);
      new_hash
    }).clone()
  }
}

#[derive(Default)]
pub struct LLabelBuilder {
  id_ctr:   u64,
}

impl LLabelBuilder {
  pub fn fresh(&mut self) -> LLabel {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    LLabel(id)
  }
}

pub struct LBuilder {
  gen_ctr:      u64,
  pub labels:   LLabelBuilder,
  pub hashes:   LHashBuilder,
  pub vars:     LVarBuilder,
  pub boxtys:   LBoxtyBuilder,
}

impl LBuilder {
  pub fn new() -> LBuilder {
    let labels = LLabelBuilder::default();
    let hashes = LHashBuilder::default();
    let vars = LVarBuilder::default();
    let boxtys = LBoxtyBuilder::default();
    LBuilder{
      gen_ctr: 0,
      labels,
      hashes,
      vars,
      boxtys,
    }
  }

  pub fn apply_term(&mut self, head: &mut FnMut(&mut Self) -> LExpr, args: Vec<&mut FnMut(&mut Self) -> LExpr>) -> LExpr {
    LExpr{
      //gen:    self._gen(),
      label:  self.labels.fresh(),
      term:   LTermRef::new(LTerm::Apply(
          head(self),
          args.into_iter().map(|a| a(self)).collect(),
      )),
    }
  }

  pub fn lambda_term(&mut self, params: Vec<LVar>, body: &mut FnMut(&mut Self) -> LExpr) -> LExpr {
    LExpr{
      //gen:    self._gen(),
      label:  self.labels.fresh(),
      term:   LTermRef::new(LTerm::Lambda(
          params,
          body(self),
      )),
    }
  }

  pub fn lookup_term(&mut self, v: LVar) -> LExpr {
    LExpr{
      //gen:    self._gen(),
      label:  self.labels.fresh(),
      term:   LTermRef::new(LTerm::Lookup(v)),
    }
  }

  pub fn vm_deref_term(&mut self, addr: VMAddr) -> LExpr {
    LExpr{
      //gen:    self._gen(),
      label:  self.labels.fresh(),
      term:   LTermRef::new(LTerm::VMExt(LVMExt::Deref(addr)))
    }
  }

  pub fn _debug_dump_vars(&self) {
    self.vars._debug_dump_vars();
  }

  pub fn _alloc_name(&mut self, name: &str) -> (LHash, LVar, LLabel) {
    let hash = self.hashes.lookup(name.to_string());
    let (_, var, _) = self.vars.bind(hash.clone());
    //println!("DEBUG: LBuilder: insert: {:?} {:?} {:?}", name, hash, var);
    let label = self.labels.fresh();
    (hash, var, label)
  }

  pub fn _gen(&self) -> u64 {
    self.gen_ctr
  }

  //pub fn _make_bclambda(&mut self, bc: VMBoxCode) -> LExpr {
  pub fn _make_bclambda(&mut self, ar: usize, cg: Rc<dyn Fn() -> VMBoxCode>, adj: Option<Rc<dyn Fn(&mut LBuilder, Vec<LVar>, LVar) -> LExpr>>) -> LExpr {
    let bcdef = LVMBCLambdaDef{
      ar,
      // FIXME
      ty:   None,
      //cg:   Some(Rc::new(move || { bc.clone() })),
      cg:   Some(cg),
      //adj:  None,
      //adj:  Some(Rc::new(move || {  })),
      adj,
    };
    LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::VMExt(LVMExt::BCLambda(vec![], bcdef))), /*info: LExprInfo::default()*/}
  }

  //pub fn _alloc_bclambda(&mut self, name: &str, bc: VMBoxCode) -> (LHash, LVar, LLabel, LExpr) {
  pub fn _alloc_bclambda(&mut self, name: &str, ar: usize, cg: Rc<dyn Fn() -> VMBoxCode>, adj: Option<Rc<dyn Fn(&mut LBuilder, Vec<LVar>, LVar) -> LExpr>>) -> (LHash, LVar, LLabel, LExpr) {
    let (hash, var, label) = self._alloc_name(name);
    let bclam = self._make_bclambda(ar, cg, adj);
    (hash, var, label, bclam)
  }

  pub fn _include_toplevel_and_lower(&mut self, htree: Rc<HExpr>) -> LExpr {
    fn bind(_gen: u64, label: LLabel, var: LVar, body: LExpr, rest: LExpr) -> LExpr {
      LExpr{/*gen,*/ label: label, term: LTermRef::new(LTerm::Let(var, body, rest)), /*info: LExprInfo::default()*/}
    }
    fn bind_next<B: Iterator<Item=(&'static str, usize, Rc<dyn Fn() -> VMBoxCode>, Option<Rc<dyn Fn(&mut LBuilder, Vec<LVar>, LVar) -> LExpr>>)>, R: FnOnce() -> Rc<HExpr>>(this: &mut LBuilder, mut bindings: B, rest: R) -> LExpr {
      match bindings.next() {
        None => this._htree_to_ltree_lower_pass((rest)()),
        Some((name, ar, cg, adj)) => {
          let (_, var, label, bc) = this._alloc_bclambda(name, ar, cg, adj);
          let ltree = (bind_next)(this, bindings, rest);
          let ltree = (bind)(this._gen(), label, var, bc, ltree);
          ltree
        }
      }
    }
    let toplevel_bindings: Vec<(_, _, Rc<dyn Fn() -> VMBoxCode>, Option<Rc<dyn Fn(&mut LBuilder, Vec<LVar>, LVar) -> LExpr>>)> = vec![
      ("add", 2, Rc::new(|| make_bc_add()), Some(Rc::new(|lb, args, sink| make_adj_add(lb, args, sink)))),
      ("neg", 1, Rc::new(|| make_bc_neg()), Some(Rc::new(|lb, args, sink| make_adj_neg(lb, args, sink)))),
      ("sub", 2, Rc::new(|| make_bc_sub()), Some(Rc::new(|lb, args, sink| make_adj_sub(lb, args, sink)))),
      ("mul", 2, Rc::new(|| make_bc_mul()), Some(Rc::new(|lb, args, sink| make_adj_mul(lb, args, sink)))),
      ("div", 2, Rc::new(|| make_bc_div()), Some(Rc::new(|lb, args, sink| make_adj_div(lb, args, sink)))),
      ("eq",  2, Rc::new(|| make_bc_eq()), None),
      //("pi100", 0, Rc::new(|| make_bc_pi100()), None),
    ];
    let ltree = bind_next(
        self,
        toplevel_bindings.into_iter(),
        move || htree
    );
    ltree
  }

  pub fn lower_with_toplevel(&mut self, htree: Rc<HExpr>) -> LTree {
    self.gen_ctr += 1;
    let ltree = self._include_toplevel_and_lower(htree);
    LTree{
      info: LTreeInfo::default(),
      root: ltree,
    }
  }

  pub fn _htree_to_ltree_lower_pass_pat_rec(&mut self, htree: Rc<HExpr>, bindings: &mut Vec<(LHash, LVar, Option<LVar>)>) -> LPat {
    match &*htree {
      &HExpr::STuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|elem| {
          LPatRef::new(self._htree_to_ltree_lower_pass_pat_rec(elem.clone(), bindings))
        }).collect();
        LPat::STuple(elems)
      }
      &HExpr::Tuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|elem| {
          LPatRef::new(self._htree_to_ltree_lower_pass_pat_rec(elem.clone(), bindings))
        }).collect();
        LPat::Tuple(elems)
      }
      &HExpr::UnitLit => {
        LPat::UnitLit
      }
      &HExpr::TeeLit => {
        LPat::BitLit(true)
      }
      &HExpr::BotLit => {
        LPat::BitLit(false)
      }
      &HExpr::IntLit(x) => {
        LPat::IntLit(x)
      }
      /*&HExpr::FloatLit(x) => {
        LPat::FloLit(x)
      }*/
      &HExpr::PlacePat => {
        LPat::Place
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.hashes.lookup(name.to_string());
        let (name_hash, name_var, name_old_var) = self.vars.bind(name_hash);
        bindings.push((name_hash, name_var.clone(), name_old_var));
        LPat::Var(name_var)
      }
      _ => {
        panic!("syntax error: invalid pattern");
      }
    }
  }

  pub fn _htree_to_ltree_lower_pass_pat(&mut self, htree: Rc<HExpr>) -> (LPat, Vec<(LHash, LVar, Option<LVar>)>) {
    let mut bindings = vec![];
    let pat = self._htree_to_ltree_lower_pass_pat_rec(htree, &mut bindings);
    (pat, bindings)
  }

  pub fn _htree_to_ltree_lower_pass(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    match &*htree {
      &HExpr::End => {
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::End)}
      }
      &HExpr::Lambda(ref params, ref body) => {
        let mut param_vars = Vec::with_capacity(params.len());
        let mut saved_params = Vec::with_capacity(params.len());
        for p in params.iter() {
          let p_name = match &**p {
            &HExpr::Ident(ref p_name) => p_name.clone(),
            _ => panic!(),
          };
          let p_hash = self.hashes.lookup(p_name);
          let (p_hash, p_var, p_oldvar) = self.vars.bind(p_hash);
          param_vars.push(p_var.clone());
          saved_params.push((p_hash, p_var, p_oldvar));
        }
        let body = self._htree_to_ltree_lower_pass(body.clone());
        for (p_hash, p_var, p_oldvar) in saved_params.into_iter().rev() {
          self.vars.unbind(p_hash, p_var, p_oldvar);
        }
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lambda(param_vars, body)), /*info: LExprInfo::default()*/}
      }
      &HExpr::Apply(ref lhs, ref args) => {
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let args: Vec<_> = args.iter().map(|arg| {
          self._htree_to_ltree_lower_pass(arg.clone())
        }).collect();
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(lhs, args)), /*info: LExprInfo::default()*/}
      }
      &HExpr::STuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|elem| {
          self._htree_to_ltree_lower_pass(elem.clone())
        }).collect();
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::STuple(elems)), /*info: LExprInfo::default()*/}
      }
      &HExpr::Tuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|elem| {
          self._htree_to_ltree_lower_pass(elem.clone())
        }).collect();
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Tuple(elems)), /*info: LExprInfo::default()*/}
      }
      &HExpr::D(ref target) => {
        let target = self._htree_to_ltree_lower_pass(target.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::D(target))}
      }
      &HExpr::Adj(ref sink) => {
        let sink = self._htree_to_ltree_lower_pass(sink.clone());
        /*let sink_var = match &*sink.term {
          &LTerm::Lookup(ref v) => v.clone(),
          _ => panic!(),
        };*/
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Adj(sink)), /*info: LExprInfo::default()*/}
      }
      /*&HExpr::AdjDyn(ref body) => {
        // TODO
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::AdjDyn(body)), /*info: LExprInfo::default()*/}
      }*/
      &HExpr::Tng(ref sink) => {
        let sink = self._htree_to_ltree_lower_pass(sink.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Tng(sink))}
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        let attrs = maybe_attrs.clone().unwrap_or_default();
        match &**lhs {
          &HExpr::Ident(ref lhs) => {
            match attrs.rec {
              false => {
                let body = self._htree_to_ltree_lower_pass(body.clone());
                let lhs_hash = self.hashes.lookup(lhs.to_string());
                let (lhs_hash, lhs_var, lhs_oldvar) = self.vars.bind(lhs_hash);
                let rest = self._htree_to_ltree_lower_pass(rest.clone());
                self.vars.unbind(lhs_hash, lhs_var.clone(), lhs_oldvar);
                LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(lhs_var, body, rest)), /*info: LExprInfo::default()*/}
              }
              true  => {
                let lhs_hash = self.hashes.lookup(lhs.to_string());
                let (lhs_hash, lhs_var, lhs_oldvar) = self.vars.bind(lhs_hash);
                let (fixname_hash, fixname_var, fixname_oldvar) = self.vars.bind(lhs_hash.clone());
                let fixbody = self._htree_to_ltree_lower_pass(body.clone());
                let fix = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Fix(fixname_var.clone(), fixbody)), /*info: LExprInfo::default()*/};
                self.vars.unbind(fixname_hash, fixname_var, fixname_oldvar);
                let rest = self._htree_to_ltree_lower_pass(rest.clone());
                self.vars.unbind(lhs_hash, lhs_var.clone(), lhs_oldvar);
                LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(lhs_var, fix, rest)), /*info: LExprInfo::default()*/}
              }
            }
          }
          &HExpr::Apply(ref lhs, ref args) => {
            // FIXME: desugar "let rec" to "let fix in".
            match attrs.rec {
              false => {
                let mut args_ = vec![];
                let mut args_vars = vec![];
                let mut args_oldvars = vec![];
                for arg in args.iter() {
                  let (arg_, arg_var, arg_oldvar) = match &**arg {
                    &HExpr::Ident(ref name) => {
                      let arg_hash = self.hashes.lookup(name.to_string());
                      self.vars.bind(arg_hash)
                    }
                    _ => panic!(),
                  };
                  args_.push(arg_);
                  args_vars.push(arg_var);
                  args_oldvars.push(arg_oldvar);
                }
                let body = self._htree_to_ltree_lower_pass(body.clone());
                for ((arg_, arg_var), arg_oldvar) in args_.iter().zip(args_vars.iter()).zip(args_oldvars.iter()).rev() {
                  self.vars.unbind(arg_.clone(), arg_var.clone(), arg_oldvar.clone());
                }
                let lam = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lambda(args_vars, body)), /*info: LExprInfo::default()*/};
                let name_hash = match &**lhs {
                  &HExpr::Ident(ref name) => {
                    self.hashes.lookup(name.to_string())
                  }
                  _ => panic!(),
                };
                let (name, name_var, name_oldvar) = self.vars.bind(name_hash);
                let rest = self._htree_to_ltree_lower_pass(rest.clone());
                self.vars.unbind(name, name_var.clone(), name_oldvar);
                LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(name_var, lam, rest)), /*info: LExprInfo::default()*/}
              }
              true  => {
                unimplemented!();
              }
            }
          }
          _ => {
            panic!();
          }
        }
      }
      &HExpr::LetMatch(ref lhs, ref body, ref rest) => {
        // FIXME
        let body = self._htree_to_ltree_lower_pass(body.clone());
        let (pat, pat_bindings) = self._htree_to_ltree_lower_pass_pat(lhs.clone());
        let rest = self._htree_to_ltree_lower_pass(rest.clone());
        for (p_hash, p_var, p_old_var) in pat_bindings.into_iter().rev() {
          self.vars.unbind(p_hash, p_var, p_old_var);
        }
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Match(body, vec![(pat, rest)]))}
      }
      &HExpr::Switch(ref pred, ref top, ref bot) => {
        let pred = self._htree_to_ltree_lower_pass(pred.clone());
        let top = self._htree_to_ltree_lower_pass(top.clone());
        let bot = self._htree_to_ltree_lower_pass(bot.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Switch(pred, top, bot)), /*info: LExprInfo::default()*/}
      }
      &HExpr::Eq(ref lhs, ref rhs) => {
        let op_name = "eq".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), /*info: LExprInfo::default()*/}
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        let op_name = "add".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), /*info: LExprInfo::default()*/}
      }
      &HExpr::Sub(ref lhs, ref rhs) => {
        let op_name = "sub".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), /*info: LExprInfo::default()*/}
      }
      &HExpr::Mul(ref lhs, ref rhs) => {
        let op_name = "mul".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), /*info: LExprInfo::default()*/}
      }
      &HExpr::Div(ref lhs, ref rhs) => {
        let op_name = "div".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), /*info: LExprInfo::default()*/}
      }
      &HExpr::Neg(ref arg) => {
        let op_name = "neg".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), /*info: LExprInfo::default()*/};
        let arg = self._htree_to_ltree_lower_pass(arg.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![arg])), /*info: LExprInfo::default()*/}
      }
      &HExpr::NoRet => {
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::NoRet), /*info: LExprInfo::default()*/}
      }
      &HExpr::NonSmooth => {
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::NonSmooth), /*info: LExprInfo::default()*/}
      }
      &HExpr::UnitLit => {
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::UnitLit), /*info: LExprInfo::default()*/}
      }
      &HExpr::NilSTupLit => {
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::STuple(vec![])), /*info: LExprInfo::default()*/}
      }
      &HExpr::NilTupLit => {
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Tuple(vec![])), /*info: LExprInfo::default()*/}
      }
      &HExpr::BotLit => {
        // TODO: special var key for literal constants.
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::BitLit(false)), /*info: LExprInfo::default()*/}
      }
      &HExpr::TeeLit => {
        // TODO: special var key for literal constants.
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::BitLit(true)), /*info: LExprInfo::default()*/}
      }
      &HExpr::IntLit(x) => {
        // TODO: special var key for literal constants.
        //let var = self.vars.int_lit(x);
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::IntLit(x)), /*info: LExprInfo::default()*/}
      }
      &HExpr::FloatLit(x) => {
        // TODO: special var key for literal constants.
        //let var = self.vars.int_lit(x);
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::FloLit(x)), /*info: LExprInfo::default()*/}
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.hashes.lookup(name.to_string());
        let name_var = self.vars.lookup(name_hash);
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(name_var)), /*/*info: LExprInfo::default()*/*/}
      }
      &HExpr::PathLookup(ref lhs, ref rhs_name) => {
        /*let (name, name_var, name_oldvar) = self.vars.bind(name.to_string());
        //let body = self._htree_to_ltree_lower_pass(body.clone());
        let env = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Env), /*info: LExprInfo::default()*/};
        //let rest = self._htree_to_ltree_lower_pass(rest.clone());
        self.vars.unbind(name, name_var.clone(), name_oldvar);
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(name_var, body, rest)), /*info: LExprInfo::default()*/}*/
        // TODO
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        //LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::DynESelect(lhs, rhs_name.clone())), /*info: LExprInfo::default()*/}
        let rhs_hash = self.hashes.lookup(rhs_name.clone());
        LExpr{/*gen: self._gen(),*/ label: self.labels.fresh(), term: LTermRef::new(LTerm::EHashSelect(lhs, rhs_hash)), /*info: LExprInfo::default()*/}
      }
      _ => {
        // TODO
        unimplemented!();
      }
    }
  }

  pub fn lower(&mut self, htree: Rc<HExpr>) -> LTree {
    self.gen_ctr += 1;
    let ltree = self._htree_to_ltree_lower_pass(htree);
    LTree{
      info: LTreeInfo::default(),
      root: ltree,
    }
  }

  pub fn _ltree_normalize_pass_kont(&mut self, ltree: LExpr, kont: &mut dyn FnMut(&mut Self, LExpr) -> LExpr) -> LExpr {
    // TODO
    match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        self._ltree_normalize_pass_kont_name(head.clone(), &mut |this, head| {
          this._ltree_normalize_pass_kont_names(VecDeque::from(args.clone()), Vec::new(), &mut |this, args| {
            let new_ltree = LExpr{
              //gen:    this._gen(),
              label:  this.labels.fresh(),
              term:   LTermRef::new(LTerm::Apply(
                  head.clone(),
                  args,
              )),
            };
            kont(this, new_ltree)
          })
        })
      }
      &LTerm::D(ref target) => {
        self._ltree_normalize_pass_kont_name(target.clone(), &mut |this, target| {
          let new_ltree = LExpr{
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::D(target)),
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::Adj(ref sink) => {
        self._ltree_normalize_pass_kont_name(sink.clone(), &mut |this, sink| {
          let new_ltree = LExpr{
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Adj(sink)),
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::Tng(ref sink) => {
        self._ltree_normalize_pass_kont_name(sink.clone(), &mut |this, sink| {
          let new_ltree = LExpr{
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Tng(sink)),
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::AEnv(ref kvs) => {
        kont(self, ltree)
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        self._ltree_normalize_pass_kont_name(lhs.clone(), &mut |this, lhs| {
          this._ltree_normalize_pass_kont_name(rhs.clone(), &mut |this, rhs| {
            let new_ltree = LExpr{
              //gen:    this._gen(),
              label:  this.labels.fresh(),
              term:   LTermRef::new(LTerm::AConcat(
                  lhs.clone(),
                  rhs,
              ))
            };
            kont(this, new_ltree)
          })
        })
      }
      &LTerm::AApp(ref args, ref arg_adjs, ref env) => {
        self._ltree_normalize_pass_kont_name(env.clone(), &mut |this, env| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::AApp(
                args.clone(),
                arg_adjs.clone(),
                env,
            ))
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::ERet(ref params, ref env) => {
        self._ltree_normalize_pass_kont_name(env.clone(), &mut |this, env| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::ERet(
                params.clone(),
                env,
            ))
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::EHashSelect(ref tg_env, ref key_hash) => {
        self._ltree_normalize_pass_kont_name(tg_env.clone(), &mut |this, tg_env| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::EHashSelect(
                tg_env,
                key_hash.clone(),
            ))
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::ESelect(ref tg_env, ref key_name) => {
        self._ltree_normalize_pass_kont_name(tg_env.clone(), &mut |this, tg_env| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::ESelect(
                tg_env,
                key_name.clone(),
            ))
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._ltree_normalize_pass_kont_term(body.clone());
        let new_ltree = LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Lambda(
              params.clone(),
              body,
          )),
        };
        kont(self, new_ltree)
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        kont(self, ltree)
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        self._ltree_normalize_pass_kont(body.clone(), &mut |this, body| {
          let rest = this._ltree_normalize_pass_kont(rest.clone(), kont);
          LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Let(
                name.clone(),
                body,
                rest,
            )),
          }
        })
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        self._ltree_normalize_pass_kont_name(pred.clone(), &mut |this, pred| {
          let top = this._ltree_normalize_pass_kont_term(top.clone());
          let bot = this._ltree_normalize_pass_kont_term(bot.clone());
          let new_switch_expr = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Switch(
                pred,
                top,
                bot,
            )),
          };
          kont(this, new_switch_expr)
        })
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        self._ltree_normalize_pass_kont_name(query.clone(), &mut |this, query| {
          let pat_arms: Vec<_> = pat_arms.iter().map(|(p, a)| {
            (p.clone(), this._ltree_normalize_pass_kont_term(a.clone()))
          }).collect();
          let new_match_expr = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Match(
                query,
                pat_arms,
            )),
          };
          kont(this, new_match_expr)
        })
      }
      &LTerm::STuple(ref elems) => {
        self._ltree_normalize_pass_kont_names(VecDeque::from(elems.clone()), Vec::new(), &mut |this, elems| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::STuple(
                elems,
            )),
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::Tuple(ref elems) => {
        self._ltree_normalize_pass_kont_names(VecDeque::from(elems.clone()), Vec::new(), &mut |this, elems| {
          let new_ltree = LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Tuple(
                elems,
            )),
          };
          kont(this, new_ltree)
        })
      }
      &LTerm::UnitLit => {
        kont(self, ltree)
      }
      &LTerm::BitLit(_) => {
        kont(self, ltree)
      }
      &LTerm::IntLit(_) => {
        kont(self, ltree)
      }
      &LTerm::FloLit(_) => {
        kont(self, ltree)
      }
      &LTerm::Lookup(_) => {
        kont(self, ltree)
      }
      e => panic!("normalize: unimplemented ltree term: {:?}", e),
    }
  }

  pub fn _ltree_normalize_pass_kont_term(&mut self, ltree: LExpr) -> LExpr {
    self._ltree_normalize_pass_kont(ltree, &mut |_, ltree| ltree)
  }

  pub fn _ltree_normalize_pass_kont_names(&mut self, mut pre_ltrees: VecDeque<LExpr>, post_ltrees: Vec<LExpr>, kont: &mut dyn FnMut(&mut Self, Vec<LExpr>) -> LExpr) -> LExpr {
    match pre_ltrees.pop_front() {
      Some(ltree) => {
        self._ltree_normalize_pass_kont_name(ltree, &mut |this, ltree| {
          let pre_ltrees = pre_ltrees.clone();
          let mut post_ltrees = post_ltrees.clone();
          post_ltrees.push(ltree);
          this._ltree_normalize_pass_kont_names(pre_ltrees, post_ltrees, kont)
        })
      }
      None => {
        kont(self, post_ltrees)
      }
    }
  }

  pub fn _ltree_normalize_pass_kont_name(&mut self, ltree: LExpr, kont: &mut dyn FnMut(&mut Self, LExpr) -> LExpr) -> LExpr {
    self._ltree_normalize_pass_kont(ltree, &mut |this, new_ltree| {
      match &*new_ltree.term {
        &LTerm::BitLit(_) => {
          kont(this, new_ltree)
        }
        &LTerm::IntLit(_) => {
          kont(this, new_ltree)
        }
        &LTerm::FloLit(_) => {
          kont(this, new_ltree)
        }
        &LTerm::Lookup(_) => {
          kont(this, new_ltree)
        }
        &LTerm::AEnv(ref kvs) => {
          if kvs.is_empty() {
            kont(this, new_ltree)
          } else if kvs.len() == 1 {
            // FIXME: kind of a hacky case for `AConcat` to approx `ACons`.
            kont(this, new_ltree)
          } else {
            // FIXME
            /*let new_var = this.vars.fresh();
            LExpr{
              //gen:    this._gen(),
              label:  this.labels.fresh(),
              term:   LTermRef::new(LTerm::Let(
                  new_var.clone(),
                  new_ltree,
                  {
                    let new_var_expr = LExpr{
                      //gen:    this._gen(),
                      label:  this.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(new_var)),
                    };
                    kont(this, new_var_expr)
                  }
              )),
            }*/
            kont(this, new_ltree)
          }
        }
        &LTerm::STuple(ref elems) => {
          if elems.is_empty() {
            kont(this, new_ltree)
          } else {
            let new_var = this.vars.fresh();
            LExpr{
              //gen:    this._gen(),
              label:  this.labels.fresh(),
              term:   LTermRef::new(LTerm::Let(
                  new_var.clone(),
                  new_ltree,
                  {
                    let new_var_expr = LExpr{
                      //gen:    this._gen(),
                      label:  this.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(new_var)),
                    };
                    kont(this, new_var_expr)
                  }
              )),
            }
          }
        }
        &LTerm::Tuple(ref elems) => {
          if elems.is_empty() {
            kont(this, new_ltree)
          } else {
            let new_var = this.vars.fresh();
            LExpr{
              //gen:    this._gen(),
              label:  this.labels.fresh(),
              term:   LTermRef::new(LTerm::Let(
                  new_var.clone(),
                  new_ltree,
                  {
                    let new_var_expr = LExpr{
                      //gen:    this._gen(),
                      label:  this.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(new_var)),
                    };
                    kont(this, new_var_expr)
                  }
              )),
            }
          }
        }
        _ => {
          let new_var = this.vars.fresh();
          LExpr{
            //gen:    this._gen(),
            label:  this.labels.fresh(),
            term:   LTermRef::new(LTerm::Let(
                new_var.clone(),
                new_ltree,
                {
                  let new_var_expr = LExpr{
                    //gen:    this._gen(),
                    label:  this.labels.fresh(),
                    term:   LTermRef::new(LTerm::Lookup(new_var)),
                  };
                  kont(this, new_var_expr)
                }
            )),
          }
        }
      }
    })
  }

  pub fn normalize(&mut self, ltree: LTree) -> LTree {
    self.gen_ctr += 1;
    let root = self._ltree_normalize_pass_kont_term(ltree.root);
    LTree{
      info: LTreeInfo::default(),
      root,
    }
  }

  pub fn _ltree_close_lambdas_pass_substitute(&mut self, ltree: LExpr, env_param: LVar, closed_vars: &HashSet<LVar>) -> LExpr {
    match &*ltree.term {
      &LTerm::Lookup(ref var) => {
        match closed_vars.contains(var) {
          false => ltree.with_gen_rec(self._gen()),
          true  => LExpr{
            //gen:    self._gen(),
            label:  self.labels.fresh(),
            term:   LTermRef::new(LTerm::ESelect(
                LExpr{
                  //gen:      self._gen(),
                  label:    self.labels.fresh(),
                  term:     LTermRef::new(LTerm::Lookup(env_param)),
                },
                var.clone(),
            )),
          }
        }
      }
      //_ => ltree.with_gen_rec(self._gen()),
      _ => unimplemented!(),
    }
  }

  pub fn _ltree_close_lambdas_pass_lambda<'root>(&mut self, lroot: &'root LTree, ltree: LExpr) -> LExpr {
    match &*ltree.term {
      /*&LTerm::Apply(ref head, ref args) => {
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::ApplyEnv(
              head.with_gen_rec(self._gen()),
              args.iter().map(|a| a.with_gen_rec(self._gen())).collect(),
          )),
        }
      }*/
      &LTerm::Lambda(ref params, ref body) => {
        let fvars = ltree.free_env(lroot);
        /*let closed_env: Vec<_> = fvars.inner.ones().map(|v| {
          let v = LVar(v as u64);
          let h = self.vars.maybe_rev_lookup(v.clone());
          //let w = self.vars.fresh();
          (h, v)
        }).collect();*/
        let closed_env: Vec<_> = fvars.iter().map(|v| {
          let h = self.vars.maybe_rev_lookup(v.clone());
          //let w = self.vars.fresh();
          (h, v)
        }).collect();
        let env_param = self.vars.fresh();
        let mut closed_vars = HashSet::new();
        for &(_, /*ref w,*/ ref v) in closed_env.iter() {
          //closed_vars.insert(v.clone(), w.clone());
          closed_vars.insert(v.clone());
        }
        let new_body = self._ltree_close_lambdas_pass_substitute(body.clone(), env_param.clone(), &closed_vars);
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::LambdaEnv(
              closed_env,
              env_param,
              params.clone(),
              new_body,
          )),
        }
      }
      _ => ltree.with_gen_rec(self._gen()),
    }
  }

  pub fn _ltree_close_lambdas_pass<'root>(&mut self, lroot: &'root LTree, ltree: LExpr) -> LExpr {
    // TODO
    let tmp_ltree = match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        let head = self._ltree_close_lambdas_pass(lroot, head.clone());
        let args: Vec<_> = args.iter().map(|a| self._ltree_close_lambdas_pass(lroot, a.clone())).collect();
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Apply(
              head,
              args,
          )),
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._ltree_close_lambdas_pass(lroot, body.clone());
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Lambda(
              params.clone(),
              body,
          )),
        }
      }
      &LTerm::LambdaEnv(ref closed_env, ref env_param, ref params, ref body) => {
        let body = self._ltree_close_lambdas_pass(lroot, body.clone());
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::LambdaEnv(
              closed_env.clone(),
              env_param.clone(),
              params.clone(),
              body,
          )),
        }
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        let pred = self._ltree_close_lambdas_pass(lroot, pred.clone());
        let top = self._ltree_close_lambdas_pass(lroot, top.clone());
        let bot = self._ltree_close_lambdas_pass(lroot, bot.clone());
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Switch(
              pred,
              top,
              bot,
          )),
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let query = self._ltree_close_lambdas_pass(lroot, query.clone());
        let pat_arms: Vec<_> = pat_arms.iter().map(|(p, a)| {
          (p.clone(), self._ltree_close_lambdas_pass(lroot, a.clone()))
        }).collect();
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Match(
              query,
              pat_arms,
          )),
        }
      }
      &LTerm::Tuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|e| self._ltree_close_lambdas_pass(lroot, e.clone())).collect();
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Tuple(elems)),
        }
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        ltree.with_gen_rec(self._gen())
      }
      &LTerm::EHashSelect(ref target, ref hash) => {
        unreachable!();
      }
      &LTerm::ESelect(ref target, ref name) => {
        let target = self._ltree_close_lambdas_pass(lroot, target.clone());
        LExpr{
          //gen:      self._gen(),
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::ESelect(
              target,
              name.clone(),
          )),
        }
      }
      _ => {
        unimplemented!();
      }
    };
    self._ltree_close_lambdas_pass_lambda(lroot, tmp_ltree)
  }

  pub fn close_lambdas(&mut self, ltree: LTree) -> LTree {
    self.gen_ctr += 1;
    let root = self._ltree_close_lambdas_pass(&ltree, ltree.root.clone());
    LTree{
      info: LTreeInfo::default(),
      root,
    }
  }
}

impl LBuilder {
  pub fn rewrite_differential(&mut self, ltree: LTree) -> LTree {
    // TODO
    unimplemented!();
  }
}

#[derive(Default)]
struct AdjPassCtx {
  adj_map:  HashMap<LVar, LVar>,
  marked:   HashSet<LVar>,
  resolved: HashSet<LVar>,
}

impl LBuilder {
  fn _ltree_search_adj_sink_pass_binding<'root>(&mut self, lroot: &'root LTree, ctx: &mut AdjPassCtx, name: LVar, adj_name: LVar, body: LExpr, rest: LExpr) -> LExpr {
    match &*body.term {
      &LTerm::FloLit(_) => {
        let sink_param = self.vars.fresh();
        let new_body = LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::STuple(
              vec![
                body.with_gen_rec(self._gen()),
                LExpr{
                  //gen:    self._gen(),
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Lambda(
                      vec![sink_param],
                      LExpr{
                        //gen:    self._gen(),
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::AEnv(vec![]))
                      },
                  ))
                },
              ]
          ))
        };
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Match(
              new_body,
              vec![(
                LPat::STuple(vec![
                  LPatRef::new(LPat::Var(name.clone())),
                  LPatRef::new(LPat::Var(adj_name)),
                ]),
                rest,
              )],
          ))
        }
      }
      &LTerm::Lookup(ref var) => {
        if !ctx.marked.contains(var) {
          let adj_var = self.vars.fresh();
          ctx.adj_map.insert(var.clone(), adj_var);
          ctx.marked.insert(var.clone());
        }
        let adj_var = ctx.adj_map.get(var).unwrap().clone();
        let sink_param = self.vars.fresh();
        let new_body = LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::STuple(
              vec![
                body.with_gen_rec(self._gen()),
                LExpr{
                  //gen:    self._gen(),
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Lambda(
                      vec![sink_param.clone()],
                      LExpr{
                        //gen:    self._gen(),
                        label:  self.labels.fresh(),
                        //term:   LTermRef::new(LTerm::ACons(
                        term:   LTermRef::new(LTerm::AConcat(
                            LExpr{
                              //gen:    self._gen(),
                              label:  self.labels.fresh(),
                              term:   LTermRef::new(LTerm::AEnv(
                                  vec![(
                                    LEnvKey::Var(var.clone()),
                                    LExpr{
                                      //gen:    self._gen(),
                                      label:  self.labels.fresh(),
                                      term:   LTermRef::new(LTerm::Lookup(sink_param.clone()))
                                    },
                                  )]
                              ))
                            },
                            LExpr{
                              //gen:    self._gen(),
                              label:  self.labels.fresh(),
                              term:   LTermRef::new(LTerm::Apply(
                                  LExpr{
                                    //gen:    self._gen(),
                                    label:  self.labels.fresh(),
                                    term:   LTermRef::new(LTerm::Lookup(adj_var))
                                  },
                                  vec![
                                    LExpr{
                                      //gen:    self._gen(),
                                      label:  self.labels.fresh(),
                                      term:   LTermRef::new(LTerm::Lookup(sink_param))
                                    },
                                  ]
                              ))
                            },
                        ))
                      },
                  ))
                },
              ]
          ))
        };
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Match(
              new_body,
              vec![(
                LPat::STuple(vec![
                  LPatRef::new(LPat::Var(name.clone())),
                  LPatRef::new(LPat::Var(adj_name)),
                ]),
                rest,
              )],
          ))
        }
      }
      &LTerm::Lambda(ref params, ref lam_body) => {
        let new_lam_body_name = self.vars.fresh();
        let tmp_sink_param = self.vars.fresh();
        let new_lam_body = LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Let(
              new_lam_body_name.clone(),
              lam_body.clone(),
              LExpr{
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::STuple(
                    vec![
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(new_lam_body_name.clone()))
                      },
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lambda(
                            vec![tmp_sink_param.clone()],
                            LExpr{
                              label:  self.labels.fresh(),
                              term:   LTermRef::new(LTerm::ERet(
                                  params.clone(),
                                  LExpr{
                                    label:  self.labels.fresh(),
                                    term:   LTermRef::new(LTerm::Apply(
                                        LExpr{
                                          label:  self.labels.fresh(),
                                          term:   LTermRef::new(LTerm::Adj(
                                              LExpr{
                                                label:  self.labels.fresh(),
                                                term:   LTermRef::new(LTerm::Lookup(new_lam_body_name.clone()))
                                              }
                                          ))
                                        },
                                        vec![LExpr{
                                          label:  self.labels.fresh(),
                                          term:   LTermRef::new(LTerm::Lookup(tmp_sink_param))
                                        }],
                                    ))
                                  },
                              ))
                            },
                        ))
                      },
                    ]
                ))
              }
          ))
        };
        let new_lam = LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Lambda(
              params.clone(),
              new_lam_body,
          ))
        };
        let new_lam = self._ltree_normalize_pass_kont_term(new_lam);
        let new_lam = match self._ltree_search_adj_sink_pass_kont2(lroot, new_lam, ctx,
            &mut |_, _, new_lam, _| new_lam) {
          None => panic!("bug"),
          Some(new_lam) => new_lam,
        };
        let new_lam_params = match &*new_lam.term {
          &LTerm::Lambda(ref params, _) => params.clone(),
          _ => panic!("bug"),
        };
        let mut new_adj_lam_params = Vec::with_capacity(new_lam_params.len());
        for _ in 0 .. new_lam_params.len() {
          new_adj_lam_params.push(self.vars.fresh());
        }
        let tmp_fst_part_name = self.vars.fresh();
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Let(
              adj_name.clone(),
              new_lam,
              LExpr{
                //gen:    self._gen(),
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::Let(
                    name,
                    LExpr{
                      //gen:    self._gen(),
                      label:  self.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lambda(
                          new_adj_lam_params.clone(),
                          LExpr{
                            //gen:    self._gen(),
                            label:  self.labels.fresh(),
                            term:   LTermRef::new(LTerm::Match(
                                LExpr{
                                  //gen:    self._gen(),
                                  label:  self.labels.fresh(),
                                  term:   LTermRef::new(LTerm::Apply(
                                      LExpr{
                                        //gen:    self._gen(),
                                        label:  self.labels.fresh(),
                                        term:   LTermRef::new(LTerm::Lookup(adj_name))
                                      },
                                      new_adj_lam_params.iter().map(|p| {
                                        LExpr{
                                          //gen:    self._gen(),
                                          label:  self.labels.fresh(),
                                          term:   LTermRef::new(LTerm::Lookup(p.clone()))
                                        }
                                      }).collect(),
                                  ))
                                },
                                vec![(
                                  LPat::STuple(vec![
                                    LPatRef::new(LPat::Var(tmp_fst_part_name.clone())),
                                    LPatRef::new(LPat::Var(self.vars.fresh())),
                                  ]),
                                  LExpr{
                                    //gen:    self._gen(),
                                    label:  self.labels.fresh(),
                                    term:   LTermRef::new(LTerm::Lookup(tmp_fst_part_name))
                                  }
                                )]
                            ))
                          }
                      ))
                    },
                    rest,
                ))
              }
          ))
        }
      }
      &LTerm::VMExt(LVMExt::BCLambda(ref bcp, ref bcdef)) => {
        // FIXME: preserve the original lam type (only introduce a new adj ty).
        let mut new_adj_params = vec![]; // FIXME
        for _ in 0 .. bcdef.ar {
          new_adj_params.push(self.vars.fresh());
        }
        let tmp_sink_param = self.vars.fresh();
        let new_adj_lam_body = LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::STuple(
              vec![
                LExpr{
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Apply(
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(name.clone()))
                      },
                      new_adj_params.iter().map(|ap| LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(ap.clone()))
                      }).collect(),
                  ))
                },
                LExpr{
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Lambda(
                      vec![tmp_sink_param.clone()],
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::ERet(
                            new_adj_params.clone(),
                            match bcdef.adj {
                              None => panic!(),
                              Some(ref adj) => {
                                (adj)(self, new_adj_params.clone(), tmp_sink_param)
                              }
                            }
                        ))
                      },
                  ))
                },
              ]
          ))
        };
        LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Let(
              name.clone(),
              body.clone(),
              LExpr{
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::Let(
                    adj_name.clone(),
                    LExpr{
                      label:  self.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lambda(
                          new_adj_params,
                          new_adj_lam_body,
                      ))
                    },
                    rest,
                ))
              }
          ))
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        let head_var = match &*head.term {
          &LTerm::Lookup(ref head_var) => head_var.clone(),
          _ => unimplemented!(),
        };
        if !ctx.marked.contains(&head_var) {
          let adj_head_var = self.vars.fresh();
          ctx.adj_map.insert(head_var.clone(), adj_head_var);
          ctx.marked.insert(head_var.clone());
        }
        // TODO: apply the arg adjs at the call conversion (`AApp`),
        // not in the callsite itself.
        let mut arg_vars = Vec::with_capacity(args.len());
        let mut arg_adjs = Vec::with_capacity(args.len());
        for (arg_idx, arg) in args.iter().enumerate() {
          match &*arg.term {
            // FIXME: literal args.
            &LTerm::Lookup(ref arg_var) => {
              arg_vars.push(arg_var.clone());
              if !ctx.marked.contains(&arg_var) {
                let adj_arg_var = self.vars.fresh();
                ctx.adj_map.insert(arg_var.clone(), adj_arg_var);
                ctx.marked.insert(arg_var.clone());
              }
              let arg_adj = ctx.adj_map.get(arg_var).unwrap().clone();
              arg_adjs.push(arg_adj.clone());
            }
            _ => unimplemented!(),
          }
        }
        let adj_head_var = ctx.adj_map.get(&head_var).unwrap().clone();
        let tmp_adj_part_name = self.vars.fresh();
        let tmp_sink_param = self.vars.fresh();
        let mut adj_app = LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::AApp(
              arg_vars.clone(),
              arg_adjs.clone(),
              LExpr{
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::Apply(
                    LExpr{
                      label:  self.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(tmp_adj_part_name.clone()))
                    },
                    vec![LExpr{
                      label:  self.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(tmp_sink_param.clone()))
                    }],
                ))
              }
          ))
        };
        for a_adj in arg_adjs.iter().rev() {
          // FIXME: Note this assumes that the parameter is of
          // non-function type.
          adj_app = LExpr{
            label:  self.labels.fresh(),
            term:   LTermRef::new(LTerm::AConcat(
                LExpr{
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Apply(
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(a_adj.clone()))
                      },
                      vec![
                        LExpr{
                          label:  self.labels.fresh(),
                          term:   LTermRef::new(LTerm::Lookup(tmp_sink_param.clone()))
                        },
                      ]
                  ))
                },
                adj_app,
            ))
          };
        }
        LExpr{
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Match(
              LExpr{
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::Apply(
                    LExpr{
                      label:  self.labels.fresh(),
                      term:   LTermRef::new(LTerm::Lookup(adj_head_var))
                    },
                    arg_vars.iter().map(|arg_var| {
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(arg_var.clone()))
                      }
                    }).collect(),
                ))
              },
              vec![(
                LPat::STuple(vec![
                  LPatRef::new(LPat::Var(name.clone())),
                  LPatRef::new(LPat::Var(tmp_adj_part_name.clone())),
                ]),
                LExpr{
                  label:  self.labels.fresh(),
                  term:   LTermRef::new(LTerm::Let(
                      adj_name.clone(),
                      LExpr{
                        label:  self.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lambda(
                            vec![tmp_sink_param.clone()],
                            /*LExpr{
                              label:  self.labels.fresh(),
                              term:   LTermRef::new(LTerm::AApp(
                                  arg_vars,
                                  arg_adjs,
                                  LExpr{
                                    label:  self.labels.fresh(),
                                    term:   LTermRef::new(LTerm::Apply(
                                        LExpr{
                                          label:  self.labels.fresh(),
                                          term:   LTermRef::new(LTerm::Lookup(tmp_adj_part_name))
                                        },
                                        vec![LExpr{
                                          label:  self.labels.fresh(),
                                          term:   LTermRef::new(LTerm::Lookup(tmp_sink_param))
                                        }],
                                    ))
                                  }
                              ))
                            }*/
                            adj_app
                        ))
                      },
                      rest,
                  ))
                }
              )]
          ))
        }
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        // FIXME
        unimplemented!();
      }
      _ => unimplemented!(),
    }
  }

  fn _ltree_search_adj_sink_pass_kont2<'root>(&mut self, lroot: &'root LTree, ltree: LExpr, ctx: &mut AdjPassCtx, kont: &mut FnMut(&mut Self, &'root LTree, LExpr, &mut AdjPassCtx) -> LExpr) -> Option<LExpr> {
    // TODO
    match &*ltree.term {
      &LTerm::Adj(ref sink) => {
        match &*sink.term {
          &LTerm::UnitLit |
          &LTerm::BitLit(_) |
          &LTerm::IntLit(_) => {
            panic!("bug: adj of nonsmooth literal");
          }
          &LTerm::FloLit(_) => {
            self.gen_ctr += 1;
            let new_ltree = LExpr{
              label:    self.labels.fresh(),
              term:     LTermRef::new(LTerm::FloLit(0.0)) // FIXME
            };
            Some(kont(self, lroot, new_ltree, ctx))
          }
          &LTerm::Lookup(ref sink_var) => {
            self.gen_ctr += 1;
            let sink_adj = if !ctx.marked.contains(sink_var) {
              let sink_adj = self.vars.fresh();
              ctx.adj_map.insert(sink_var.clone(), sink_adj.clone());
              ctx.marked.insert(sink_var.clone());
              sink_adj
            } else {
              ctx.adj_map.get(sink_var).unwrap().clone()
            };
            let new_ltree = LExpr{
              label:    self.labels.fresh(),
              term:     LTermRef::new(LTerm::Lookup(sink_adj))
            };
            Some(kont(self, lroot, new_ltree, ctx))
          }
          _ => panic!("bug: adj search must follow normalization pass"),
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        // TODO: returning `None` on this case assumes normalized lexpr.
        /*self._ltree_search_adj_sink_pass_kont2(lroot, head.clone(), ctx,
            &mut |_, _, head, _| unimplemented!());*/
        None
      }
      &LTerm::Lambda(ref params, ref body) => {
        self._ltree_search_adj_sink_pass_kont2(lroot, body.clone(), ctx,
            &mut |this, lroot, body, ctx| {
              let mut new_params = Vec::with_capacity(params.len());
              let mut new_matches = HashMap::new();
              for p in params.iter() {
                if ctx.marked.contains(p) {
                  if ctx.resolved.contains(p) {
                    panic!("bug");
                  }
                  let adj_param = ctx.adj_map.get(p).unwrap();
                  ctx.resolved.insert(p.clone());
                  let new_param = this.vars.fresh();
                  new_params.push(new_param.clone());
                  new_matches.insert(new_param.clone(), (p.clone(), Some(adj_param.clone())));
                } else {
                  if ctx.resolved.contains(p) {
                    panic!("double bug");
                  }
                  let adj_param = this.vars.fresh();
                  ctx.adj_map.insert(p.clone(), adj_param.clone());
                  ctx.marked.insert(p.clone());
                  ctx.resolved.insert(p.clone());
                  let new_param = this.vars.fresh();
                  new_params.push(new_param.clone());
                  new_matches.insert(new_param.clone(), (p.clone(), None));
                }
              }
              let mut new_body = body;
              for np in new_params.iter().rev() {
                match new_matches.get(np) {
                  None => panic!(),
                  Some(&(ref p, Some(ref adj_p))) => {
                    // FIXME: Note this assumes that the parameter is of
                    // non-function type.
                    let tmp_sink_param = this.vars.fresh();
                    new_body = LExpr{
                      label:  this.labels.fresh(),
                      term:   LTermRef::new(LTerm::Let(
                          adj_p.clone(),
                          LExpr{
                            label:  this.labels.fresh(),
                            term:   LTermRef::new(LTerm::Lambda(
                                vec![tmp_sink_param],
                                LExpr{
                                  label:  this.labels.fresh(),
                                  term:   LTermRef::new(LTerm::AEnv(Vec::new()))
                                },
                            ))
                          },
                          new_body,
                      ))
                    };
                    /*new_body = LExpr{
                      label:    this.labels.fresh(),
                      term:     LTermRef::new(LTerm::Match(
                          LExpr{
                            label:  this.labels.fresh(),
                            term:   LTermRef::new(LTerm::Lookup(np.clone()))
                          },
                          vec![(
                            LPat::STuple(vec![
                              LPatRef::new(LPat::Var(p.clone())),
                              LPatRef::new(LPat::Var(adj_p.clone())),
                            ]),
                            new_body,
                          )],
                      ))
                    };*/
                  }
                  Some(&(ref p, None)) => {
                    /*new_body = LExpr{
                      label:    this.labels.fresh(),
                      term:     LTermRef::new(LTerm::Match(
                          LExpr{
                            label:  this.labels.fresh(),
                            term:   LTermRef::new(LTerm::Lookup(np.clone()))
                          },
                          vec![(
                            LPat::STuple(vec![
                              LPatRef::new(LPat::Var(p.clone())),
                              LPatRef::new(LPat::Var(this.vars.fresh())),
                            ]),
                            new_body,
                          )],
                      ))
                    };*/
                  }
                }
              }
              let new_ltree = LExpr{
                label:  this.labels.fresh(),
                term:   LTermRef::new(LTerm::Lambda(
                    params.clone(),
                    /*new_params,*/
                    new_body,
                ))
              };
              kont(this, lroot, new_ltree, ctx)
            }
        )
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        // FIXME
        //unimplemented!();
        /*self._ltree_search_adj_sink_pass_kont2(lroot, body.clone(), ctx,
            &mut |this, lroot, body, ctx| {
            }
        )*/
        None
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        match self._ltree_search_adj_sink_pass_kont2(lroot, body.clone(), ctx,
            &mut |this, lroot, body, ctx| {
              let new_ltree = LExpr{
                //gen:    this._gen(),
                label:  this.labels.fresh(),
                term:   LTermRef::new(LTerm::Let(
                    name.clone(),
                    body,
                    //rest.with_gen_rec(this._gen()),
                    rest.clone(),
                ))
              };
              kont(this, lroot, new_ltree, ctx)
            }
        ) {
          None => {}
          Some(ltree) => return Some(ltree),
        }
        match self._ltree_search_adj_sink_pass_kont2(lroot, rest.clone(), ctx,
            &mut |this, lroot, rest, ctx| {
              let new_ltree = if ctx.marked.contains(name) {
                if ctx.resolved.contains(name) {
                  panic!("bug");
                }
                let adj_name = ctx.adj_map.get(name).unwrap().clone();
                ctx.resolved.insert(name.clone());
                this._ltree_search_adj_sink_pass_binding(lroot, ctx, name.clone(), adj_name, body.clone(), rest)
              } else {
                LExpr{
                  //gen:    this._gen(),
                  label:  this.labels.fresh(),
                  term:   LTermRef::new(LTerm::Let(
                      name.clone(),
                      //body.with_gen_rec(this._gen()),
                      body.clone(),
                      rest,
                  ))
                }
              };
              kont(this, lroot, new_ltree, ctx)
            }
        ) {
          None => {}
          Some(ltree) => return Some(ltree),
        }
        None
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        // FIXME
        unimplemented!();
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // FIXME
        unimplemented!();
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        None
      }
      _ => unimplemented!(),
    }
  }

  fn _ltree_fixup_adj_app_pass_kont2<'root>(&mut self, lroot: &'root LTree, ltree: LExpr, ctx: &mut AdjPassCtx, kont: &mut FnMut(&mut Self, &'root LTree, LExpr, &mut AdjPassCtx) -> LExpr) -> Option<LExpr> {
    // FIXME
    unimplemented!();
  }

  pub fn expand_adj(&mut self, ltree: LTree) -> LTree {
    let mut ltree = ltree;
    // FIXME
    //loop {
      match self._ltree_search_adj_sink_pass_kont2(&ltree, ltree.root.clone(), &mut AdjPassCtx::default(), &mut |_, _, ltree, _| ltree) {
        None => return ltree,
        Some(root) => {
          ltree = LTree{
            info: LTreeInfo::default(),
            root,
          };
        }
      }
    //}
    ltree
  }
}

impl LBuilder {
  fn _ltree_resolve_ty_inf_pass(&mut self, ltree: LExpr, ty_inf: &SimpleTyInferenceMachine) -> LExpr {
    match &*ltree.term {
      &LTerm::EHashSelect(ref tg_env, ref key_hash) => {
        let tg_env = self._ltree_resolve_ty_inf_pass(tg_env.clone(), ty_inf);
        match ty_inf._find_tree_pty(&ltree) {
          Some(ty) => match ty {
            Ty::ESel(_, ref tyinf_key_var, ref tyinf_key_hash) => {
              assert_eq!(tyinf_key_hash, key_hash);
              LExpr{
                //gen:    self._gen(),
                label:  self.labels.fresh(),
                term:   LTermRef::new(LTerm::ESelect(
                    tg_env,
                    tyinf_key_var.clone(),
                ))
              }
            }
            _ => panic!(),
          },
          None => panic!(),
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        let head = self._ltree_resolve_ty_inf_pass(head.clone(), ty_inf);
        let args: Vec<_> = args.iter().map(|a| self._ltree_resolve_ty_inf_pass(a.clone(), ty_inf)).collect();
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Apply(
              head,
              args,
          ))
        }
      }
      &LTerm::AEnv(ref kvs) => {
        let kvs = kvs.iter().map(|&(ref k, ref v)| (k.clone(), self._ltree_resolve_ty_inf_pass(v.clone(), ty_inf))).collect();
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::AEnv(
              kvs,
          ))
        }
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        let lhs = self._ltree_resolve_ty_inf_pass(lhs.clone(), ty_inf);
        let rhs = self._ltree_resolve_ty_inf_pass(rhs.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::AConcat(
              lhs,
              rhs,
          ))
        }
      }
      &LTerm::AApp(ref args, ref arg_adjs, ref env) => {
        let env = self._ltree_resolve_ty_inf_pass(env.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::AApp(
              args.clone(),
              arg_adjs.clone(),
              env,
          ))
        }
      }
      &LTerm::ERet(ref params, ref env) => {
        let env = self._ltree_resolve_ty_inf_pass(env.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::ERet(
              params.clone(),
              env,
          ))
        }
      }
      &LTerm::ESelect(ref tg_env, ref key_var) => {
        let tg_env = self._ltree_resolve_ty_inf_pass(tg_env.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::ESelect(
              tg_env,
              key_var.clone(),
          ))
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._ltree_resolve_ty_inf_pass(body.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Lambda(
              params.clone(),
              body,
          ))
        }
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        // FIXME
        ltree
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = self._ltree_resolve_ty_inf_pass(body.clone(), ty_inf);
        let rest = self._ltree_resolve_ty_inf_pass(rest.clone(), ty_inf);
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Let(
              name.clone(),
              body,
              rest,
          ))
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let query = self._ltree_resolve_ty_inf_pass(query.clone(), ty_inf);
        let pat_arms: Vec<_> = pat_arms.iter().map(|&(ref p, ref a)| (p.clone(), self._ltree_resolve_ty_inf_pass(a.clone(), ty_inf))).collect();
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::Match(
              query,
              pat_arms,
          ))
        }
      }
      &LTerm::STuple(ref elems) => {
        let elems: Vec<_> = elems.iter().map(|e| self._ltree_resolve_ty_inf_pass(e.clone(), ty_inf)).collect();
        LExpr{
          //gen:    self._gen(),
          label:  self.labels.fresh(),
          term:   LTermRef::new(LTerm::STuple(
              elems,
          ))
        }
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FloLit(_) |
      &LTerm::Lookup(_) => {
        ltree
      }
      _ => unimplemented!(),
    }
  }

  pub fn resolve_ty_inf(&mut self, ltree: LTree) -> LTree {
    let mut ty_inf = SimpleTyInferenceMachine::default();
    ty_inf.gen(ltree.root.clone());
    let ty_res = ty_inf.solve(self);
    // TODO
    match ty_res {
      Err(_) => panic!(),
      Ok(_) => {}
    }
    let root = self._ltree_resolve_ty_inf_pass(ltree.root.clone(), &ty_inf);
    LTree{
      info: LTreeInfo::default(),
      root,
    }
  }
}

type TyRef = Rc<Ty>;

#[derive(Clone, PartialEq, Eq, Debug)]
enum Ty {
  Tyvar(u64),
  Boxty(LBoxty),
  //AEnv(Vec<LVar>, HashMap<LHash, LVar>),
  //AEnvFlat(HashSet<LEnvKey>, HashMap<LHash, LVar>),
  AEnvNil,
  ACons(LEnvKey, TyRef, TyRef),
  AConcat(TyRef, TyRef),
  AApp(Vec<LVar>, Vec<LVar>, TyRef),
  ERet(Vec<LVar>, TyRef),
  EHashSel(TyRef, LHash),
  ESel(TyRef, LVar, LHash),
  Fun(Vec<TyRef>, TyRef),
  STup(Vec<TyRef>),
  Tup,
  Bit,
  Int,
  Flo,
}

struct TyHypothesis {
  ltree:    LExpr,
  ty:       Ty,
  venv:     HashMap<LVar, Ty>,
}

enum TyConstraint {
  Eq(Ty, Ty),
  IsaEnvSelByKeyHash(Ty, Ty, LHash),
  IsaEnvSelByKeyHash2(Ty, Ty, Ty, LHash),
  //IsaEnvSelByKeyHash2(Ty, Ty, VecDeque<Ty>, LHash),
}

#[derive(Default)]
pub struct PreAdjTyInferenceMachine {
  tyvar_ctr:    u64,
  tree_tyvars:  HashMap<LLabel, u64>,
  bound_tyvars: HashMap<LVar, u64>,
  hypotheses:   VecDeque<TyHypothesis>,
  constraints:  VecDeque<TyConstraint>,
  // FIXME: use a proper union-find data structure.
  substitution: HashMap<u64, Ty>,
}

#[derive(Default)]
pub struct SimpleTyInferenceMachine {
  tyvar_ctr:    u64,
  tree_tyvars:  HashMap<LLabel, u64>,
  bound_tyvars: HashMap<LVar, u64>,
  hypotheses:   VecDeque<TyHypothesis>,
  constraints:  VecDeque<TyConstraint>,
  // FIXME: use a proper union-find data structure.
  substitution: HashMap<u64, Ty>,
}

impl SimpleTyInferenceMachine {
  fn _find_tree_pty(&self, ltree: &LExpr) -> Option<Ty> {
    match self.tree_tyvars.get(&ltree.label) {
      None => return None,
      Some(&v) => {
        Self::_find_pty(&self.substitution, v)
      }
    }
  }

  fn _tree_tyvar(&mut self, ltree: &LExpr) -> Ty {
    if self.tree_tyvars.contains_key(&ltree.label) {
      return Ty::Tyvar(*self.tree_tyvars.get(&ltree.label).unwrap());
    }
    self.tyvar_ctr += 1;
    assert!(self.tyvar_ctr != 0);
    self.tree_tyvars.insert(ltree.label.clone(), self.tyvar_ctr);
    Ty::Tyvar(self.tyvar_ctr)
  }

  fn _bound_tyvar(&mut self, var: LVar) -> Ty {
    if self.bound_tyvars.contains_key(&var) {
      return Ty::Tyvar(*self.bound_tyvars.get(&var).unwrap());
    }
    self.tyvar_ctr += 1;
    assert!(self.tyvar_ctr != 0);
    self.bound_tyvars.insert(var, self.tyvar_ctr);
    Ty::Tyvar(self.tyvar_ctr)
  }

  fn _anon_tyvar(&mut self) -> Ty {
    self.tyvar_ctr += 1;
    assert!(self.tyvar_ctr != 0);
    Ty::Tyvar(self.tyvar_ctr)
  }

  fn _pat_ty_rec(&mut self, pat: &LPat, tyvars: &mut Vec<(LVar, Ty)>) -> Ty {
    match pat {
      &LPat::STuple(ref elems) => {
        Ty::STup(elems.iter().map(|e| TyRef::new(self._pat_ty_rec(e, tyvars))).collect())
      }
      &LPat::Tuple(_) => {
        Ty::Tup
      }
      &LPat::BitLit(_) => {
        Ty::Bit
      }
      &LPat::IntLit(_) => {
        Ty::Int
      }
      /*&LPat::FloLit(_) => {
        Ty::Flo
      }*/
      &LPat::Place => {
        // FIXME: create an anon `LVar`, then create corresponding bound tyvar.
        let ty = self._anon_tyvar();
        //tyvars.push((tmp_var.clone(), ty.clone()));
        ty
      }
      &LPat::Var(ref var) => {
        let ty = self._bound_tyvar(var.clone());
        tyvars.push((var.clone(), ty.clone()));
        ty
      }
      _ => {
        panic!("_pat_ty: unimplemented lpat: {:?}", pat);
      }
    }
  }

  fn _pat_ty(&mut self, pat: &LPat) -> (Ty, Vec<(LVar, Ty)>) {
    let mut tyvars = Vec::new();
    let ty = self._pat_ty_rec(pat, &mut tyvars);
    (ty, tyvars)
  }

  fn _reset(&mut self, ltree: LExpr) {
    let ty = self._tree_tyvar(&ltree);
    self.hypotheses.clear();
    self.hypotheses.push_back(TyHypothesis{
      ltree,
      ty,
      venv: HashMap::new(),
    });
  }

  fn _step(&mut self) -> bool {
    match self.hypotheses.pop_front() {
      None => {
        true
      }
      Some(ref hyp) => {
        match &*hyp.ltree.term {
          &LTerm::Apply(ref head, ref args) => {
            let mut args_tys = Vec::with_capacity(args.len());
            for a in args.iter() {
              let a_ty_v = self._tree_tyvar(a);
              args_tys.push(TyRef::new(a_ty_v));
            }
            self.hypotheses.push_front(TyHypothesis{
              ltree:    head.clone(),
              ty:       Ty::Fun(args_tys, TyRef::new(hyp.ty.clone())),
              venv:     hyp.venv.clone(),
            });
            for a in args.iter() {
              let a_ty_v = self._tree_tyvar(a);
              self.hypotheses.push_back(TyHypothesis{
                ltree:  a.clone(),
                ty:     a_ty_v,
                venv:   hyp.venv.clone(),
              });
            }
          }
          &LTerm::AEnv(ref kvs) => {
            if kvs.is_empty() {
              self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::AEnvNil));
            } else if kvs.len() == 1 {
              let v_ty_v = self._tree_tyvar(&kvs[0].1);
              self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::ACons(kvs[0].0.clone(), TyRef::new(v_ty_v.clone()), TyRef::new(Ty::AEnvNil))));
              self.hypotheses.push_front(TyHypothesis{
                ltree:  kvs[0].1.clone(),
                ty:     v_ty_v,
                venv:   hyp.venv.clone(),
              });
            } else {
              panic!("bug: unimplemented tyinf on large AEnv");
            }
          }
          &LTerm::AConcat(ref lhs, ref rhs) => {
            match &*lhs.term {
              &LTerm::AEnv(ref lhs_kvs) => {
                let rhs_ty_v = self._tree_tyvar(rhs);
                if lhs_kvs.is_empty() {
                  self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), rhs_ty_v.clone()));
                  self.hypotheses.push_front(TyHypothesis{
                    ltree:  rhs.clone(),
                    ty:     rhs_ty_v,
                    venv:   hyp.venv.clone(),
                  });
                } else if lhs_kvs.len() == 1 {
                  let lhs_ty_v = self._tree_tyvar(&lhs_kvs[0].1);
                  self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::ACons(lhs_kvs[0].0.clone(), TyRef::new(lhs_ty_v.clone()), TyRef::new(rhs_ty_v.clone()))));
                  self.hypotheses.push_front(TyHypothesis{
                    ltree:  rhs.clone(),
                    ty:     rhs_ty_v,
                    venv:   hyp.venv.clone(),
                  });
                  self.hypotheses.push_back(TyHypothesis{
                    ltree:  lhs_kvs[0].1.clone(),
                    ty:     lhs_ty_v,
                    venv:   hyp.venv.clone(),
                  });
                } else {
                  panic!("bug: unimplemented tyinf on large AEnv");
                }
              }
              _ => {
                let lhs_ty_v = self._tree_tyvar(lhs);
                let rhs_ty_v = self._tree_tyvar(rhs);
                self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::AConcat(TyRef::new(lhs_ty_v.clone()), TyRef::new(rhs_ty_v.clone()))));
                self.hypotheses.push_front(TyHypothesis{
                  ltree:    lhs.clone(),
                  ty:       lhs_ty_v,
                  venv:     hyp.venv.clone(),
                });
                self.hypotheses.push_front(TyHypothesis{
                  ltree:    rhs.clone(),
                  ty:       rhs_ty_v,
                  venv:     hyp.venv.clone(),
                });
              }
            }
          }
          &LTerm::AApp(ref arg_vars, ref arg_adjs, ref env) => {
            let env_ty_v = self._tree_tyvar(env);
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::AApp(arg_vars.clone(), arg_adjs.clone(), TyRef::new(env_ty_v.clone()))));
            self.hypotheses.push_front(TyHypothesis{
              ltree:    env.clone(),
              ty:       env_ty_v,
              venv:     hyp.venv.clone(),
            });
          }
          &LTerm::ERet(ref params, ref env) => {
            let env_ty_v = self._tree_tyvar(env);
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::ERet(params.clone(), TyRef::new(env_ty_v.clone()))));
            self.hypotheses.push_front(TyHypothesis{
              ltree:    env.clone(),
              ty:       env_ty_v,
              venv:     hyp.venv.clone(),
            });
          }
          &LTerm::EHashSelect(ref tg_env, ref key_hash) => {
            let tg_env_ty_v = self._tree_tyvar(tg_env);
            //self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::EHashSel(TyRef::new(tg_env_ty_v.clone()), key_hash.clone())));
            self.constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(hyp.ty.clone(), tg_env_ty_v.clone(), key_hash.clone()));
            self.hypotheses.push_front(TyHypothesis{
              ltree:    tg_env.clone(),
              ty:       tg_env_ty_v,
              venv:     hyp.venv.clone(),
            });
          }
          &LTerm::ESelect(ref tg_env, ref key) => {
            unimplemented!();
          }
          &LTerm::Lambda(ref params, ref body) => {
            let mut body_venv = hyp.venv.clone();
            let mut params_tys = Vec::with_capacity(params.len());
            for p in params.iter() {
              let p_ty_v = self._bound_tyvar(p.clone());
              body_venv.insert(p.clone(), p_ty_v.clone());
              params_tys.push(TyRef::new(p_ty_v));
            }
            let body_ty_v = self._tree_tyvar(body);
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::Fun(params_tys, TyRef::new(body_ty_v.clone()))));
            self.hypotheses.push_front(TyHypothesis{
              ltree:    body.clone(),
              ty:       body_ty_v,
              venv:     body_venv,
            });
          }
          &LTerm::VMExt(LVMExt::BCLambda(..)) => {
            // FIXME
          }
          &LTerm::Let(ref name, ref body, ref rest) => {
            let name_ty_v = self._bound_tyvar(name.clone());
            let body_ty_v = self._tree_tyvar(body);
            let rest_ty_v = self._tree_tyvar(rest);
            let mut rest_venv = hyp.venv.clone();
            rest_venv.insert(name.clone(), name_ty_v.clone());
            self.constraints.push_back(TyConstraint::Eq(name_ty_v, body_ty_v.clone()));
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), rest_ty_v.clone()));
            self.hypotheses.push_front(TyHypothesis{
              ltree:    body.clone(),
              ty:       body_ty_v,
              venv:     hyp.venv.clone(),
            });
            self.hypotheses.push_back(TyHypothesis{
              ltree:    rest.clone(),
              ty:       rest_ty_v,
              venv:     rest_venv,
            });
          }
          &LTerm::Match(ref query, ref pat_arms) => {
            if pat_arms.is_empty() {
              panic!("bug");
            } else if pat_arms.len() == 1 {
              // TODO
              let pat = &pat_arms[0].0;
              let arm = &pat_arms[0].1;
              let query_ty_v = self._tree_tyvar(query);
              let (pat_ty, pat_tyvars) = self._pat_ty(pat);
              let arm_ty_v = self._tree_tyvar(arm);
              let mut arm_venv = hyp.venv.clone();
              for (pv, p_tv) in pat_tyvars.into_iter() {
                arm_venv.insert(pv, p_tv);
              }
              self.constraints.push_back(TyConstraint::Eq(query_ty_v.clone(), pat_ty.clone()));
              self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), arm_ty_v.clone()));
              self.hypotheses.push_front(TyHypothesis{
                ltree:    query.clone(),
                ty:       query_ty_v,
                venv:     hyp.venv.clone(),
              });
              self.hypotheses.push_back(TyHypothesis{
                ltree:    arm.clone(),
                ty:       arm_ty_v,
                venv:     arm_venv,
              });
            } else {
              // FIXME
              unimplemented!();
            }
          }
          &LTerm::STuple(ref elems) => {
            // TODO
            let mut elems_tys = Vec::new();
            for e in elems.iter() {
              let e_ty_v = self._tree_tyvar(e);
              elems_tys.push(TyRef::new(e_ty_v.clone()));
              self.hypotheses.push_back(TyHypothesis{
                ltree:    e.clone(),
                ty:       e_ty_v,
                venv:     hyp.venv.clone(),
              });
            }
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::STup(elems_tys)));
          }
          &LTerm::Tuple(_) => {
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::Tup));
          }
          &LTerm::BitLit(_) => {
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::Bit));
          }
          &LTerm::IntLit(_) => {
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::Int));
          }
          &LTerm::FloLit(_) => {
            self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), Ty::Flo));
          }
          &LTerm::Lookup(ref var) => {
            match hyp.venv.get(var) {
              None => panic!("bug"),
              Some(ty_v) => {
                self.constraints.push_back(TyConstraint::Eq(hyp.ty.clone(), ty_v.clone()));
              }
            }
          }
          _ => unimplemented!(),
        }
        false
      }
    }
  }

  pub fn gen(&mut self, ltree: LExpr) {
    self._reset(ltree);
    while !self._step() {
    }
  }

  fn _find_pty(substitution: &HashMap<u64, Ty>, ty_v: u64) -> Option<Ty> {
    let mut v = ty_v;
    loop {
      match substitution.get(&v) {
        Some(&Ty::Tyvar(w)) => {
          v = w;
        }
        Some(ty) => return Some(ty.clone()),
        None => return None,
      }
    }
  }

  fn _unify(lbuilder: &mut LBuilder, constraints: &mut VecDeque<TyConstraint>, substitution: &mut HashMap<u64, Ty>) -> Result<(), ()> {
    match constraints.pop_front() {
      None => {
        Ok(())
      }
      Some(TyConstraint::Eq(ref lhs, ref rhs)) => {
        if lhs == rhs {
          return Self::_unify(lbuilder, constraints, substitution);
        }
        match (lhs, rhs) {
          (_, &Ty::Tyvar(v)) => {
            // TODO: occurs-check.
            match substitution.get(&v) {
              Some(ty) => {
                constraints.push_front(TyConstraint::Eq(lhs.clone(), ty.clone()));
              }
              None => {
                substitution.insert(v, lhs.clone());
              }
            }
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::Tyvar(v), _) => {
            // TODO: occurs-check.
            match substitution.get(&v) {
              Some(ty) => {
                constraints.push_front(TyConstraint::Eq(ty.clone(), rhs.clone()));
              }
              None => {
                substitution.insert(v, rhs.clone());
              }
            }
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::Fun(ref lhs_dom, ref lhs_cod), &Ty::Fun(ref rhs_dom, ref rhs_cod)) => {
            if lhs_dom.len() != rhs_dom.len() {
              return Err(());
            }
            for (lt, rt) in lhs_dom.iter().zip(rhs_dom.iter()) {
              constraints.push_back(TyConstraint::Eq((**lt).clone(), (**rt).clone()));
            }
            constraints.push_back(TyConstraint::Eq((**lhs_cod).clone(), (**rhs_cod).clone()));
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::STup(ref lhs_elems), &Ty::STup(ref rhs_elems)) => {
            if lhs_elems.len() != rhs_elems.len() {
              return Err(());
            }
            for (lt, rt) in lhs_elems.iter().zip(rhs_elems.iter()) {
              constraints.push_back(TyConstraint::Eq((**lt).clone(), (**rt).clone()));
            }
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::ACons(ref lhs_key, ref lhs_kty, ref lhs_env), &Ty::ACons(ref rhs_key, ref rhs_kty, ref rhs_env)) => {
            // TODO
            if lhs_key != rhs_key {
              println!("DEBUG: unify failure: AEnv key mismatch");
              return Err(());
            }
            constraints.push_back(TyConstraint::Eq((**lhs_kty).clone(), (**rhs_kty).clone()));
            constraints.push_back(TyConstraint::Eq((**lhs_env).clone(), (**rhs_env).clone()));
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::AApp(_, _, ref lhs_ty), &Ty::AApp(_, _, ref rhs_ty)) => {
            // TODO: bind keys?
            constraints.push_back(TyConstraint::Eq((**lhs_ty).clone(), (**rhs_ty).clone()));
            Self::_unify(lbuilder, constraints, substitution)
          }
          (&Ty::ERet(_, ref lhs_ty), &Ty::ERet(_, ref rhs_ty)) => {
            // TODO: bind keys?
            constraints.push_back(TyConstraint::Eq((**lhs_ty).clone(), (**rhs_ty).clone()));
            Self::_unify(lbuilder, constraints, substitution)
          }
          /*(&Ty::EHashSel(ref env_ty, ref key_hash), _) => {
            // TODO
            unimplemented!();
          }*/
          _ => {
            println!("DEBUG: unify failure: lhs: {:?} rhs: {:?}", lhs, rhs);
            Err(())
          }
        }
      }
      Some(TyConstraint::IsaEnvSelByKeyHash(ref sel_ty, ref env_ty, ref key_hash)) => {
        match &*env_ty {
          &Ty::Tyvar(env_ty_v) => {
            match Self::_find_pty(substitution, env_ty_v) {
              None => {
                constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), env_ty.clone(), key_hash.clone()));
              }
              Some(ref env_pty) => {
                match env_pty {
                  &Ty::Tyvar(_) => {
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), env_ty.clone(), key_hash.clone()));
                  }
                  &Ty::AEnvNil => {
                    println!("DEBUG: unify failure: select nonexistent key hash in env");
                    return Err(());
                  }
                  &Ty::ACons(ref key, ref val_ty, ref next_env_ty) => {
                    let mut matched_var = None;
                    match key {
                      &LEnvKey::Var(ref key_var) => {
                        match lbuilder.vars.maybe_rev_lookup(key_var.clone()) {
                          None => {}
                          Some(ref key_var_hash) => {
                            if key_var_hash == key_hash {
                              matched_var = Some(key_var.clone());
                            }
                          }
                        }
                      }
                      _ => {}
                    }
                    if matched_var.is_some() {
                      println!("DEBUG: unify: found matching env select on key hash");
                      // FIXME: other constraints?
                      match &*sel_ty {
                        &Ty::Tyvar(sel_ty_v) => {
                          match substitution.get(&sel_ty_v) {
                            Some(ty) => {
                              constraints.push_back(TyConstraint::Eq(ty.clone(), Ty::ESel(TyRef::new(env_ty.clone()), matched_var.clone().unwrap(), key_hash.clone())));
                            }
                            None => {
                              substitution.insert(sel_ty_v, Ty::ESel(TyRef::new(env_ty.clone()), matched_var.clone().unwrap(), key_hash.clone()));
                            }
                          }
                        }
                        _ => unimplemented!(),
                      }
                    } else {
                      constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), (**next_env_ty).clone(), key_hash.clone()));
                    }
                  }
                  &Ty::AConcat(ref lhs_env_ty, ref rhs_env_ty) => {
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), (**lhs_env_ty).clone(), (**rhs_env_ty).clone(), key_hash.clone()));
                  }
                  &Ty::AApp(ref arg_vars, _, ref env_ty) => {
                    // TODO: bind keys?
                    // FIXME: this loop matches the first type with a compatible
                    // hash, but what if the hash has multiple matches?
                    let mut matched_var = None;
                    for arg_var in arg_vars.iter() {
                      match lbuilder.vars.maybe_rev_lookup(arg_var.clone()) {
                        None => {}
                        Some(ref arg_hash) => {
                          if arg_hash == key_hash {
                            matched_var = Some(arg_var.clone());
                            break;
                          }
                        }
                      }
                    }
                    if matched_var.is_some() {
                      println!("DEBUG: unify: found matching env select on key hash");
                      // FIXME: other constraints?
                      match &*sel_ty {
                        &Ty::Tyvar(sel_ty_v) => {
                          match substitution.get(&sel_ty_v) {
                            Some(ty) => {
                              constraints.push_back(TyConstraint::Eq(ty.clone(), Ty::ESel(TyRef::new((**env_ty).clone()), matched_var.clone().unwrap(), key_hash.clone())));
                            }
                            None => {
                              substitution.insert(sel_ty_v, Ty::ESel(TyRef::new((**env_ty).clone()), matched_var.clone().unwrap(), key_hash.clone()));
                            }
                          }
                        }
                        _ => unimplemented!(),
                      }
                    } else {
                      constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), (**env_ty).clone(), key_hash.clone()));
                    }
                  }
                  &Ty::ERet(_, ref env_ty) => {
                    // TODO: bind keys?
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), (**env_ty).clone(), key_hash.clone()));
                  }
                  _ => {
                    println!("DEBUG: unify failure: select key hash in a non-env ty: {:?}", env_pty);
                    return Err(());
                  }
                }
              }
            }
            return Self::_unify(lbuilder, constraints, substitution);
          }
          _ => unimplemented!(),
        }
      }
      Some(TyConstraint::IsaEnvSelByKeyHash2(ref sel_ty, ref env_ty, ref fallback_env_ty, ref key_hash)) => {
        match &*env_ty {
          &Ty::Tyvar(env_ty_v) => {
            match Self::_find_pty(substitution, env_ty_v) {
              None => {
                constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), env_ty.clone(), fallback_env_ty.clone(), key_hash.clone()));
              }
              Some(ref env_pty) => {
                match env_pty {
                  &Ty::Tyvar(_) => {
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), env_ty.clone(), fallback_env_ty.clone(), key_hash.clone()));
                  }
                  &Ty::AEnvNil => {
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash(sel_ty.clone(), fallback_env_ty.clone(), key_hash.clone()));
                  }
                  &Ty::ACons(ref key, ref val_ty, ref next_env_ty) => {
                    let mut matched_var = None;
                    match key {
                      &LEnvKey::Var(ref key_var) => {
                        match lbuilder.vars.maybe_rev_lookup(key_var.clone()) {
                          None => {}
                          Some(ref key_var_hash) => {
                            if key_var_hash == key_hash {
                              matched_var = Some(key_var.clone());
                            }
                          }
                        }
                      }
                      _ => {}
                    }
                    if matched_var.is_some() {
                      println!("DEBUG: unify: found matching env select on key hash");
                      // FIXME: other constraints?
                      match &*sel_ty {
                        &Ty::Tyvar(sel_ty_v) => {
                          match substitution.get(&sel_ty_v) {
                            Some(ty) => {
                              constraints.push_back(TyConstraint::Eq(ty.clone(), Ty::ESel(TyRef::new(env_ty.clone()), matched_var.clone().unwrap(), key_hash.clone())));
                            }
                            None => {
                              substitution.insert(sel_ty_v, Ty::ESel(TyRef::new(env_ty.clone()), matched_var.clone().unwrap(), key_hash.clone()));
                            }
                          }
                        }
                        _ => unimplemented!(),
                      }
                    } else {
                      constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), (**next_env_ty).clone(), fallback_env_ty.clone(), key_hash.clone()));
                    }
                  }
                  &Ty::AConcat(ref lhs_env_ty, ref rhs_env_ty) => {
                    // FIXME: push `rhs_env_ty` to the front of the queue of
                    // fallback env tys.
                    println!("WARNING: unify: emitting a truncated env-sel ty constraint");
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), (**lhs_env_ty).clone(), (**rhs_env_ty).clone(), key_hash.clone()));
                  }
                  &Ty::AApp(ref arg_vars, _, ref env_ty) => {
                    // TODO: bind keys?
                    // FIXME: this loop matches the first type with a compatible
                    // hash, but what if the hash has multiple matches?
                    let mut matched_var = None;
                    for arg_var in arg_vars.iter() {
                      match lbuilder.vars.maybe_rev_lookup(arg_var.clone()) {
                        None => {}
                        Some(ref arg_hash) => {
                          if arg_hash == key_hash {
                            matched_var = Some(arg_var.clone());
                            break;
                          }
                        }
                      }
                    }
                    if matched_var.is_some() {
                      println!("DEBUG: unify: found matching env select on key hash");
                      // FIXME: other constraints?
                      match &*sel_ty {
                        &Ty::Tyvar(sel_ty_v) => {
                          match substitution.get(&sel_ty_v) {
                            Some(ty) => {
                              constraints.push_back(TyConstraint::Eq(ty.clone(), Ty::ESel(TyRef::new((**env_ty).clone()), matched_var.clone().unwrap(), key_hash.clone())));
                            }
                            None => {
                              substitution.insert(sel_ty_v, Ty::ESel(TyRef::new((**env_ty).clone()), matched_var.clone().unwrap(), key_hash.clone()));
                            }
                          }
                        }
                        _ => unimplemented!(),
                      }
                    } else {
                      constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), (**env_ty).clone(), fallback_env_ty.clone(), key_hash.clone()));
                    }
                  }
                  &Ty::ERet(_, ref env_ty) => {
                    // TODO: bind keys?
                    constraints.push_back(TyConstraint::IsaEnvSelByKeyHash2(sel_ty.clone(), (**env_ty).clone(), fallback_env_ty.clone(), key_hash.clone()));
                  }
                  _ => {
                    println!("DEBUG: unify failure: select key hash in a non-env ty: {:?}", env_pty);
                    return Err(());
                  }
                }
              }
            }
            return Self::_unify(lbuilder, constraints, substitution);
          }
          _ => unimplemented!(),
        }
      }
      Some(_) => unimplemented!(),
    }
  }

  pub fn solve(&mut self, lbuilder: &mut LBuilder) -> Result<(), ()> {
    Self::_unify(lbuilder, &mut self.constraints, &mut self.substitution)
  }

  pub fn _debug_dump(&self) {
    for (vv, v) in self.bound_tyvars.iter() {
      println!("DEBUG: SimpleTyInferenceMachine: bound tv: {} = {:?}", v, vv);
    }
    for (ll, v) in self.tree_tyvars.iter() {
      println!("DEBUG: SimpleTyInferenceMachine: tree tv:  {} = {:?}", v, ll);
    }
    for (v, t) in self.substitution.iter() {
      println!("DEBUG: SimpleTyInferenceMachine: type sub: {} : {:?}", v, t);
    }
  }
}

impl LBuilder {
  pub fn pretty_print(&self, ltree: LTree) {
    LTreePrettyPrinter2{builder: self}.print(ltree);
  }
}

/*pub enum LPrettyPrinterVerbosity {
  V0,
  V1,
  V2,
  V3,
}

pub struct LPrettyPrinter {
  //v: LPrettyPrinterVerbosity,
}

impl LPrettyPrinter {
  fn _write<W: Write>(&mut self, ltree: LExpr, indent: usize, indent_first: bool, writer: &mut W) -> bool {
    // TODO
    if indent_first {
      for _ in 0 .. indent {
        write!(writer, " ").unwrap();
      }
    }
    match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        // TODO
        let apply_toks = "apply ";
        write!(writer, "{}", apply_toks).unwrap();
        self._write(head.clone(), indent + apply_toks.len() + 2, false, writer);
        writeln!(writer, "").unwrap();
        for arg in args.iter() {
          for _ in 0 .. indent + apply_toks.len() {
            write!(writer, " ").unwrap();
          }
          self._write(arg.clone(), indent + apply_toks.len() + 2, false, writer);
          writeln!(writer, "").unwrap();
        }
        false
      }
      &LTerm::Adj(ref sink) => {
        if let Some(ref freeuses) = ltree.info.freeuses {
          write!(writer, "# INFO: freeuses: [").unwrap();
          let mut first_it = true;
          for v in freeuses.inner.ones() {
            if first_it {
              write!(writer, "${}", v).unwrap();
              first_it = false;
            } else {
              write!(writer, ", ${}", v).unwrap();
            }
          }
          writeln!(writer, "]").unwrap();
          for _ in 0 .. indent {
            write!(writer, " ").unwrap();
          }
        }
        let adj_toks = format!("adj ");
        write!(writer, "{}", adj_toks).unwrap();
        let sink_indent = indent + adj_toks.len();
        self._write(sink.clone(), sink_indent, false, writer)
      }
      &LTerm::Lambda(ref params, ref body) => {
        // FIXME
        write!(writer, "\\").unwrap();
        for (param_idx, param) in params.iter().enumerate() {
          if param_idx == 0 {
            write!(writer, "${}", param.0).unwrap();
          } else {
            write!(writer, ", ${}", param.0).unwrap();
          }
        }
        write!(writer, ". <lam.body>").unwrap();
        false
      }
      &LTerm::VMExt(LTermVMExt::BCLambda(..)) => {
        // FIXME
        write!(writer, "<bclam>").unwrap();
        false
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        if let Some(ref freeuses) = ltree.info.freeuses {
          write!(writer, "# INFO: freeuses: [").unwrap();
          let mut first_it = true;
          for v in freeuses.inner.ones() {
            if first_it {
              write!(writer, "${}", v).unwrap();
              first_it = false;
            } else {
              write!(writer, ", ${}", v).unwrap();
            }
          }
          writeln!(writer, "]").unwrap();
          for _ in 0 .. indent {
            write!(writer, " ").unwrap();
          }
        }
        let let_toks = format!("let ${} = ", name.0);
        write!(writer, "{}", let_toks).unwrap();
        let body_indent = indent + let_toks.len();
        if self._write(body.clone(), body_indent, false, writer) {
          writeln!(writer, "").unwrap();
        }
        writeln!(writer, " in").unwrap();
        self._write(rest.clone(), indent, true, writer)
      }
      &LTerm::Switch(ref query, ref top, ref bot) => {
        let switch_toks = format!("switch ");
        write!(writer, "{}", switch_toks).unwrap();
        let query_indent = indent + switch_toks.len();
        if self._write(query.clone(), query_indent, false, writer) {
          writeln!(writer, "").unwrap();
        }
        writeln!(writer, " then").unwrap();
        self._write(top.clone(), indent + 4, true, writer);
        writeln!(writer, " |").unwrap();
        self._write(bot.clone(), indent + 4, true, writer)
      }
      &LTerm::Tuple(ref _elems) => {
        // FIXME
        write!(writer, "<tup>").unwrap();
        false
      }
      &LTerm::BitLit(x) => {
        // TODO
        write!(writer, "{}", if x { "tee" } else { "bot" }).unwrap();
        false
      }
      &LTerm::IntLit(x) => {
        // TODO
        write!(writer, "{}", x).unwrap();
        false
      }
      &LTerm::FloLit(x) => {
        // TODO
        write!(writer, "{:.0}f", x).unwrap();
        false
      }
      &LTerm::Lookup(ref lookup_var) => {
        // TODO
        write!(writer, "${}", lookup_var.0).unwrap();
        false
      }
      e => {
        panic!("pretty print: unimplemented ltree expr: {:?}", e);
      }
    }
  }

  pub fn write_to<W: Write>(&mut self, ltree: LExpr, writer: &mut W) {
    self._write(ltree, 0, true, writer);
    writeln!(writer, "").unwrap();
  }

  pub fn print(&mut self, ltree: LExpr) {
    let w = stdout();
    self.write_to(ltree, &mut w.lock());
  }
}*/

pub enum LTreePrettyPrinterVerbosity {
  V0,
  V1,
  V2,
  V3,
}

pub struct LTreePrettyPrinter<'a> {
  builder: &'a LBuilder,
  //v: LTreePrettyPrinterVerbosity,
}

impl<'a> LTreePrettyPrinter<'a> {
  fn _write<W: Write>(&mut self, lroot: &LTree, ltree: LExpr, indent: usize, indent_first: bool, writer: &mut W) -> bool {
    // TODO
    if indent_first {
      for _ in 0 .. indent {
        write!(writer, " ").unwrap();
      }
    }
    match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        // TODO
        let apply_toks = "apply ";
        write!(writer, "{}", apply_toks).unwrap();
        self._write(lroot, head.clone(), indent + apply_toks.len() + 2, false, writer);
        writeln!(writer, "").unwrap();
        for arg in args.iter() {
          for _ in 0 .. indent + apply_toks.len() {
            write!(writer, " ").unwrap();
          }
          self._write(lroot, arg.clone(), indent + apply_toks.len() + 2, false, writer);
          writeln!(writer, "").unwrap();
        }
        false
      }
      &LTerm::Lambda(ref params, ref body) => {
        // FIXME
        write!(writer, "\\").unwrap();
        for (param_idx, param) in params.iter().enumerate() {
          if param_idx == 0 {
            write!(writer, "${}", param.0).unwrap();
          } else {
            write!(writer, ", ${}", param.0).unwrap();
          }
        }
        write!(writer, ". <lam.body>").unwrap();
        false
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        // FIXME
        write!(writer, "<bclam>").unwrap();
        false
      }
      &LTerm::Adj(ref sink) => {
        if let Some(ref free_env) = ltree.maybe_free_env(lroot) {
          write!(writer, "# INFO: free env: [").unwrap();
          let mut first_it = true;
          for v in free_env.inner.ones() {
            if first_it {
              write!(writer, "${}", v).unwrap();
              first_it = false;
            } else {
              write!(writer, ", ${}", v).unwrap();
            }
          }
          writeln!(writer, "]").unwrap();
          for _ in 0 .. indent {
            write!(writer, " ").unwrap();
          }
        }
        let adj_toks = format!("adj ");
        write!(writer, "{}", adj_toks).unwrap();
        let sink_indent = indent + adj_toks.len();
        self._write(lroot, sink.clone(), sink_indent, false, writer)
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        if let Some(ref free_env) = ltree.maybe_free_env(lroot) {
          write!(writer, "# INFO: free env: [").unwrap();
          let mut first_it = true;
          for v in free_env.inner.ones() {
            if first_it {
              write!(writer, "${}", v).unwrap();
              first_it = false;
            } else {
              write!(writer, ", ${}", v).unwrap();
            }
          }
          writeln!(writer, "]").unwrap();
          for _ in 0 .. indent {
            write!(writer, " ").unwrap();
          }
        }
        let let_toks = match self.builder.vars.maybe_rev_lookup(name.clone()) {
          None => format!("let ${} = ", name.0),
          Some(h) => {
            let s = self.builder.hashes.rev_lookup(h);
            format!("let ${}({}) = ", name.0, s)
          }
        };
        write!(writer, "{}", let_toks).unwrap();
        let body_indent = indent + let_toks.len();
        if self._write(lroot, body.clone(), body_indent, false, writer) {
          writeln!(writer, "").unwrap();
        }
        writeln!(writer, " in").unwrap();
        self._write(lroot, rest.clone(), indent, true, writer)
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        let switch_toks = format!("switch ");
        write!(writer, "{}", switch_toks).unwrap();
        let pred_indent = indent + switch_toks.len();
        if self._write(lroot, pred.clone(), pred_indent, false, writer) {
          writeln!(writer, "").unwrap();
        }
        writeln!(writer, " then").unwrap();
        self._write(lroot, top.clone(), indent + 4, true, writer);
        writeln!(writer, " |").unwrap();
        self._write(lroot, bot.clone(), indent + 4, true, writer)
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let switch_toks = format!("match ");
        write!(writer, "{}", switch_toks).unwrap();
        let query_indent = indent + switch_toks.len();
        if self._write(lroot, query.clone(), query_indent, false, writer) {
          writeln!(writer, "").unwrap();
        }
        writeln!(writer, " |").unwrap();
        if pat_arms.len() == 1 {
          self._write(lroot, pat_arms[0].1.clone(), indent, true, writer)
        } else {
          let mut r = true;
          for &(ref pat, ref arm) in pat_arms.iter() {
            // FIXME: pattern.
            r = self._write(lroot, arm.clone(), indent + 4, true, writer);
            //writeln!(writer, " |").unwrap();
          }
          r
        }
      }
      &LTerm::Tuple(ref _elems) => {
        // FIXME
        write!(writer, "<tup>").unwrap();
        false
      }
      &LTerm::BitLit(x) => {
        // TODO
        write!(writer, "{}", if x { "tee" } else { "bot" }).unwrap();
        false
      }
      &LTerm::IntLit(x) => {
        // TODO
        write!(writer, "{}", x).unwrap();
        false
      }
      &LTerm::FloLit(x) => {
        // TODO
        //write!(writer, "{:.0}f", x).unwrap();
        write!(writer, "{}f", x).unwrap();
        false
      }
      &LTerm::Lookup(ref lookup_var) => {
        // TODO
        write!(writer, "${}", lookup_var.0).unwrap();
        false
      }
      e => {
        panic!("pretty print: unimplemented ltree expr: {:?}", e);
      }
    }
  }

  pub fn write_to<W: Write>(&mut self, ltree: LTree, writer: &mut W) {
    self._write(&ltree, ltree.root.clone(), 0, true, writer);
    writeln!(writer, "").unwrap();
  }

  pub fn print(&mut self, ltree: LTree) {
    let w = stdout();
    self.write_to(ltree, &mut w.lock());
  }
}

pub struct LTreePrettyPrinter2<'a> {
  builder: &'a LBuilder,
  //v: LTreePrettyPrinterVerbosity,
}

impl<'a> LTreePrettyPrinter2<'a> {
  fn _write_pat<W: Write>(&mut self, pat: &LPat, writer: &mut W) {
    // TODO
    match pat {
      &LPat::Cons(ref lhs, ref rhs) => {
        self._write_pat(&*lhs, writer);
        write!(writer, " :: ").unwrap();
        self._write_pat(&*rhs, writer);
      }
      &LPat::Concat(ref lhs, ref rhs) => {
        self._write_pat(&*lhs, writer);
        write!(writer, " ++ ").unwrap();
        self._write_pat(&*rhs, writer);
      }
      &LPat::STuple(ref elems) => {
        write!(writer, "{{").unwrap();
        for (e_idx, elem) in elems.iter().enumerate() {
          self._write_pat(&*elem, writer);
          if e_idx + 1 < elems.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, "}}").unwrap();
      }
      &LPat::Tuple(ref elems) => {
        write!(writer, "(").unwrap();
        for (e_idx, elem) in elems.iter().enumerate() {
          self._write_pat(&*elem, writer);
          if e_idx + 1 < elems.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, ")").unwrap();
      }
      &LPat::UnitLit => {
        write!(writer, "unit").unwrap();
      }
      &LPat::BitLit(x) => {
        write!(writer, "{}", if x { "tee" } else { "bot" }).unwrap();
      }
      &LPat::IntLit(x) => {
        write!(writer, "{}", x).unwrap();
      }
      /*&LPat::FloLit(x) => {
        //write!(writer, "{:.0}f", x).unwrap();
        write!(writer, "{}f", x).unwrap();
      }*/
      &LPat::Place => {
        write!(writer, "_").unwrap();
      }
      &LPat::Var(ref lookup_var) => {
        write!(writer, "${}", lookup_var.0).unwrap();
      }
      //Alias(LPatRef, LVar),
      //_ => unimplemented!(),
      p => {
        panic!("pretty print: unimplemented lpat: {:?}", p);
      }
    }
  }

  fn _write<W: Write>(&mut self, lroot: &LTree, ltree: LExpr, writer: &mut W) {
    match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        write!(writer, "(").unwrap();
        self._write(lroot, head.clone(), writer);
        write!(writer, ")[").unwrap();
        for (arg_idx, arg) in args.iter().enumerate() {
          self._write(lroot, arg.clone(), writer);
          if arg_idx + 1 < args.len() {
            write!(writer, ", ").unwrap();
          }
        }
        write!(writer, "]").unwrap();
      }
      &LTerm::OldEnv(ref kvs) => {
        write!(writer, "<env>{{").unwrap();
        for (kv_idx, &(_, ref k, ref v)) in kvs.iter().enumerate() {
          write!(writer, "${} => ", k.0).unwrap();
          self._write(lroot, v.clone(), writer);
          if kv_idx + 1 < kvs.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, "}}").unwrap();
      }
      &LTerm::AdjEnv(ref kvs) => {
        write!(writer, "<adj-env>{{").unwrap();
        for (kv_idx, &(ref k, ref v)) in kvs.iter().enumerate() {
          write!(writer, "${} => ", k.0).unwrap();
          self._write(lroot, v.clone(), writer);
          if kv_idx + 1 < kvs.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, "}}").unwrap();
      }
      &LTerm::AEnv(ref kvs) => {
        write!(writer, "<a-env>{{").unwrap();
        for (kv_idx, &(ref k, ref v)) in kvs.iter().enumerate() {
          match k {
            &LEnvKey::Var(ref var) => {
              write!(writer, "${} => ", var.0).unwrap();
            }
            &LEnvKey::Param(ref pos) => {
              write!(writer, "{} => ", pos).unwrap();
            }
          }
          self._write(lroot, v.clone(), writer);
          if kv_idx + 1 < kvs.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, "}}").unwrap();
      }
      &LTerm::ACons(ref lhs_key, ref lhs_value, ref rhs) => {
        write!(writer, "(").unwrap();
        // FIXME
        //self._write(lroot, lhs.clone(), writer);
        write!(writer, " <a>:: ").unwrap();
        self._write(lroot, rhs.clone(), writer);
        write!(writer, ")").unwrap();
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        write!(writer, "(").unwrap();
        self._write(lroot, lhs.clone(), writer);
        write!(writer, " <a>++ ").unwrap();
        self._write(lroot, rhs.clone(), writer);
        write!(writer, ")").unwrap();
      }
      &LTerm::AApp(ref args, ref arg_adjs, ref env) => {
        // TODO
        write!(writer, "<a-app>({{").unwrap();
        for (idx, ref arg) in args.iter().enumerate() {
          if idx < args.len() - 1 {
            write!(writer, "{} => ${}, ", idx, arg.0).unwrap();
          } else {
            write!(writer, "{} => ${},", idx, arg.0).unwrap();
          }
        }
        write!(writer, "}}, ").unwrap();
        self._write(lroot, env.clone(), writer);
        write!(writer, ")").unwrap();
      }
      &LTerm::ERet(ref params, ref env) => {
        write!(writer, "<e-ret>({{").unwrap();
        for (idx, ref param) in params.iter().enumerate() {
          if idx < params.len() - 1 {
            write!(writer, "${} => {}, ", param.0, idx).unwrap();
          } else {
            write!(writer, "${} => {},", param.0, idx).unwrap();
          }
        }
        write!(writer, "}}, ").unwrap();
        self._write(lroot, env.clone(), writer);
        write!(writer, ")").unwrap();
      }
      &LTerm::EHashSelect(ref tg_env, ref key_hash) => {
        write!(writer, "<e-hash-sel>(").unwrap();
        self._write(lroot, tg_env.clone(), writer);
        write!(writer, ", #{})", key_hash.0).unwrap();
      }
      &LTerm::ESelect(ref tg_env, ref key_name) => {
        write!(writer, "<e-sel>(").unwrap();
        self._write(lroot, tg_env.clone(), writer);
        write!(writer, ", ${})", key_name.0).unwrap();
      }
      &LTerm::Lambda(ref params, ref body) => {
        write!(writer, "\\").unwrap();
        for (param_idx, param) in params.iter().enumerate() {
          if param_idx == 0 {
            write!(writer, "${}", param.0).unwrap();
          } else {
            write!(writer, ", ${}", param.0).unwrap();
          }
        }
        write!(writer, ". ").unwrap();
        self._write(lroot, body.clone(), writer);
      }
      &LTerm::VMExt(LVMExt::BCLambda(..)) => {
        // FIXME
        write!(writer, "<bclam>").unwrap();
      }
      &LTerm::Adj(ref sink) => {
        write!(writer, "adj ").unwrap();
        self._write(lroot, sink.clone(), writer);
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        let let_toks = match self.builder.vars.maybe_rev_lookup(name.clone()) {
          None => format!("let ${} = ", name.0),
          Some(h) => {
            let s = self.builder.hashes.rev_lookup(h);
            format!("let ${}({}) = ", name.0, s)
          }
        };
        write!(writer, "{}", let_toks).unwrap();
        self._write(lroot, body.clone(), writer);
        writeln!(writer, " in ").unwrap();
        self._write(lroot, rest.clone(), writer);
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        write!(writer, "switch ").unwrap();
        self._write(lroot, pred.clone(), writer);
        write!(writer, " -: ").unwrap();
        self._write(lroot, top.clone(), writer);
        write!(writer, " | ").unwrap();
        self._write(lroot, bot.clone(), writer);
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        write!(writer, "match ").unwrap();
        self._write(lroot, query.clone(), writer);
        for (case_idx, &(ref pat, ref arm)) in pat_arms.iter().enumerate() {
          if case_idx == 0 {
            write!(writer, " with ").unwrap();
          } else {
            write!(writer, " | ").unwrap();
          }
          self._write_pat(pat, writer);
          write!(writer, " => ").unwrap();
          if pat_arms.len() == 1 {
            writeln!(writer, "").unwrap();
          }
          self._write(lroot, arm.clone(), writer);
        }
      }
      &LTerm::Concat(ref lhs, ref rhs) => {
        write!(writer, "(").unwrap();
        self._write(lroot, lhs.clone(), writer);
        write!(writer, " ++ ").unwrap();
        self._write(lroot, rhs.clone(), writer);
        write!(writer, ")").unwrap();
      }
      &LTerm::STuple(ref elems) => {
        write!(writer, "{{").unwrap();
        for (e_idx, elem) in elems.iter().enumerate() {
          self._write(lroot, elem.clone(), writer);
          if e_idx + 1 < elems.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, "}}").unwrap();
      }
      &LTerm::Tuple(ref elems) => {
        write!(writer, "(").unwrap();
        for (e_idx, elem) in elems.iter().enumerate() {
          self._write(lroot, elem.clone(), writer);
          if e_idx + 1 < elems.len() {
            write!(writer, ", ").unwrap();
          } else {
            write!(writer, ",").unwrap();
          }
        }
        write!(writer, ")").unwrap();
      }
      &LTerm::UnitLit => {
        // TODO
        write!(writer, "<unit>").unwrap();
      }
      &LTerm::BitLit(x) => {
        // TODO
        write!(writer, "{}", if x { "tee" } else { "bot" }).unwrap();
      }
      &LTerm::IntLit(x) => {
        // TODO
        write!(writer, "{}", x).unwrap();
      }
      &LTerm::FloLit(x) => {
        // TODO
        //write!(writer, "{:.0}f", x).unwrap();
        write!(writer, "{}f", x).unwrap();
      }
      &LTerm::Lookup(ref lookup_var) => {
        // TODO
        write!(writer, "${}", lookup_var.0).unwrap();
      }
      e => {
        panic!("pretty print: unimplemented ltree expr: {:?}", e);
      }
    }
  }

  pub fn print_to<W: Write>(&mut self, ltree: LTree, writer: &mut W) {
    self._write(&ltree, ltree.root.clone(), writer);
    writeln!(writer, "").unwrap();
  }

  pub fn print(&mut self, ltree: LTree) {
    let w = stdout();
    self.print_to(ltree, &mut w.lock());
  }
}
