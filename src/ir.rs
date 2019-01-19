// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::stdlib::*;
use crate::vm::{VMBoxCode};

use serde::{Serialize, Serializer};
//use serde::ser::{SerializeStruct};
use vertreap::{VertreapMap};

use std::collections::{HashMap};
//use std::collections::hash_map::{Entry};
use std::fmt::{self, Debug};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize)]
pub struct LIdx(pub usize);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize)]
pub struct LVar(pub u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize)]
pub struct LIdxVar {
  pub idx:  LIdx,
  pub var:  LVar,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize)]
pub struct LHash(pub u64);

#[derive(Clone, Default, Debug, Serialize)]
pub struct LLabel(pub u64);

pub enum LTermVMExt {
  BcLambda(Vec<LVar>, VMBoxCode),
}

impl Debug for LTermVMExt {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    // TODO
    write!(f, "BcLambda(...)")
  }
}

#[derive(Debug)]
//#[derive(Debug, Serialize)]
pub enum LTerm<E=LExpr, X=LTermVMExt> {
  Apply(E, Vec<E>),
  TailApply(E, Vec<E>),
  Env,
  DynEnv(LEnv),
  Lambda(Vec<LVar>, E),
  //BcLambda(Vec<LVar>, VMBoxCode),
  Let(LVar, E, E),
  Fix(LVar, E),
  //LetFunc(LVar, Vec<LVar>, E, E),
  Switch(E, E, E),
  NoRet,
  NonSmooth,
  BitLit(bool),
  IntLit(i64),
  FloatLit(f64),
  Lookup(LVar),
  EnvLookup(E, LVar),
  DynEnvLookup(E, String),
  //DynEnvLookupStr(E, String),
  //DynEnvLookup(E, LHash),
  Adj(E),
  AdjDyn(E),
  Extension(X),
}

#[derive(Debug)]
pub struct LTermRef<E=LExpr, X=LTermVMExt> {
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

#[derive(Clone, Default, Debug)]
pub struct LExprInfo {
  pub env:      Option<LEnv>,
  //pub freevars: Option<Vec<LVar>>,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub label:    LLabel,
  pub term:     LTermRef,
  pub info:     LExprInfo,
}

/*impl Serialize for LExpr {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let mut s = serializer.serialize_struct("LExpr", 3)?;
    s.serialize_field("label", &self.label)?;
    s.serialize_field("term", &*self.term)?;
    s.serialize_field("info", &self.info)?;
    s.end()
  }
}*/

#[derive(Clone, Debug)]
pub enum LDef {
  Code(LExpr),
  // TODO
  Fixpoint(LLabel, LVar, LTermRef, /*LEnvInfo,*/ Option<LEnv>),
}

#[derive(Clone, Default)]
pub struct LEnvNew {
  pub bindings: VertreapMap<LVar, (usize, LDef)>,
  pub vars:     VertreapMap<usize, LVar>,
}

#[derive(Clone, Default, Debug)]
pub struct LEnv {
  //pub bindings: HashMap<LVar, (usize, Rc<LExpr>)>,
  //pub vars:     Vec<(LVar, usize)>,
  pub bindings: HashMap<LVar, (usize, LDef)>,
  pub names:    HashMap<String, LVar>,
  //pub envs:     HashMap<LVar, LEnv>,
  pub vars:     Vec<LVar>,
}

impl LEnv {
  pub fn _bind(&mut self, var: LVar, code: LExpr) {
    let left_idx = self.vars.len();
    self.bindings.insert(var.clone(), (left_idx, LDef::Code(code)));
    self.vars.push(var);
  }

  pub fn _bind_fixed(&mut self, label: LLabel, fixvar: LVar, fixbody: LTermRef, env: Option<LEnv>) {
    let left_idx = self.vars.len();
    self.bindings.insert(fixvar.clone(), (left_idx, LDef::Fixpoint(label, fixvar.clone(), fixbody, env)));
    self.vars.push(fixvar);
  }

  pub fn _bind_named(&mut self, name: String, var: LVar, body: LExpr) {
    let left_idx = self.vars.len();
    self.bindings.insert(var.clone(), (left_idx, LDef::Code(body)));
    self.names.insert(name, var.clone());
    self.vars.push(var);
  }

  pub fn _lookup_name(&self, name: String) -> (LVar, LExpr) {
    match self.names.get(&name) {
      Some(var) => {
        match self.bindings.get(var) {
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
  }

  pub fn fork(&self, name: LVar, body: LExpr) -> LEnv {
    let mut new_env = self.clone();
    new_env._bind(name, body);
    new_env
  }

  pub fn fork_fixed(&self, label: LLabel, fixname: LVar, fixbody: LTermRef, env: Option<LEnv>) -> LEnv {
    let mut new_env = self.clone();
    new_env._bind_fixed(label, fixname, fixbody, env);
    new_env
  }
}

/*pub enum LVarKey {
  Fresh,
  Name(String),
  IntLit(i64),
  FloatLit(f64),
}*/

#[derive(Debug)]
pub enum LBindKey {
  Fresh,
  Name(String),
  Hash(LHash),
  //IntLit(i64),
  //FloatLit(f64),
}

#[derive(Default)]
struct LVarBuilder {
  //n_to_id:  HashMap<String, LVar>,
  h_to_id:  HashMap<LHash, LVar>,
  id_to_k:  HashMap<LVar, LBindKey>,
  id_ctr:   u64,
}

impl LVarBuilder {
  pub fn _debug_dump_vars(&self) {
    println!("DEBUG: vars: {:?}", self.id_to_k);
  }

  //pub fn rev_lookup(&mut self, var: LVar) -> String {
  pub fn rev_lookup(&mut self, var: LVar) -> LHash {
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
  pub fn lookup(&mut self, hash: LHash) -> LVar {
    match self.h_to_id.get(&hash) {
      Some(var) => var.clone(),
      None => panic!(),
    }
  }

  /*pub fn insert(&mut self, name: String) {
    let _ = self.bind(name);
  }*/

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
struct LHashBuilder {
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
struct LLabelBuilder {
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
  labels:   LLabelBuilder,
  hashes:   LHashBuilder,
  vars:     LVarBuilder,
}

impl LBuilder {
  pub fn new() -> LBuilder {
    let labels = LLabelBuilder::default();
    let hashes = LHashBuilder::default();
    let vars = LVarBuilder::default();
    LBuilder{
      labels,
      hashes,
      vars,
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

  pub fn _make_bclambda(&mut self, bc: VMBoxCode) -> LExpr {
    LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Extension(LTermVMExt::BcLambda(vec![], bc))), info: LExprInfo::default()}
  }

  pub fn _alloc_bclambda(&mut self, name: &str, bc: VMBoxCode) -> (LHash, LVar, LLabel, LExpr) {
    let (hash, var, label) = self._alloc_name(name);
    let bclam = self._make_bclambda(bc);
    (hash, var, label, bclam)
  }

  pub fn _include_stdlib_and_lower(&mut self, htree: Rc<HExpr>) -> LExpr {
    let (_, var_pi100, label_pi100, bc_pi100) = self._alloc_bclambda("pi100", make_bc_pi100());
    let (_, var_neg, label_neg, bc_neg) = self._alloc_bclambda("neg", make_bc_neg());
    let (_, var_add, label_add, bc_add) = self._alloc_bclambda("add", make_bc_add());
    let (_, var_mul, label_mul, bc_mul) = self._alloc_bclambda("mul", make_bc_mul());
    let ltree = self._htree_to_ltree_lower_pass(htree);
    fn bind(label: LLabel, var: LVar, body: LExpr, rest: LExpr) -> LExpr {
      LExpr{label: label, term: LTermRef::new(LTerm::Let(var, body, rest)), info: LExprInfo::default()}
    }
    let ltree = (bind)(label_mul, var_mul, bc_mul, ltree);
    let ltree = (bind)(label_add, var_add, bc_add, ltree);
    let ltree = (bind)(label_neg, var_neg, bc_neg, ltree);
    let ltree = (bind)(label_pi100, var_pi100, bc_pi100, ltree);
    ltree
  }

  pub fn _htree_to_ltree_lower_pass(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    match &*htree {
      &HExpr::Lambda(ref args, ref body) => {
        // TODO
        let bvars: Vec<_> = args.iter().map(|arg| {
          let a = self._htree_to_ltree_lower_pass(arg.clone());
          match &*a.term {
            &LTerm::Lookup(ref v) => v.clone(),
            _ => panic!(),
          }
        }).collect();
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lambda(bvars, body)), info: LExprInfo::default()}
      }
      &HExpr::Apply(ref lhs, ref args) => {
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let args: Vec<_> = args.iter().map(|arg| {
          self._htree_to_ltree_lower_pass(arg.clone())
        }).collect();
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(lhs, args)), info: LExprInfo::default()}
      }
      &HExpr::Adj(ref body) => {
        // TODO
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Adj(body)), info: LExprInfo::default()}
      }
      &HExpr::AdjDyn(ref body) => {
        // TODO
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::AdjDyn(body)), info: LExprInfo::default()}
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        let attrs = maybe_attrs.clone().unwrap_or_default();
        match &**lhs {
          &HExpr::Ident(ref lhs) => {
            // FIXME: desugar "let rec" to "let fix in".
            match attrs.rec {
              false => {
                let lhs_hash = self.hashes.lookup(lhs.to_string());
                let (lhs_hash, lhs_var, lhs_oldvar) = self.vars.bind(lhs_hash);
                let body = self._htree_to_ltree_lower_pass(body.clone());
                let rest = self._htree_to_ltree_lower_pass(rest.clone());
                self.vars.unbind(lhs_hash, lhs_var.clone(), lhs_oldvar);
                LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(lhs_var, body, rest)), info: LExprInfo::default()}
              }
              true  => {
                let lhs_hash = self.hashes.lookup(lhs.to_string());
                let (lhs_hash, lhs_var, lhs_oldvar) = self.vars.bind(lhs_hash);
                let fixbody = self._htree_to_ltree_lower_pass(body.clone());
                let fix = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Fix(lhs_var.clone(), fixbody)), info: LExprInfo::default()};
                let rest = self._htree_to_ltree_lower_pass(rest.clone());
                self.vars.unbind(lhs_hash, lhs_var.clone(), lhs_oldvar);
                LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(lhs_var, fix, rest)), info: LExprInfo::default()}
              }
            }
          }
          &HExpr::Apply(ref lhs, ref args) => {
            // FIXME: desugar "let rec" to "let fix in".
            let lhs_hash = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.hashes.lookup(name.to_string())
              }
              _ => panic!(),
            };
            let (name, name_var, name_oldvar) = self.vars.bind(lhs_hash);
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
            let lam = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lambda(args_vars, body)), info: LExprInfo::default()};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            self.vars.unbind(name, name_var.clone(), name_oldvar);
            LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(name_var, lam, rest)), info: LExprInfo::default()}
          }
          _ => {
            panic!();
          }
        }
      }
      &HExpr::Switch(ref pred, ref top, ref bot) => {
        let pred = self._htree_to_ltree_lower_pass(pred.clone());
        let top = self._htree_to_ltree_lower_pass(top.clone());
        let bot = self._htree_to_ltree_lower_pass(bot.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Switch(pred, top, bot)), info: LExprInfo::default()}
      }
      &HExpr::Eq(ref lhs, ref rhs) => {
        let op_name = "eq".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        let op_name = "add".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::Sub(ref lhs, ref rhs) => {
        let op_name = "sub".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::Mul(ref lhs, ref rhs) => {
        let op_name = "mul".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::Div(ref lhs, ref rhs) => {
        let op_name = "div".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::Neg(ref arg) => {
        let op_name = "neg".to_string();
        let op_hash = self.hashes.lookup(op_name);
        let op_var = self.vars.lookup(op_hash);
        let op = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(op_var)), info: LExprInfo::default()};
        let arg = self._htree_to_ltree_lower_pass(arg.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Apply(op, vec![arg])), info: LExprInfo::default()}
      }
      &HExpr::NoRet => {
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::NoRet), info: LExprInfo::default()}
      }
      &HExpr::NonSmooth => {
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::NonSmooth), info: LExprInfo::default()}
      }
      &HExpr::BotLit => {
        // TODO: special varbol key for literal constants.
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::BitLit(false)), info: LExprInfo::default()}
      }
      &HExpr::TeeLit => {
        // TODO: special varbol key for literal constants.
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::BitLit(true)), info: LExprInfo::default()}
      }
      &HExpr::IntLit(x) => {
        // TODO: special varbol key for literal constants.
        //let var = self.vars.int_lit(x);
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::IntLit(x)), info: LExprInfo::default()}
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.hashes.lookup(name.to_string());
        let name_var = self.vars.lookup(name_hash);
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Lookup(name_var)), info: LExprInfo::default()}
      }
      &HExpr::PathLookup(ref lhs, ref name) => {
        /*let (name, name_var, name_oldvar) = self.vars.bind(name.to_string());
        //let body = self._htree_to_ltree_lower_pass(body.clone());
        let env = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Env), info: LExprInfo::default()};
        //let rest = self._htree_to_ltree_lower_pass(rest.clone());
        self.vars.unbind(name, name_var.clone(), name_oldvar);
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::Let(name_var, body, rest)), info: LExprInfo::default()}*/
        // TODO
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::DynEnvLookup(lhs, name.clone())), info: LExprInfo::default()}
      }
      _ => {
        // TODO
        unimplemented!();
      }
    }
  }

  pub fn lower(&mut self, htree: Rc<HExpr>) -> LExpr {
    self._htree_to_ltree_lower_pass(htree)
  }
/*}

pub struct LTransformer {
}

impl LTransformer {
  pub fn new() -> LTransformer {
    LTransformer{}
  }*/

  pub fn _ltree_normalize_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn normalize(&mut self, ltree: LExpr) -> LExpr {
    self._ltree_normalize_pass(ltree)
  }

  pub fn _ltree_env_info_pass_rec(&mut self, env: LEnv, ltree: LExpr) -> LExpr {
    // TODO
    match &*ltree.term {
      &LTerm::Apply(ref head, ref args) => {
        let head = self._ltree_env_info_pass_rec(env.clone(), head.clone());
        let args = args.iter().map(|arg| self._ltree_env_info_pass_rec(env.clone(), arg.clone())).collect();
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Apply(
              head,
              args,
          )),
          info,
        }
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = self._ltree_env_info_pass_rec(env.clone(), body.clone());
        let rest_env = env.fork(name.clone(), body.clone());
        let rest = self._ltree_env_info_pass_rec(rest_env, rest.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Let(
              name.clone(),
              body,
              rest,
          )),
          info,
        }
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        // TODO
        let fix_env = env.fork_fixed(ltree.label.clone(), fixname.clone(), fixbody.term.clone(), Some(env.clone()));
        let fixbody = self._ltree_env_info_pass_rec(fix_env, fixbody.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Fix(
              fixname.clone(),
              fixbody,
          )),
          info,
        }
      }
      &LTerm::Switch(ref pred, ref top, ref bot) => {
        let pred = self._ltree_env_info_pass_rec(env.clone(), pred.clone());
        let top = self._ltree_env_info_pass_rec(env.clone(), top.clone());
        let bot = self._ltree_env_info_pass_rec(env.clone(), bot.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Switch(
              pred,
              top,
              bot,
          )),
          info,
        }
      }
      &LTerm::IntLit(x) => {
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::IntLit(x)),
          info,
        }
      }
      &LTerm::Lookup(ref lookup_var) => {
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Lookup(lookup_var.clone())),
          info,
        }
      }
      &LTerm::Adj(ref body) => {
        // TODO
        let body = self._ltree_env_info_pass_rec(env.clone(), body.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Adj(body)),
          info,
        }
      }
      &LTerm::AdjDyn(ref body) => {
        // TODO
        let body = self._ltree_env_info_pass_rec(env.clone(), body.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::AdjDyn(body)),
          info,
        }
      }
      &LTerm::DynEnvLookup(ref target, ref name) => {
        // TODO
        let target = self._ltree_env_info_pass_rec(env.clone(), target.clone());
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::DynEnvLookup(target, name.clone())),
          info,
        }
        /*let target = self._ltree_env_info_pass_rec(env.clone(), target.clone());
        match target.info.env {
          Some(ref tgenv) => {
            let (lk_var, lk_code) = tgenv._lookup_name(name.clone());
            // FIXME: may want a fresh label.
            lk_code
          }
          None => panic!(),
        }*/
      }
      _ => unimplemented!(),
    }
  }

  pub fn _ltree_env_info_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO: fill initial env.
    let env = LEnv::default();
    self._ltree_env_info_pass_rec(env, ltree)
  }

  pub fn _ltree_adjoint_pass(&mut self, ltree: LExpr) -> LExpr {
    match &*ltree.term {
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = self._ltree_adjoint_pass(body.clone());
        let rest = self._ltree_adjoint_pass(rest.clone());
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Let(
              name.clone(),
              body,
              rest,
          )),
          info:     ltree.info,
        }
      }
      &LTerm::IntLit(x) => {
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::IntLit(x)),
          info:     ltree.info,
        }
      }
      &LTerm::Lookup(ref lookup_var) => {
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::Lookup(lookup_var.clone())),
          info:     ltree.info,
        }
      }
      &LTerm::Adj(ref body) => {
        // TODO
        let orig_env = match ltree.info.env {
          Some(ref env) => env.clone(),
          None => panic!(),
        };
        let mut shadow_env = orig_env.clone();
        let mut shadow = vec![];
        // FIXME: only need to shadow freevars, not all bindings in scope.
        for (fvar_var, _) in orig_env.bindings.iter() {
          let fvar_name = self.vars.rev_lookup(fvar_var.clone());
          let (shadow_hash, shadow_var, shadow_oldvar) = self.vars.bind(fvar_name);
          let shadow_name = self.hashes.rev_lookup(shadow_hash.clone());
          // FIXME: next line is where we bind the adjoint expr;
          // for now, we set the adjoint to be any old literal.
          let shadow_code = LExpr{label: self.labels.fresh(), term: LTermRef::new(LTerm::IntLit(42424242)), info: LExprInfo::default()};
          shadow_env._bind_named(shadow_name.clone(), shadow_var.clone(), shadow_code);
          shadow.push((shadow_hash, shadow_var, shadow_oldvar));
        }
        for (shadow_hash, shadow_var, shadow_oldvar) in shadow.into_iter().rev() {
          self.vars.unbind(shadow_hash, shadow_var, shadow_oldvar);
        }
        let mut info = LExprInfo::default();
        info.env = Some(shadow_env);
        LExpr{
          label:    self.labels.fresh(),
          term:     LTermRef::new(LTerm::Env),
          info,
        }
      }
      &LTerm::AdjDyn(ref root) => {
        // TODO
        let root = self._ltree_adjoint_pass(root.clone());
        let root_env = match root.info.env {
          Some(ref env) => env.clone(),
          None => panic!(),
        };
        let mut shadow_env = root_env.clone();
        let mut shadow = vec![];
        // FIXME: do the correct traversal order (requires freevars).
        // FIXME: only need to shadow freevars, not all bindings in scope.
        for (fvar_var, &(_, ref fvar_def)) in root_env.bindings.iter() {
          let fvar_hash = self.vars.rev_lookup(fvar_var.clone());
          let (fvar_hash, shadow_var, shadow_oldvar) = self.vars.bind(fvar_hash);
          let fvar_name = self.hashes.rev_lookup(fvar_hash.clone());
          // FIXME: next line is where we bind the adjoint expr;
          // for now, we set the adjoint to be any old literal.
          let adj_term = match &*root.term {
            &LTerm::Lookup(ref root_var) => {
              if root_var == fvar_var {
                Some(LTerm::IntLit(1))
              } else {
                None
              }
            }
            _ => {
              // FIXME: if the IR is properly normalized, root should always be
              // a var.
              println!("WARNING: adj dyn: root is not a var");
              None
            }
          }.unwrap_or({
            /*match fvar_def {
              &LDef::Code(ref ltree) => {
                // TODO
                //unimplemented!();
              }
            }*/
            LTerm::IntLit(42424242)
          });
          let shadow_code = LExpr{label: self.labels.fresh(), term: LTermRef::new(adj_term), info: LExprInfo::default()};
          shadow_env._bind_named(fvar_name, shadow_var.clone(), shadow_code);
          shadow.push((fvar_hash, shadow_var, shadow_oldvar));
        }
        for (fvar_hash, shadow_var, shadow_oldvar) in shadow.into_iter().rev() {
          self.vars.unbind(fvar_hash, shadow_var, shadow_oldvar);
        }
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::DynEnv(shadow_env)),
          info:     ltree.info,
        }
      }
      &LTerm::DynEnvLookup(ref target, ref name) => {
        // TODO
        let target = self._ltree_adjoint_pass(target.clone());
        LExpr{
          label:    ltree.label.clone(),
          term:     LTermRef::new(LTerm::DynEnvLookup(target, name.clone())),
          info:     ltree.info,
        }
      }
      _ => unimplemented!(),
    }
  }

  /*pub fn _ltree_adjoint_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO: fill initial env.
    let env = LEnv::default();
    self._ltree_adjoint_pass_rec(env, ltree)
  }*/

  pub fn _ltree_adjoint_lookup_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }
}
