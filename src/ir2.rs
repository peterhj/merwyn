// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::mach::{MAddr, MBLambda, MCLambda};

use rpds::{HashTrieMap, Queue, RedBlackTreeMap, Stack};

use std::cell::{RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LLabel(u64);

impl AsRef<LLabel> for LLabel {
  fn as_ref(&self) -> &LLabel {
    self
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LIdent(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LVar(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LEnvKey {
  Var(LVar),
  Pos(usize),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LTyvar(u64);

#[derive(Clone, Debug)]
pub enum LPat {
  Cons(LPatRef, LPatRef),
  Concat(LPatRef, LPatRef),
  STuple(Vec<LPatRef>),
  Tuple(Vec<LPatRef>),
  BitLit(bool),
  IntLit(i64),
  Var(LVar),
  Alias(LPatRef, LVar),
}

#[derive(Clone, Debug)]
pub struct LPatRef(Rc<LPat>);

impl From<LVar> for LPatRef {
  fn from(var: LVar) -> LPatRef {
    LPat::Var(var).into()
  }
}

impl From<LPat> for LPatRef {
  fn from(pat: LPat) -> LPatRef {
    LPatRef(Rc::new(pat))
  }
}

impl Deref for LPatRef {
  type Target = LPat;

  fn deref(&self) -> &LPat {
    &*self.0
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
    let mut vars_buf = Vec::new();
    let mut vars_set = HashSet::new();
    self._vars(&mut vars_set, &mut vars_buf);
    vars_buf
  }
}

#[derive(Clone, Debug)]
pub enum LTerm<E=LLoc> {
  End,
  Module(Vec<E>, E),
  TodoRequire,
  Break(E),
  Apply(E, Vec<E>),
  Lambda(Vec<LVar>, E),
  Import(E, E),
  ImportR(Vec<LVar>, E, E),
  Export,
  Env(Vec<(LVar, E)>),
  PtlD(E),
  AdjD(E),
  TngD(E),
  Jac(E),
  Adj(E),
  Tng(E),
  Let(LVar, E, E),
  Fix(LVar, E),
  //Alt(LVar, LVar, E, E),
  Match(E, Vec<(LPatRef, E)>),
  Cons(E, E),
  Concat(E, E),
  STuple(Vec<E>),
  Tuple(Vec<E>),
  UnitLit,
  BitLit(bool),
  IntLit(i64),
  FloLit(f64),
  Lookup(LVar),
  ProjectIdent(E, LIdent),
  Unbind(LVar, E),
  MExt(LMLoc),
}

#[derive(Clone)]
pub struct LMExpr {
  pub label:    LLabel,
  pub mterm:    LMTerm,
}

#[derive(Clone)]
pub enum LMTerm {
  Deref(MAddr),
  BLam(LMLambdaDef<MBLambda>),
  CLam(LMLambdaDef<MCLambda>),
}

#[derive(Clone)]
pub struct LMLambdaDef<Module> {
  pub ar:   usize,
  pub cg:   Option<Rc<dyn Fn() -> Module>>,
  pub ty:   Option<Rc<dyn Fn(&mut LBuilder, /*LCtxRef*/) -> (Vec<LTy>, LTy)>>,
  pub adj:  Option<Rc<dyn Fn(&mut LBuilder, /*LCtxRef,*/ Vec<LVar>, LVar) -> LExpr>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LVarBinder {
  Ident(LIdent),
  Anon,
}

impl From<LIdent> for LVarBinder {
  fn from(hash: LIdent) -> LVarBinder {
    LVarBinder::Ident(hash)
  }
}

#[derive(Clone, Default)]
pub struct LBuilder {
  label_ctr:    u64,
  hash_ctr:     u64,
  var_ctr:      u64,
  name_to_hash: HashTrieMap<String, LIdent>,
  hash_to_name: HashTrieMap<LIdent, String>,
  var_to_bind:  HashTrieMap<LVar, LVarBinder>,
  adj_var:      HashTrieMap<LVar, LVar>,
  adj_exp:      HashTrieMap<LLabel, LLabel>,
  adj_snd_exp:  HashTrieMap<LLabel, LLabel>,
  tyinf:        IncTyInfMachine,
  //ctx:          LCtxRef,
  //tctx:         LTyctxRef,
}

impl LBuilder {
  pub fn fresh_label(&mut self) -> LLabel {
    self.label_ctr += 1;
    assert!(self.label_ctr != 0);
    LLabel(self.label_ctr)
  }

  pub fn lookup_name(&mut self, name: &str) -> LIdent {
    match self.name_to_hash.get(name) {
      None => {
        self.hash_ctr += 1;
        assert!(self.hash_ctr != 0);
        let new_hash = LIdent(self.hash_ctr);
        self.name_to_hash.insert_mut(name.to_owned(), new_hash.clone());
        self.hash_to_name.insert_mut(new_hash.clone(), name.to_owned());
        new_hash
      }
      Some(hash) => hash.clone(),
    }
  }

  pub fn fresh_anon_var(&mut self) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    let new_var = LVar(self.var_ctr);
    assert!(!self.var_to_bind.contains_key(&new_var));
    self.var_to_bind.insert_mut(new_var.clone(), LVarBinder::Anon);
    new_var
  }

  pub fn fresh_hash_var(&mut self, hash: LIdent) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    let new_var = LVar(self.var_ctr);
    assert!(!self.var_to_bind.contains_key(&new_var));
    self.var_to_bind.insert_mut(new_var.clone(), LVarBinder::Ident(hash.clone()));
    new_var
  }

  pub fn lookup_var(&mut self, var: &LVar) -> LVarBinder {
    match self.var_to_bind.get(var) {
      None => panic!("bug"),
      Some(binder) => binder.clone(),
    }
  }

  pub fn _lookup_adj_var(&mut self, var: &LVar) -> Option<LVar> {
    match self.adj_var.get(var) {
      None => None,
      Some(adj) => Some(adj.clone()),
    }
  }

  pub fn lookup_adj_var(&mut self, var: &LVar) -> LVar {
    match self.adj_var.get(var) {
      None => {
        let adj = self.fresh_anon_var();
        self.adj_var.insert_mut(var.clone(), adj.clone());
        adj
      }
      Some(adj) => adj.clone(),
    }
  }

  pub fn _lookup_adj_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> Option<LLabel> {
    let label = loc.as_ref();
    match self.adj_exp.get(label) {
      None => None,
      Some(adj) => Some(adj.clone()),
    }
  }

  pub fn lookup_adj_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> LLabel {
    let label = loc.as_ref();
    match self.adj_exp.get(label) {
      None => {
        let adj = self.fresh_label();
        self.adj_exp.insert_mut(label.clone(), adj.clone());
        adj
      }
      Some(adj) => adj.clone(),
    }
  }

  pub fn _lookup_adj_snd_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> Option<LLabel> {
    let label = loc.as_ref();
    match self.adj_snd_exp.get(label) {
      None => None,
      Some(adj) => Some(adj.clone()),
    }
  }

  pub fn lookup_adj_snd_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> LLabel {
    let label = loc.as_ref();
    match self.adj_snd_exp.get(label) {
      None => {
        let adj = self.fresh_label();
        self.adj_snd_exp.insert_mut(label.clone(), adj.clone());
        adj
      }
      Some(adj) => adj.clone(),
    }
  }

  pub fn compile(&mut self, htree: Rc<HExpr>) -> Result<LModule, ()> {
    // TODO
    unimplemented!();
  }

  pub fn _compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef, top_tctx: LTyctxRef) -> Result<LModule, ()> {
    // TODO
    let tree = self._lower(htree, top_ctx.clone());
    let tree = self._normalize(tree);
    let tree = self._recontext(tree, top_ctx.clone());
    //let tree = self._gc(tree);
    // FIXME: derive tenv from base tctx.
    let mut tenv = TyEnv::default();
    //let mut tenv = TyEnv::from_tctx(&top_tctx);
    let mut work = TyWork::default();
    self.tyinf.gen(&tree, &mut tenv, &mut work);
    let ty_res = self.tyinf.solve(tree.root(), &mut tenv, &mut work);
    //println!("DEBUG: compile: tyinf result: {:?}", ty_res);
    //println!("DEBUG: compile:   defer: {:?}", work.defer_cs);
    //println!("DEBUG: compile:   unsat: {:?}", work.unsat);
    /*loop {
      if work.unsat() {
        return Err(());
      } else if work.defer() {
        let old_tree = tree.clone();
        let new_tree = self._resolve_tyinf(old_tree.clone(), &tenv);
        self.tyinf.gen_inc(&old_tree, &new_tree, &mut tenv, &mut work);
        self.tyinf.solve(new_tree.root(), &mut tenv, &mut work);
        tree = new_tree;
      } else {
        break;
      }
    }*/
    let end_ctx = tree.root_ctx();
    let end_tctx = match end_ctx {
      None => None,
      Some(ref ctx) => tree.final_tctx(ctx, &mut tenv),
    };
    //println!("DEBUG: compile:   ctx? {:?} tctx? {:?}",
    //    end_ctx.is_some(), end_tctx.is_some());
    Ok(LModule{
      tree,
      end_ctx,
      end_tctx,
    })
  }
}

impl LBuilder {
  pub fn _lower_pat_rec(&mut self, htree: Rc<HExpr>, _other: ()) -> LPatRef {
    // TODO
    match &*htree {
      &HExpr::STuple(ref elems) => {
        unimplemented!();
      }
      &HExpr::Tuple(ref elems) => {
        unimplemented!();
      }
      &HExpr::TeeLit => {
        LPat::BitLit(true).into()
      }
      &HExpr::BotLit => {
        LPat::BitLit(false).into()
      }
      &HExpr::IntLit(x) => {
        LPat::IntLit(x).into()
      }
      &HExpr::PlacePat => {
        unimplemented!();
      }
      &HExpr::Ident(ref name) => {
        unimplemented!();
      }
      _ => unimplemented!(),
    }
  }

  pub fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_hash(op_hash) {
      Some(v) => v,
      None => {
        // TODO: propagate errors.
        println!("error: unknown var '{}'", op_name);
        self.fresh_anon_var()
      }
    };
    let op_label = self.fresh_label();
    let op_e = LExpr{
      version:  0,
      label:    op_label.clone(),
      term:     LTerm::Lookup(op_var)
    };
    let op_ = LLoc::new2(op_label, pos + 1, pos);
    let mut curr_pos = pos + 2;
    let (arg_label, next_pos) = self._lower_rec(arg, ctx.clone(), stack, curr_pos);
    let arg_ = LLoc::new2(arg_label, curr_pos, pos);
    curr_pos = next_pos;
    let label = self.fresh_label();
    let e = LExpr{
      version:  0,
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![arg_])
    };
    //stack.push_front((op_e, ctx.clone(), pos + 1));
    //stack.push_front((e, ctx, pos));
    stack.insert(pos + 1, (op_e, ctx.clone(), pos + 1));
    stack.insert(pos, (e, ctx, pos));
    (label, curr_pos)
  }

  pub fn _lower_binop(&mut self, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_hash(op_hash) {
      Some(v) => v,
      None => {
        // TODO: propagate errors.
        println!("error: unknown var '{}'", op_name);
        self.fresh_anon_var()
      }
    };
    let op_label = self.fresh_label();
    let op_e = LExpr{
      version:  0,
      label:    op_label.clone(),
      term:     LTerm::Lookup(op_var)
    };
    let op_ = LLoc::new2(op_label, pos + 1, pos);
    let mut curr_pos = pos + 2;
    let (lhs_label, next_pos) = self._lower_rec(lhs, ctx.clone(), stack, curr_pos);
    let lhs_ = LLoc::new2(lhs_label, curr_pos, pos);
    curr_pos = next_pos;
    let (rhs_label, next_pos) = self._lower_rec(rhs, ctx.clone(), stack, curr_pos);
    let rhs_ = LLoc::new2(rhs_label, curr_pos, pos);
    curr_pos = next_pos;
    let label = self.fresh_label();
    let e = LExpr{
      version:  0,
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![lhs_, rhs_])
    };
    //stack.push_front((op_e, ctx.clone(), pos + 1));
    //stack.push_front((e, ctx, pos));
    stack.insert(pos + 1, (op_e, ctx.clone(), pos + 1));
    stack.insert(pos, (e, ctx, pos));
    (label, curr_pos)
  }

  pub fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, /*up: LLoc, label: LLabel,*/ pos: usize) -> (LLabel, usize) {
    match &*htree {
      &HExpr::End => {
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          //up,
          label:    label.clone(),
          term:     LTerm::End
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Apply(ref head, ref args) => {
        let mut curr_pos = pos + 1;
        let (head_label, next_pos) = self._lower_rec(head.clone(), ctx.clone(), stack, curr_pos);
        let head_ = LLoc::new2(head_label, curr_pos, pos);
        curr_pos = next_pos;
        let mut args_: Vec<_> = Vec::with_capacity(args.len());
        for arg in args.iter() {
          let (arg_label, next_pos) = self._lower_rec(arg.clone(), ctx.clone(), stack, curr_pos);
          args_.push(LLoc::new2(arg_label, curr_pos, pos));
          curr_pos = next_pos;
        }
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::Apply(head_, args_)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, curr_pos)
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
          let p_var = self.fresh_hash_var(p_hash.clone());
          body_ctx.bind_mut(p_hash, p_var.clone());
          param_vars.push(p_var);
        }
        let body_pos = pos + 1;
        let (body_label, next_pos) = self._lower_rec(body.clone(), body_ctx, stack, body_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::Lambda(param_vars, LLoc::new2(body_label, body_pos, pos))
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::PartialD(ref target) => {
        let target_pos = pos + 1;
        let (target_label, next_pos) = self._lower_rec(target.clone(), ctx.clone(), stack, target_pos);
        let target_ = LLoc::new(target_label, target_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::PtlD(target_)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::AdjointD(ref target) => {
        let target_pos = pos + 1;
        let (target_label, next_pos) = self._lower_rec(target.clone(), ctx.clone(), stack, target_pos);
        let target_ = LLoc::new(target_label, target_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::AdjD(target_)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::TangentD(ref target) => {
        let target_pos = pos + 1;
        let (target_label, next_pos) = self._lower_rec(target.clone(), ctx.clone(), stack, target_pos);
        let target_ = LLoc::new(target_label, target_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::TngD(target_)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::Jacobian(ref target) => {
        let target_pos = pos + 1;
        let (target_label, next_pos) = self._lower_rec(target.clone(), ctx.clone(), stack, target_pos);
        let target_ = LLoc::new(target_label, target_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::Jac(target_)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::Let(ref attrs, ref lhs, ref body, ref rest) => {
        // TODO: attributes.
        let body_ctx = ctx.clone();
        let mut rest_ctx = ctx.clone();
        let name = match &**lhs {
          &HExpr::Ident(ref name) => name,
          _ => unimplemented!(),
        };
        let attrs = attrs.clone().unwrap_or_default();
        let n_hash = self.lookup_name(name);
        let n_var = self.fresh_hash_var(n_hash.clone());
        let prev_n_var = if attrs.alt {
          match ctx.lookup_hash(n_hash.clone()) {
            None => panic!(),
            Some(prev_n_var) => Some(prev_n_var),
          }
        } else {
          None
        };
        rest_ctx.bind_mut(n_hash, n_var.clone());
        let body_pos = pos + 1;
        let (body_label, next_pos) = self._lower_rec(body.clone(), body_ctx, stack, body_pos);
        let body_ = LLoc::new2(body_label, body_pos, pos);
        let rest_pos = next_pos;
        let (rest_label, next_pos) = self._lower_rec(rest.clone(), rest_ctx, stack, rest_pos);
        let rest_ = LLoc::new2(rest_label, rest_pos, pos);
        let label = self.fresh_label();
        let e = match prev_n_var {
          Some(prev_n_var) => {
            panic!("overloaded bindings with `alt` are not yet supported");
          }
          None => LExpr{
            version:    0,
            label:      label.clone(),
            term:       LTerm::Let(n_var, body_, rest_)
          },
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      /*&HExpr::LetFun(ref attrs, ref lhs, ref body, ref rest) => {
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
          version:  0,
          label:    label.clone(),
          term:     LTerm::BitLit(false)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::TeeLit => {
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::BitLit(true)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::IntLit(x) => {
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::IntLit(x)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::FloLit(x) => {
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::FloLit(x)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.lookup_name(name);
        let name_var = match ctx.lookup_hash(name_hash) {
          Some(v) => v,
          None => {
            // TODO: propagate errors.
            println!("error: unknown var '{}'", name);
            self.fresh_anon_var()
          }
        };
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::Lookup(name_var)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::PathLookup(ref lhs, ref rhs_name) => {
        let name_hash = self.lookup_name(rhs_name);
        let lhs_pos = pos + 1;
        let (lhs_label, next_pos) = self._lower_rec(lhs.clone(), ctx.clone(), stack, lhs_pos);
        let lhs_ = LLoc::new(lhs_label, lhs_pos);
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::ProjectIdent(lhs_, name_hash)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
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

  pub fn _lower(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LTreeCell {
    let mut stack = BTreeMap::new();
    //let root_label = self.fresh_label();
    //self._lower_rec(htree, ctx, &mut stack, LLoc::new(root_label.clone(), 0), root_label, 0);
    self._lower_rec(htree, ctx, &mut stack, 0);
    let mut ltree = LTree::default();
    for (&pos, &(ref e, ref ctx, pos2)) in stack.iter() {
      assert_eq!(pos, pos2);
      assert_eq!(pos, ltree.exps.len());
      assert_eq!(pos, ltree.ctxs.len());
      ltree.exps.push(e.clone());
      ltree.ctxs.insert(e.label.clone(), ctx.clone());
    }
    let view = LTreeView{
      root:     LLoc::new(ltree.exps[0].label.clone(), 0),
      epoch:    1,
      //version:  ltree.exps.len(),
      version:  0,
      //revision: 0,
      //changed:  false,
    };
    LTreeCell{
      view,
      data: Rc::new(RefCell::new(ltree)),
    }
  }
}

impl LBuilder {
  pub fn _normalize_kont(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    match &exp.term() {
      // TODO: cases.
      &LTerm::End => kont(self, exp),
      &LTerm::Break(ref inner) => {
        let inner = self._normalize_term(exp.lookup(inner));
        let new_exp = exp.append(self, &mut |_| LTerm::Break(inner.loc()));
        kont(self, new_exp)
      }
      &LTerm::Apply(ref head, ref args) => {
        let head = exp.lookup(head);
        let args = Queue::from_iter(args.iter().map(|a| exp.lookup(a)));
        self._normalize_name(head, &mut |this, head| {
          this._normalize_names(args.clone(), Queue::new(), &mut |this, args| {
            let new_exp = exp.append(this, &mut |_| LTerm::Apply(
                head.loc(),
                args.iter().map(|a| a.loc()).collect(),
            ));
            kont(this, new_exp)
          })
        })
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._normalize_term(exp.lookup(body));
        let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
            params.clone(),
            body.loc(),
        ));
        kont(self, new_exp)
      }
      &LTerm::Import(ref env, ref body) => {
        let env = exp.lookup(env);
        let body = exp.lookup(body);
        self._normalize_name(env, &mut |this, env| {
          let body = this._normalize_term(body.clone());
          let new_exp = exp.append(this, &mut |_| LTerm::Import(
              env.loc(),
              body.loc(),
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::Export => kont(self, exp),
      &LTerm::PtlD(ref target) => {
        let target = exp.lookup(target);
        self._normalize_name(target, &mut |this, target| {
          let new_exp = exp.append(this, &mut |_| LTerm::PtlD(target.loc()));
          kont(this, new_exp)
        })
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = exp.lookup(body);
        let rest = exp.lookup(rest);
        self._normalize_kont(body, &mut |this, body| {
          let rest = this._normalize_kont(rest.clone(), kont);
          exp.append(this, &mut |_| LTerm::Let(
              name.clone(),
              body.loc(),
              rest.loc(),
          ))
        })
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixbody = self._normalize_term(exp.lookup(fixbody));
        let new_exp = exp.append(self, &mut |_| LTerm::Fix(
            fixname.clone(),
            fixbody.loc(),
        ));
        kont(self, new_exp)
      }
      /*&LTerm::Alt(ref name, ref alt_name, ref body, ref rest) => {
        let body = exp.lookup(body);
        let rest = exp.lookup(rest);
        self._normalize_kont(body, &mut |this, body| {
          let rest = this._normalize_kont(rest.clone(), kont);
          exp.append(this, &mut |_| LTerm::Alt(
              name.clone(),
              alt_name.clone(),
              body.loc(),
              rest.loc(),
          ))
        })
      }*/
      &LTerm::BitLit(_) => kont(self, exp),
      &LTerm::IntLit(_) => kont(self, exp),
      &LTerm::FloLit(_) => kont(self, exp),
      &LTerm::Lookup(_) => kont(self, exp),
      &LTerm::ProjectIdent(ref env, ref name) => {
        let env = exp.lookup(env);
        self._normalize_name(env, &mut |this, env| {
          let new_exp = exp.append(this, &mut |_| LTerm::ProjectIdent(
              env.loc(),
              name.clone(),
          ));
          kont(this, new_exp)
        })
      }
      _ => {
        unimplemented!();
      }
    }
  }

  pub fn _normalize_term(&mut self, exp: LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |_, exp| exp)
  }

  pub fn _normalize_names(&mut self, mut pre_exps: Queue<LExprCell>, post_exps: Queue<LExprCell>, kont: &mut dyn FnMut(&mut Self, Queue<LExprCell>) -> LExprCell) -> LExprCell {
    match pre_exps.peek() {
      Some(exp) => {
        let exp = exp.clone();
        assert!(pre_exps.dequeue_mut());
        self._normalize_name(exp, &mut |this, exp| {
          let pre_exps = pre_exps.clone();
          let post_exps = post_exps.enqueue(exp);
          this._normalize_names(pre_exps, post_exps, kont)
        })
      }
      None => kont(self, post_exps)
    }
  }

  pub fn _normalize_name(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |this, exp| {
      match &exp.term() {
        &LTerm::BitLit(_) => kont(this, exp),
        &LTerm::IntLit(_) => kont(this, exp),
        &LTerm::FloLit(_) => kont(this, exp),
        &LTerm::Lookup(_) => kont(this, exp),
        // TODO: cases.
        _ => {
          let new_var = this.fresh_anon_var();
          let new_var_e1 = exp.append(this, &mut |this| {
            LTerm::Lookup(new_var.clone())
          });
          let new_var_e = kont(this, new_var_e1);
          let bind_e = exp.append(this, &mut |_| LTerm::Let(
              new_var.clone(),
              exp.loc(),
              new_var_e.loc(),
          ));
          bind_e
        }
      }
    })
  }

  pub fn _normalize(&mut self, tree: LTreeCell) -> LTreeCell {
    let new_root = self._normalize_term(tree.root());
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }
}

impl LBuilder {
  pub fn _recontext_exp(&mut self, exp: LExprCell, ctx: LCtxRef) {
    exp.unsafe_set_ctx(ctx.clone());
    match &exp.term() {
      &LTerm::End => {}
      &LTerm::Break(ref inner) => {
        self._recontext_exp(exp.lookup(inner), ctx);
      }
      &LTerm::Apply(ref head, ref args) => {
        self._recontext_exp(exp.lookup(head), ctx.clone());
        for arg in args.iter() {
          self._recontext_exp(exp.lookup(arg), ctx.clone());
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut body_ctx = ctx.clone();
        for p in params.iter() {
          body_ctx.bind_mut(self.lookup_var(p), p.clone());
        }
        self._recontext_exp(exp.lookup(body), body_ctx);
      }
      &LTerm::Import(ref env, ref body) => {
        let env = exp.lookup(env);
        let body = exp.lookup(body);
        self._recontext_exp(env, ctx);
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }
      &LTerm::Export => {}
      &LTerm::PtlD(ref target) => {
        self._recontext_exp(exp.lookup(target), ctx);
      }
      &LTerm::AdjD(ref target) => {
        self._recontext_exp(exp.lookup(target), ctx);
      }
      &LTerm::Adj(ref target) => {
        self._recontext_exp(exp.lookup(target), ctx);
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let mut rest_ctx = ctx.clone();
        rest_ctx.bind_mut(self.lookup_var(name), name.clone());
        self._recontext_exp(exp.lookup(body), ctx);
        self._recontext_exp(exp.lookup(rest), rest_ctx);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let mut fixctx = ctx.clone();
        fixctx.bind_mut(self.lookup_var(fixname), fixname.clone());
        self._recontext_exp(exp.lookup(fixbody), fixctx);
      }
      /*&LTerm::Alt(ref name, ref alt_name, ref body, ref rest) => {
        let mut rest_ctx = ctx.clone();
        rest_ctx.bind_mut(self.lookup_var(alt_name), alt_name.clone());
        self._recontext_exp(exp.lookup(body), ctx);
        self._recontext_exp(exp.lookup(rest), rest_ctx);
      }*/
      &LTerm::BitLit(_) => {}
      &LTerm::IntLit(_) => {}
      &LTerm::FloLit(_) => {}
      &LTerm::Lookup(_) => {}
      &LTerm::ProjectIdent(ref env, _) => {
        self._recontext_exp(exp.lookup(env), ctx);
      }
      _ => unimplemented!(),
    }
  }

  pub fn _recontext(&mut self, tree: LTreeCell, ctx: LCtxRef) -> LTreeCell {
    self._recontext_exp(tree.root(), ctx);
    tree
  }
}

impl LBuilder {
  pub fn _gc(&mut self, tree: LTreeCell) -> LTreeCell {
    unimplemented!();
  }
}

impl LBuilder {
  fn _resolve_deferred_0(&mut self, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    // TODO
    let defer_ct = work.defer.len();
    for _ in 0 .. defer_ct {
      let deferred = work.defer.pop_front().unwrap();
      match &deferred {
        &TyDeferral::PtlD(ref ptld, ref target) => {
          if let Some((_, _, ty)) = tenv.mgu_exp(target) {
            match &*ty {
              &LTy::Flo => {
                // TODO
                let _ = root.append(self, &mut |this| {
                  let adj_e = root.append(this, &mut |this| {
                    //let tg_e = root.append(this, &mut |_| LTerm::Lookup(target.clone()));
                    LTerm::Adj(target.clone())
                  });
                  let id_e = root.append(this, &mut |_| LTerm::FloLit(1.0));
                  LTerm::Apply(
                      adj_e.loc(),
                      vec![id_e.loc()]
                  )
                });
              }
              _ => {
                // TODO
              }
            }
          } else {
            work.defer.push_back(deferred);
            continue;
          }
        }
        _ => {
          work.defer.push_back(deferred);
          continue;
        }
      }
    }
  }

  fn _adj_pat(&mut self, pat: LPatRef) -> LPatRef {
    // TODO
    unimplemented!();
  }

  fn _adj_snd_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv) -> Option<LExprCell> {
    // TODO
    match self._lookup_adj_snd_exp(&exp) {
      None => {}
      Some(adj_snd_l) => return Some(exp.lookup_exp(&adj_snd_l)),
    }
    match &exp.term() {
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        let rest_e = exp.lookup(rest);
        let adj_rest_e = match self._adj_snd_exp(rest_e, tenv) {
          None => return None,
          Some(e) => e,
        };
        let new_label = self.lookup_adj_snd_exp(&exp);
        let new_exp = match self._lookup_adj_var(name) {
          None => {
            exp._append(new_label, self, &mut |_| LTerm::Let(
                name.clone(),
                body.clone(),
                adj_rest_e.loc()
            ))
          }
          Some(adj_name) => {
            let body_e = exp.lookup(body);
            let adj_body_e = self._adj_exp(body_e, tenv);
            exp._append(new_label, self, &mut |_| LTerm::Match(
                adj_body_e.loc(),
                vec![(
                  LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                  adj_rest_e.loc(),
                )]
            ))
          }
        };
        // TODO: register `new_exp`.
        Some(new_exp)
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        let mut nontriv_adj_arm = false;
        let mut adj_arms = Vec::with_capacity(pat_arms.len());
        for &(_, ref arm) in pat_arms.iter() {
          let arm_e = exp.lookup(arm);
          match self._adj_snd_exp(arm_e, tenv) {
            None => {
              let unit_e = exp.append(self, &mut |_| LTerm::UnitLit);
              adj_arms.push(unit_e);
            }
            Some(adj_arm_e) => {
              nontriv_adj_arm = true;
              adj_arms.push(adj_arm_e);
            }
          }
        }
        if !nontriv_adj_arm {
          return None;
        }
        // FIXME: test for adj var bound in pat.
        let mut nontriv_adj_pat = false;
        let mut adj_pats = Vec::with_capacity(pat_arms.len());
        for &(ref pat, _) in pat_arms.iter() {
          let adj_pat = self._adj_pat(pat.clone());
          adj_pats.push(adj_pat);
        }
        let query_e = exp.lookup(query);
        let adj_query_e = self._adj_exp(query_e, tenv);
        let new_label = self.lookup_adj_snd_exp(&exp);
        let new_exp = exp._append(new_label, self, &mut |_| LTerm::Match(
            adj_query_e.loc(),
            adj_pats.iter().map(|pat| pat.clone())
              .zip(adj_arms.iter().map(|e| e.loc()))
              .collect()
        ));
        // TODO: register `new_exp`.
        Some(new_exp)
      }
      &LTerm::Apply(..) => {
        // TODO
        unimplemented!();
      }
      &LTerm::Lambda(ref params, ref body) => {
        // TODO
        let body_e = exp.lookup(body);
        let adj_body_e = self._adj_exp(body_e, tenv);
        if adj_body_e.label == body.label {
          return None;
        }
        let mut adj_params = Vec::with_capacity(params.len());
        //let mut adj_vars = Vec::with_capacity(params.len());
        for p in params.iter() {
          match self._lookup_adj_var(p) {
            None => {
              adj_params.push(p.clone());
            }
            Some(adj_p) => match tenv.mgu_var(p.clone()) {
              None => {
                // FIXME: need to defer this term.
              }
              Some((_, _, ty)) => match &*ty {
                // FIXME
                &LTy::Flo => {}
                &LTy::Fun(..) => {}
                _ => unimplemented!(),
              }
            }
          }
        }
        // FIXME: need to do some fixup of the adj body.
        let new_label = self.lookup_adj_snd_exp(&exp);
        let adj_lam_e = exp._append(new_label, self, &mut |_| LTerm::Lambda(
            adj_params.clone(),
            adj_body_e.loc()
        ));
        Some(adj_lam_e)
      }
      &LTerm::STuple(ref elems) => {
        let mut nontriv_adj_elem = false;
        let mut adj_elems = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          let elem_e = exp.lookup(elem);
          match self._adj_snd_exp(elem_e, tenv) {
            None => {
              let unit_e = exp.append(self, &mut |_| LTerm::UnitLit);
              adj_elems.push(unit_e);
            }
            Some(adj_elem_e) => {
              nontriv_adj_elem = true;
              adj_elems.push(adj_elem_e);
            }
          }
        }
        if !nontriv_adj_elem {
          return None;
        }
        let new_label = self.lookup_adj_snd_exp(&exp);
        let adj_stuple_e = exp._append(new_label, self, &mut |_| LTerm::STuple(
            adj_elems.iter().map(|e| e.loc()).collect()
        ));
        Some(adj_stuple_e)
      }
      &LTerm::Tuple(ref elems) => {
        // TODO
        unimplemented!();
      }
      &LTerm::FloLit(_) => {
        let adj_nil_env_e = exp.append(self, &mut |_| LTerm::Env(vec![]));
        let new_label = self.lookup_adj_snd_exp(&exp);
        let adj_mk_env_e = exp._append(new_label, self, &mut |this| LTerm::Lambda(
            vec![this.fresh_anon_var()],
            adj_nil_env_e.loc()
        ));
        Some(adj_mk_env_e)
      }
      &LTerm::Lookup(ref var) => {
        // FIXME: may depend on MGU for `var`.
        let adj_var = self.lookup_adj_var(var);
        let new_label = self.lookup_adj_snd_exp(&exp);
        let adj_lookup_e = exp._append(new_label, self, &mut |_| LTerm::Lookup(adj_var.clone()));
        Some(adj_lookup_e)
      }
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) => {
        None
      }
      _ => unimplemented!(),
    }
  }

  fn _adj_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv) -> LExprCell {
    // TODO
    match self._lookup_adj_exp(&exp) {
      None => {}
      Some(adj_l) => return exp.lookup_exp(&adj_l),
    }
    match &exp.term() {
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        let rest_e = exp.lookup(rest);
        let adj_rest_e = self._adj_exp(rest_e, tenv);
        if adj_rest_e.label == rest.label {
          return exp;
        }
        let new_label = self.lookup_adj_exp(&exp);
        let new_exp = match self._lookup_adj_var(name) {
          None => {
            exp._append(new_label, self, &mut |_| LTerm::Let(
                name.clone(),
                body.clone(),
                adj_rest_e.loc()
            ))
          }
          Some(adj_name) => {
            let body_e = exp.lookup(body);
            let adj_body_e = self._adj_exp(body_e, tenv);
            exp._append(new_label, self, &mut |_| LTerm::Match(
                adj_body_e.loc(),
                vec![(
                  LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                  adj_rest_e.loc(),
                )]
            ))
          }
        };
        // TODO: register `new_exp`.
        new_exp
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        let mut nontriv_adj_arm = false;
        let mut adj_arms = Vec::with_capacity(pat_arms.len());
        for &(_, ref arm) in pat_arms.iter() {
          let arm_e = exp.lookup(arm);
          let adj_arm_e = self._adj_exp(arm_e, tenv);
          if adj_arm_e.label != arm.label {
            nontriv_adj_arm = true;
          }
          adj_arms.push(adj_arm_e);
        }
        if !nontriv_adj_arm {
          return exp;
        }
        // FIXME: test for adj var bound in pat.
        let mut nontriv_adj_pat = false;
        let mut adj_pats = Vec::with_capacity(pat_arms.len());
        for &(ref pat, _) in pat_arms.iter() {
          let adj_pat = self._adj_pat(pat.clone());
          adj_pats.push(adj_pat);
        }
        let query_e = exp.lookup(query);
        let adj_query_e = self._adj_exp(query_e, tenv);
        let new_label = self.lookup_adj_exp(&exp);
        let new_exp = exp._append(new_label, self, &mut |_| LTerm::Match(
            adj_query_e.loc(),
            adj_pats.iter().map(|pat| pat.clone())
              .zip(adj_arms.iter().map(|e| e.loc()))
              .collect()
        ));
        // TODO: register `new_exp`.
        new_exp
      }
      _ => {
        match self._adj_snd_exp(exp.clone(), tenv) {
          None => exp,
          Some(adj_exp) => {
            let new_label = self.lookup_adj_exp(&exp);
            let new_exp = exp._append(new_label, self, &mut |_| LTerm::STuple(vec![exp.loc(), adj_exp.loc()]));
            // TODO: register `new_exp`.
            new_exp
          }
        }
      }
    }
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Tyexp {
  Var(LTyvar),
  //Adj(/*LTyvar,*/ LTyvar),
  Fun(Vec<TyexpRef>, TyexpRef),
  //EnvCons(LVar, LIdent, LTyvar, TyexpRef),
  //EnvCat(RedBlackTreeMap<LEnvKey, LTyvar>, RedBlackTreeMap<LIdent, LVar>, TyexpRef),
  Env(RedBlackTreeMap<LEnvKey, LTyvar>, RedBlackTreeMap<LIdent, LVar>),
  STup(Vec<TyexpRef>),
  Tup,
  Bit,
  Int,
  Flo,
  VFlo,
  Unit,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct TyexpRef(Rc<Tyexp>);

impl From<Tyexp> for TyexpRef {
  fn from(e: Tyexp) -> TyexpRef {
    TyexpRef(Rc::new(e))
  }
}

impl From<LTyvar> for TyexpRef {
  fn from(v: LTyvar) -> TyexpRef {
    TyexpRef::from(Tyexp::Var(v))
  }
}

impl Deref for TyexpRef {
  type Target = Tyexp;

  fn deref(&self) -> &Tyexp {
    &*self.0
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Tytag {
  // FIXME: need more of the domain signature, arity alone is not sufficient.
  PtlDf(usize),
  PtlDv,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LTy {
  Fun(Vec<LTyRef>, LTyRef),
  Env(RedBlackTreeMap<LEnvKey, LTyRef>, RedBlackTreeMap<LIdent, LVar>),
  STup(Vec<LTyRef>),
  Tup,
  Bit,
  Int,
  Flo,
  VFlo,
  Unit,
}

pub type LTyRef = Rc<LTy>;

/*#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct LTyRef {
  inner:    Rc<LTy>,
}

impl LTyRef {
  pub fn new(e: LTy) -> LTyRef {
    LTyRef{inner: Rc::new(e)}
  }
}

impl Deref for LTyRef {
  type Target = LTy;

  fn deref(&self) -> &LTy {
    &*self.inner
  }
}*/

type TyConRef = Rc<TyCon>;

// TODO
/*struct TyConRef {
  inner:    Rc<(Cell<bool>, TyCon)>,
}*/

#[derive(Debug)]
enum TyCon {
  Top,
  Cnj(Queue<TyConRef>),
  Eq_(TyexpRef, TyexpRef),
  Tagged(TyexpRef, Tytag),
  IsPtlD(TyexpRef, TyexpRef),
  //IsACons(LVar, LTy, LTy, LTy),
  //IsAConcat(LTy, LTy, LTy),
  //IsAApp(Vec<(usize, LVar)>, LTyvar, LTy),
  //IsERet(Vec<(usize, LVar)>, LTyvar, LTy),
  IsProjIdent(TyexpRef, TyexpRef, LIdent),
}

/*fn conj_ty2(lhs: TyConRef, rhs: TyConRef) -> TyConRef {
  match &*lhs {
    &TyCon::Cnj(ref cons) => {
      TyConRef::new(TyCon::Cnj(cons.enqueue(rhs)))
    }
    _ => {
      let mut cons = Queue::new();
      cons.enqueue_mut(lhs);
      cons.enqueue_mut(rhs);
      TyConRef::new(TyCon::Cnj(cons))
    }
  }
}

fn conj_tys(cons: Vec<TyConRef>) -> TyConRef {
  if cons.is_empty() {
    return TyConRef::new(TyCon::Top);
  }
  match &*cons[0] {
    &TyCon::Cnj(ref cons0) => {
      let mut cons0 = cons0.clone();
      for c in cons[1 .. ].iter() {
        cons0.enqueue_mut(c.clone());
      }
      TyConRef::new(TyCon::Cnj(cons0))
    }
    _ => {
      let cons_ = Queue::from_iter(cons.into_iter());
      TyConRef::new(TyCon::Cnj(cons_))
    }
  }
}*/

#[derive(Debug)]
struct TyAdjHyp {
  pri_ety:  LTyvar,
  adj_texp: TyexpRef,
}

#[derive(Debug)]
enum TyDeferral {
  PtlD(LLoc, LLoc),
  ProjIdent(LLoc, LLoc, LIdent),
}

#[derive(Default, Debug)]
struct TyWork {
  //tenv:     TyEnv,
  cons:     VecDeque<TyConRef>,
  unsat:    VecDeque<TyConRef>,
  defer_cs: VecDeque<TyConRef>,
  defer:    VecDeque<TyDeferral>
}

impl TyWork {
  fn unsat(&self) -> bool {
    !self.unsat.is_empty()
  }

  fn defer(&self) -> bool {
    !self.defer_cs.is_empty()
  }
}

#[derive(Debug)]
struct TyBridgeWork {
  exps: HashMap<LLoc, LLoc>,
}

/*enum TyUnify {
  OK,
  Maybe,
  No,
}*/

/*#[derive(Default)]
struct TyUnionFind {
  db:   BTreeMap<LTyvar, LTyvar>,
  tag:  BTreeMap<LTyvar, Tytag>,
  term: BTreeMap<LTyvar, TyexpRef>,
}

impl TyUnionFind {
  fn head(&mut self, query: LTyvar) -> LTyvar {
    if !self.db.contains_key(&query) {
      self.db.insert(query.clone(), query.clone());
      return query;
    }
    let mut cursor = query;
    let mut next = self.db.get(&cursor).unwrap().clone();
    while cursor != next {
      let next2 = match self.db.get(&next) {
        None => next.clone(),
        Some(next2) => next2.clone(),
      };
      self.db.insert(next.clone(), next2.clone());
      cursor = next;
      next = next2;
    }
    cursor
  }
}*/

#[derive(Debug)]
enum TyReduce {
  Exp(TyexpRef),
  Var(LTyvar),
}

#[derive(Default, Debug)]
struct TyEnv {
  // TODO
  vctr: u64,
  var:  HashMap<LVar, LTyvar>,
  vari: HashMap<LTyvar, LVar>,
  exp:  HashMap<LLabel, LTyvar>,
  expi: HashMap<LTyvar, LLabel>,
  db:   HashMap<LTyvar, LTyvar>,
  texp: HashMap<LTyvar, TyexpRef>,
  tag:  HashMap<LTyvar, Tytag>,
  tadj: HashMap<LTyvar, LTyvar>,
}

impl TyEnv {
  fn from_tctx(tctx: &LTyctxRef) -> TyEnv {
    // TODO
    unimplemented!();
  }

  fn fresh_tvar(&mut self) -> LTyvar {
    self.vctr += 1;
    assert!(self.vctr != 0);
    LTyvar(self.vctr)
  }

  fn _lookup_var(&mut self, var: &LVar) -> Option<LTyvar> {
    match self.var.get(var) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  fn lookup_var(&mut self, var: &LVar) -> LTyvar {
    match self.var.get(var) {
      None => {
        let v = self.fresh_tvar();
        self.var.insert(var.clone(), v.clone());
        self.vari.insert(v.clone(), var.clone());
        v
      }
      Some(v) => v.clone(),
    }
  }

  fn _lookup_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> Option<LTyvar> {
    let label = loc.as_ref();
    match self.exp.get(label) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  fn lookup_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> LTyvar {
    let label = loc.as_ref();
    match self.exp.get(label) {
      None => {
        let v = self.fresh_tvar();
        self.exp.insert(label.clone(), v.clone());
        self.expi.insert(v.clone(), label.clone());
        v
      }
      Some(v) => v.clone(),
    }
  }

  fn lookup_adj(&mut self, v: LTyvar) -> LTyvar {
    match self.tadj.get(&v) {
      None => {
        let dv = self.fresh_tvar();
        self.tadj.insert(v, dv.clone());
        dv
      }
      Some(dv) => dv.clone(),
    }
  }

  fn head(&mut self, query: LTyvar) -> LTyvar {
    if !self.db.contains_key(&query) {
      self.db.insert(query.clone(), query.clone());
      return query;
    }
    let mut cursor = query;
    let mut next = self.db.get(&cursor).unwrap().clone();
    while cursor != next {
      let next2 = match self.db.get(&next) {
        None => next.clone(),
        Some(next2) => next2.clone(),
      };
      self.db.insert(next.clone(), next2.clone());
      cursor = next;
      next = next2;
    }
    cursor
  }

  fn unify(&mut self, lv: LTyvar, rv: LTyvar) {
    if lv == rv {
      return;
    }
    let lw = self.head(lv);
    let rw = self.head(rv);
    if lw == rw {
      return;
    }
    self.db.insert(lw.clone(), rw.clone());
    match self.tag.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.tag.remove(&lw);
        self.tag.insert(rw.clone(), t);
      }
    }
    match self.texp.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.texp.remove(&lw);
        self.texp.insert(rw.clone(), t);
      }
    }
  }

  fn unify_texp(&mut self, v: LTyvar, query: TyexpRef) {
    let w = self.head(v);
    self.texp.insert(w, query);
  }

  fn reduce(&mut self, v: LTyvar) -> TyReduce {
    let w = self.head(v);
    match self.texp.get(&w) {
      None => TyReduce::Var(w),
      Some(query) => {
        let query = query.clone();
        let query = self.reduce_texp(query);
        self.texp.insert(w, query.clone());
        TyReduce::Exp(query)
      }
    }
  }

  fn reduce_texp(&mut self, query: TyexpRef) -> TyexpRef {
    match &*query {
      // TODO: cases.
      &Tyexp::Var(ref v) => {
        match self.reduce(v.clone()) {
          TyReduce::Exp(e) => e,
          TyReduce::Var(w) => w.into(),
        }
      }
      &Tyexp::Fun(ref dom, ref ret) => {
        let mut dom_ = Vec::with_capacity(dom.len());
        for d in dom.iter() {
          dom_.push(self.reduce_texp(d.clone()));
        }
        let ret_ = self.reduce_texp(ret.clone());
        Tyexp::Fun(dom_, ret_).into()
      }
      &Tyexp::Tup |
      &Tyexp::Bit |
      &Tyexp::Int |
      &Tyexp::Flo |
      &Tyexp::Unit => query,
      _ => unimplemented!(),
    }
  }

  fn mgu_var(&mut self, var: LVar) -> Option<(LTyvar, LTyvar, LTyRef)> {
    match self._lookup_var(&var) {
      None => None,
      Some(v) => match self.mgu(v.clone()) {
        None => None,
        Some((w, e)) => Some((v, w, e)),
      }
    }
  }

  fn mgu_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> Option<(LTyvar, LTyvar, LTyRef)> {
    match self._lookup_exp(loc) {
      None => None,
      Some(v) => match self.mgu(v.clone()) {
        None => None,
        Some((w, e)) => Some((v, w, e)),
      }
    }
  }

  fn mgu(&mut self, v: LTyvar) -> Option<(LTyvar, LTyRef)> {
    let w = self.head(v);
    match self.texp.get(&w) {
      None => None,
      Some(query) => {
        let query = query.clone();
        match self.mgu_texp(query) {
          None => None,
          Some(e) => Some((w, e)),
        }
      }
    }
  }

  fn mgu_texp(&mut self, query: TyexpRef) -> Option<LTyRef> {
    let query = self.reduce_texp(query);
    self._mgu_reduced(query).ok()
  }

  fn _mgu_reduced(&mut self, query: TyexpRef) -> Result<LTyRef, ()> {
    match &*query {
      // TODO: cases.
      &Tyexp::Var(_) => Err(()),
      &Tyexp::Fun(ref dom, ref ret) => {
        let mut dom_ = Vec::with_capacity(dom.len());
        for d in dom.iter() {
          dom_.push(self._mgu_reduced(d.clone())?);
        }
        let ret_ = self._mgu_reduced(ret.clone())?;
        Ok(LTy::Fun(dom_, ret_).into())
      }
      &Tyexp::Bit => Ok(LTy::Bit.into()),
      &Tyexp::Int => Ok(LTy::Int.into()),
      &Tyexp::Flo => Ok(LTy::Flo.into()),
      &Tyexp::Unit => Ok(LTy::Unit.into()),
      _ => Err(()),
    }
  }
}

#[derive(Clone, Default)]
struct IncTyInfMachine {
}

impl IncTyInfMachine {
  fn _gen_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    let ety = tenv.lookup_exp(&exp);
    match &exp.term() {
      &LTerm::End => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Unit.into()));
        work.cons.push_front(con);
      }
      &LTerm::Break(ref inner) => {
        self._gen_exp(exp.lookup(inner), tenv, work);
        let brk_con = TyConRef::new(TyCon::Eq_(ety.into(), tenv.lookup_exp(inner).into()));
        work.cons.push_front(brk_con);
      }
      &LTerm::Apply(ref head, ref args) => {
        self._gen_exp(exp.lookup(head), tenv, work);
        let mut arg_tys = Vec::with_capacity(args.len());
        for a in args.iter() {
          self._gen_exp(exp.lookup(a), tenv, work);
          arg_tys.push(tenv.lookup_exp(a).into());
        }
        let app_con = TyConRef::new(TyCon::Eq_(tenv.lookup_exp(&head).into(), Tyexp::Fun(arg_tys, ety.into()).into()));
        work.cons.push_front(app_con);
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut param_tys = Vec::with_capacity(params.len());
        for p in params.iter() {
          let p_v = tenv.lookup_var(p);
          param_tys.push(p_v.into());
        }
        self._gen_exp(exp.lookup(body), tenv, work);
        let lam_con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Fun(param_tys, tenv.lookup_exp(body).into()).into()));
        work.cons.push_front(lam_con);
      }
      &LTerm::Import(ref _env, ref _body) => {
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }
      &LTerm::Export => {
        // TODO
        let ctx = exp.ctx();
        let mut keys: RedBlackTreeMap<LEnvKey, LTyvar> = Default::default();
        let mut hashes: RedBlackTreeMap<LIdent, LVar> = Default::default();
        for (binder, var) in ctx.bind_to_var.iter() {
          keys.insert_mut(LEnvKey::Var(var.clone()), tenv.lookup_var(var));
          match binder {
            &LVarBinder::Ident(ref hash) => {
              hashes.insert_mut(hash.clone(), var.clone());
            }
            &LVarBinder::Anon => {}
          }
        }
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Env(keys, hashes).into()));
        work.cons.push_front(con);
      }
      &LTerm::PtlD(ref target) => {
        // FIXME: should immediately defer the constraint here.
        self._gen_exp(exp.lookup(target), tenv, work);
        let con = TyConRef::new(TyCon::IsPtlD(ety.into(), tenv.lookup_exp(target).into()));
        work.cons.push_front(con);
        /*work.defer.push_front(TyDeferral::PtlD(ety.clone(), target.clone()));*/
      }
      &LTerm::AdjD(ref _target) => {
        unimplemented!();
      }
      &LTerm::Adj(ref _target) => {
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let name_v = tenv.lookup_var(name);
        self._gen_exp(exp.lookup(body), tenv, work);
        self._gen_exp(exp.lookup(rest), tenv, work);
        let let_con1 = TyConRef::new(TyCon::Eq_(name_v.into(), tenv.lookup_exp(body).into()));
        let let_con2 = TyConRef::new(TyCon::Eq_(ety.into(), tenv.lookup_exp(rest).into()));
        work.cons.push_front(let_con2);
        work.cons.push_front(let_con1);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixname_v = tenv.lookup_var(fixname);
        self._gen_exp(exp.lookup(fixbody), tenv, work);
        let fix_con1 = TyConRef::new(TyCon::Eq_(fixname_v.into(), tenv.lookup_exp(fixbody).into()));
        let fix_con2 = TyConRef::new(TyCon::Eq_(ety.into(), tenv.lookup_exp(fixbody).into()));
        work.cons.push_front(fix_con2);
        work.cons.push_front(fix_con1);
      }
      &LTerm::BitLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Bit.into()));
        work.cons.push_front(con);
      }
      &LTerm::IntLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Int.into()));
        work.cons.push_front(con);
      }
      &LTerm::FloLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Flo.into()));
        work.cons.push_front(con);
      }
      &LTerm::Lookup(ref name) => {
        let name_v = tenv.lookup_var(name);
        let con = TyConRef::new(TyCon::Eq_(ety.into(), name_v.into()));
        work.cons.push_front(con);
      }
      &LTerm::ProjectIdent(ref env, ref hash) => {
        // FIXME: should immediately defer this case.
        let env_con = self._gen_exp(exp.lookup(env), tenv, work);
        let hashsel_con = TyConRef::new(TyCon::IsProjIdent(ety.into(), tenv.lookup_exp(env).into(), hash.clone()));
        work.cons.push_front(hashsel_con);
        /*work.defer.push_front(TyDeferral::ProjIdent(ety.clone(), env.clone(), hash.clone()));*/
      }
      _ => unimplemented!(),
    }
  }

  fn gen(&mut self, tree: &LTreeCell, tenv: &mut TyEnv, work: &mut TyWork) {
    self._gen_exp(tree.root(), tenv, work);
  }

  /*fn gen_inc(&mut self, old_tree: &LTreeCell, new_tree: &LTreeCell) -> TyConRef {
    // TODO: things that could have changed:
    // - entirely new tree
    // - new root
    // - appended exprs
    // - existing exprs mutated to point to newly appended exprs
    // - existing exprs with more extensive term mutations
    if !Rc::ptr_eq(&old_tree.data, &new_tree.data) {
      return self.gen(new_tree);
    }
    unimplemented!();
  }*/

  fn inc_gen_adj(&mut self, tree: &LTreeCell, tenv: &mut TyEnv, work: &mut TyWork) {
    // TODO
    unimplemented!();
  }

  fn _solve_eq_var(&mut self, lv: LTyvar, rv: LTyvar, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) -> Result<(), ()> {
    let lquery = tenv.reduce(lv.clone());
    let rquery = tenv.reduce(rv.clone());
    match (lquery, rquery) {
      (TyReduce::Exp(lquery), TyReduce::Exp(rquery)) => {
        let con = TyConRef::new(TyCon::Eq_(lquery, rquery));
        work.cons.push_back(con);
        self.solve(root, tenv, work)
      }
      _ => {
        tenv.unify(lv, rv);
        self.solve(root, tenv, work)
      }
    }
  }

  fn _solve_eq_exp(&mut self, v: LTyvar, query: TyexpRef, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) -> Result<(), ()> {
    let lquery = tenv.reduce(v.clone());
    let rquery = tenv.reduce_texp(query.clone());
    match lquery {
      TyReduce::Exp(lquery) => {
        let con = TyConRef::new(TyCon::Eq_(lquery, rquery));
        work.cons.push_back(con);
        self.solve(root, tenv, work)
      }
      TyReduce::Var(_) => {
        tenv.unify_texp(v, rquery.clone());
        self.solve(root, tenv, work)
      }
    }
  }

  fn _debug_solve_dump(&mut self) {
    /*println!("DEBUG: solve: done");
    println!("DEBUG: solve:   # vtys:");
    //println!("DEBUG: solve:   {:?}", self.root.etys);
    println!("DEBUG: solve:   {:?}", root.tree.data.borrow().vtys);
    println!("DEBUG: solve:   # db:");
    for (lv, _) in tenv.db.clone().iter() {
      let lw = tenv.head(lv.clone());
      let q = match tenv.texp.get(&lw) {
        None => None,
        Some(e) => Some(tenv.reduce_texp(e.clone())),
      };
      println!("DEBUG: solve:   {:?} => {:?} :: {:?}", lv, lw, q);
    }
    println!("DEBUG: solve:   # texp:");
    for (v, t) in tenv.texp.iter() {
      println!("DEBUG: solve:   {:?} => {:?}", v, t);
    }*/
  }

  fn solve(&mut self, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) -> Result<(), ()> {
    let con = match work.cons.pop_front() {
      None => {
        //self._debug_solve_dump();
        return Ok(());
      }
      Some(c) => c,
    };
    match &*con {
      &TyCon::Top => {
        self.solve(root, tenv, work)
      }
      &TyCon::Eq_(ref lquery, ref rquery) => {
        match (&**lquery, &**rquery) {
          // TODO: cases.
          (&Tyexp::Var(ref lv), &Tyexp::Var(ref rv)) => {
            self._solve_eq_var(lv.clone(), rv.clone(), root, tenv, work)
          }
          (&Tyexp::Var(ref lv), _) => {
            self._solve_eq_exp(lv.clone(), rquery.clone(), root, tenv, work)
          }
          (_, &Tyexp::Var(ref rv)) => {
            self._solve_eq_exp(rv.clone(), lquery.clone(), root, tenv, work)
          }
          (&Tyexp::Fun(ref ldom, ref lret), &Tyexp::Fun(ref rdom, ref rret)) => {
            if ldom.len() != rdom.len() {
              println!("WARNING: Eq_: fun arity mismatch");
              work.unsat.push_back(con.clone());
            } else {
              for (ld, rd) in ldom.iter().zip(rdom.iter()) {
                work.cons.push_back(TyConRef::new(TyCon::Eq_(ld.clone(), rd.clone())));
              }
            }
            work.cons.push_back(TyConRef::new(TyCon::Eq_(lret.clone(), rret.clone())));
            self.solve(root, tenv, work)
          }
          (&Tyexp::Tup, &Tyexp::Tup) |
          (&Tyexp::Bit, &Tyexp::Bit) |
          (&Tyexp::Int, &Tyexp::Int) |
          (&Tyexp::Flo, &Tyexp::Flo) |
          (&Tyexp::Unit, &Tyexp::Unit) => {
            self.solve(root, tenv, work)
          }
          _ => {
            println!("WARNING: Eq_: type mismatch or unimpl");
            work.unsat.push_back(con);
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::Tagged(ref query, ref tag) => {
        // TODO
        //let query = tenv.reduce_texp(query.clone());
        match (&**query, tag) {
          (&Tyexp::Var(ref w), _) => {
            match tenv.tag.get(w) {
              None => {
                tenv.tag.insert(w.clone(), tag.clone());
                work.defer_cs.push_back(con.clone());
              }
              Some(etag) => if etag == tag {
                work.defer_cs.push_back(con.clone());
              } else {
                work.unsat.push_back(con);
              }
            }
            self.solve(root, tenv, work)
          }
          // TODO: cases.
          (_, _) => {
            work.defer_cs.push_back(con.clone());
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::IsPtlD(ref e, ref target) => {
        let target = tenv.reduce_texp(target.clone());
        match &*target {
          // TODO: missing cases.
          &Tyexp::Var(_) => {
            let con = TyConRef::new(TyCon::IsPtlD(e.clone(), target.clone()));
            work.cons.push_back(con);
            self.solve(root, tenv, work)
          }
          &Tyexp::Fun(ref dom, ref ret) => {
            match &**ret {
              &Tyexp::Var(_) => {
                let con = TyConRef::new(TyCon::IsPtlD(e.clone(), target.clone()));
                work.cons.push_back(con);
                self.solve(root, tenv, work)
              }
              &Tyexp::Flo => {
                println!("DEBUG: IsPtlD: differentiating a scalar Fun (... -> Flo)");
                let con = TyConRef::new(TyCon::Tagged(e.clone(), Tytag::PtlDf(dom.len())));
                work.cons.push_back(con);
                self.solve(root, tenv, work)
              }
              _ => {
                println!("WARNING: IsPtlD: differentiating a nonscalar Fun");
                work.unsat.push_back(con);
                self.solve(root, tenv, work)
              }
            }
          }
          &Tyexp::Flo => {
            println!("DEBUG: IsPtlD: differentiating a Flo");
            let con = TyConRef::new(TyCon::Tagged(e.clone(), Tytag::PtlDv));
            work.cons.push_back(con);
            self.solve(root, tenv, work)
          }
          _ => {
            println!("WARNING: IsPtlD: differentiating a nonscalar type");
            work.unsat.push_back(con);
            self.solve(root, tenv, work)
          }
        }
      }
      /*&TyCon::IsPtlD(ref e, ref tg) => {
        // TODO
        match tenv.mgu(tg.clone()).map(|t| &**t) {
          None => {
            /* FIXME: defer this constraint */
          }
          Some((_, &LTy::Flo)) => {
            // TODO TODO TODO: generate an adj hyp.
            println!("DEBUG: IsPtlD: differentiating a scalar type");
            let adj_ret_v = tenv.fresh_tvar();
            let adj_ty = Tyexp::Fun(vec![Tyexp::Flo.into()], adj_ret_v.into()).into();
            let tg_dv = tenv.lookup_adj(tg.clone());
            let con1 = TyConRef::new(TyCon::Eq_(tg_dv, adj_ty));
            let con2 = TyConRef::new(TyCon::Adj(tg.clone(), tg_dv));
            self.solve(root, tenv, work)
          }
          Some(_) => {
            println!("WARNING: IsPtlD: differentiating a nonscalar type");
            work.unsat.push_back(con);
            self.solve(root, tenv, work)
          }
        }
      }*/
      &TyCon::IsProjIdent(ref ety, ref env_ty, ref hash) => {
        // TODO
        match tenv.mgu_texp(env_ty.clone()).as_ref().map(|t| &**t) {
          None => {
            /* FIXME: defer this constraint */
            self.solve(root, tenv, work)
          }
          Some(&LTy::Env(ref keys, ref hashes)) => {
            match hashes.get(hash) {
              None => {
                // FIXME
                self.solve(root, tenv, work)
              }
              Some(key_var) => {
                if !keys.contains_key(&LEnvKey::Var(key_var.clone())) {
                  // FIXME
                  self.solve(root, tenv, work)
                } else {
                  let key_ty = tenv.lookup_var(key_var).into();
                  let con = TyConRef::new(TyCon::Eq_(ety.clone(), key_ty));
                  work.cons.push_back(con);
                  self.solve(root, tenv, work)
                }
              }
            }
          }
          Some(_) => {
            work.unsat.push_back(con);
            self.solve(root, tenv, work)
          }
        }
      }
      _ => unimplemented!(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct LCtxRef {
  // TODO
  version:      usize,
  //tree_version: usize,
  bind_to_var:  HashTrieMap<LVarBinder, LVar>,
  var_to_depth: HashTrieMap<LVar, usize>,
  var_stack:    Stack<LVar>,
}

impl LCtxRef {
  pub fn empty_top_level() -> LCtxRef {
    LCtxRef{
      version:      0,
      bind_to_var:  HashTrieMap::default(),
      var_to_depth: HashTrieMap::default(),
      var_stack:    Stack::default(),
    }
  }

  pub fn lookup_hash(&self, hash: LIdent) -> Option<LVar> {
    match self.bind_to_var.get(&LVarBinder::Ident(hash)) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  pub fn bind_mut<B: Into<LVarBinder>>(&mut self, into_binder: B, var: LVar) {
    let binder: LVarBinder = into_binder.into();
    self.bind_to_var.insert_mut(binder, var.clone());
    self.var_to_depth.insert_mut(var.clone(), self.var_stack.size());
    self.var_stack.push_mut(var);
  }
}

#[derive(Clone, Default, Debug)]
pub struct LTyctxRef {
  tvar_ctr:     u64,
  var_to_ty:    HashTrieMap<LVar, (LTyvar, LTyvar, LTyRef)>,
}

impl LTyctxRef {
  /*pub fn lookup_var(&self, var: &LVar) -> Option<LTy> {
    match self.var_to_tyvar.get(var) {
      None => None,
      Some(tv) => Some(tv.clone()),
    }
  }*/
}

/*#[derive(Default, Debug)]
struct AdjEnv {
  vars: HashMap<LVar, LVar>,
  bound_adjs: HashSet<LVar>,
}

impl AdjEnv {
  fn has_adj(&self, var: &LVar) -> bool {
    self.vars.contains_key(var)
  }

  fn is_bound_adj(&self, adj: &LVar) -> bool {
    self.bound_adjs.contains(adj)
  }

  fn unsafe_bind_adj(&mut self, adj: LVar) {
    self.bound_adjs.insert(adj);
  }
}*/

/*#[derive(Clone)]
pub struct LRel {
  pub label:    LLabel,
  pub offset:   isize,
}

impl LRel {
  pub fn new(label: LLabel, pos: usize, ref_pos: usize) -> LRel {
    // NB: Should not assume anything about the relative order of this expr
    // vs the reference expr!
    /*assert!(pos > ref_pos);*/
    LRel{
      label,
      offset:   pos as isize - ref_pos as isize,
    }
  }
}*/

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LLoc {
  pub label:    LLabel,
  pub pos:      usize,
}

impl AsRef<LLabel> for LLoc {
  fn as_ref(&self) -> &LLabel {
    &self.label
  }
}

impl LLoc {
  pub fn new(label: LLabel, pos: usize) -> LLoc {
    LLoc{
      label,
      pos,
    }
  }

  pub fn new2(label: LLabel, pos: usize, _: usize) -> LLoc {
    LLoc{
      label,
      pos,
    }
  }
}

#[derive(Clone, Debug)]
pub struct LMLoc {
  pub label:    LLabel,
  pub pos:      usize,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  // TODO
  pub version:  usize,
  //pub up:       LLoc,
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Debug)]
pub enum LDelta {
  Append(LLoc),
  Rewrite(LLoc),
}

#[derive(Default, Debug)]
pub struct LTreeIndex {
  ptld:     BTreeSet<(LLoc, LLoc)>,
  adjd:     BTreeSet<(LLoc, LLoc)>,
  tngd:     BTreeSet<(LLoc, LLoc)>,
  jac:      BTreeSet<(LLoc, LLoc)>,
  adj:      BTreeSet<(LLoc, LLoc)>,
  tng:      BTreeSet<(LLoc, LLoc)>,
}

#[derive(Default)]
pub struct LTree {
  //reqs:     Vec<_>,
  mexps:    Vec<LMExpr>,
  exps:     Vec<LExpr>,
  history:  Vec<(usize, LDelta)>,
  index:    HashMap<LLabel, usize>,
  ctxs:     HashMap<LLabel, LCtxRef>,
  //index:    LTreeIndex,
}

#[derive(Clone, Debug)]
pub struct LTreeView {
  root:     LLoc,
  epoch:    usize,
  version:  usize,
  //revision: usize,
  //changed:  bool,
}

impl From<LTreeViewCell> for LTreeView {
  fn from(view: LTreeViewCell) -> LTreeView {
    view.data.borrow().clone()
  }
}

#[derive(Clone, Debug)]
pub struct LTreeViewCell {
  data: Rc<RefCell<LTreeView>>,
}

impl From<LTreeView> for LTreeViewCell {
  fn from(view: LTreeView) -> LTreeViewCell {
    LTreeViewCell{data: Rc::new(RefCell::new(view))}
  }
}

#[derive(Clone)]
pub struct LTreeCell {
  view: LTreeView,
  data: Rc<RefCell<LTree>>,
}

impl LTreeCell {
  pub fn root(&self) -> LExprCell {
    let data = self.data.borrow();
    let label = data.exps[self.view.root.pos].label.clone();
    assert_eq!(self.view.root.label, label);
    LExprCell{
      view:     LTreeViewCell::from(self.view.clone()),
      tree:     self.clone(),
      pos:      self.view.root.pos,
      label,
    }
  }

  pub fn root_ctx(&self) -> Option<LCtxRef> {
    let mut exp = self.root();
    loop {
      match exp.term() {
        LTerm::End => {
          break;
        }
        LTerm::Let(_, _, ref rest) => {
          exp = exp.lookup(rest);
        }
        _ => {
          return None;
        }
      }
    }
    Some(exp.ctx())
  }

  fn final_tctx(&self, ctx: &LCtxRef, tenv: &mut TyEnv) -> Option<LTyctxRef> {
    let tree = self.data.borrow();
    let mut tctx = LTyctxRef::default();
    for var in ctx.var_stack.iter() {
      let v = match tenv._lookup_var(var) {
        None => {
          //println!("DEBUG: resolve_ctx: no tvar");
          return None;
        }
        Some(v) => v,
      };
      match tenv.mgu(v.clone()) {
        None => {
          //println!("DEBUG: resolve_ctx: no mgu");
          return None;
        }
        Some((w, ty)) => {
          tctx.var_to_ty.insert_mut(var.clone(), (v, w, ty));
        }
      }
    }
    Some(tctx)
  }
}

#[derive(Clone)]
pub struct LExprCell {
  pub view:     LTreeViewCell,
  pub tree:     LTreeCell,
  pub pos:      usize,
  pub label:    LLabel,
}

impl AsRef<LLabel> for LExprCell {
  fn as_ref(&self) -> &LLabel {
    &self.label
  }
}

impl LExprCell {
  pub fn loc(&self) -> LLoc {
    LLoc{
      label:    self.label.clone(),
      pos:      self.pos,
    }
  }

  pub fn term(&self) -> LTerm {
    let tree = self.tree.data.borrow();
    let exp = tree.exps[self.pos].clone();
    assert_eq!(self.label, exp.label);
    exp.term
  }

  fn unsafe_set_self_root(&self) {
    let mut view = self.view.data.borrow_mut();
    view.root = LLoc::new(self.label.clone(), self.pos);
    view.epoch += 1;
  }

  fn unsafe_set_ctx(&self, new_ctx: LCtxRef) {
    let mut tree = self.tree.data.borrow_mut();
    tree.ctxs.insert(self.label.clone(), new_ctx);
  }

  fn unsafe_unset_ctx(&self) {
    let mut tree = self.tree.data.borrow_mut();
    tree.ctxs.remove(&self.label);
  }

  pub fn ctx(&self) -> LCtxRef {
    let tree = self.tree.data.borrow();
    match tree.ctxs.get(&self.label) {
      None => panic!("bug"),
      Some(ctx) => ctx.clone()
    }
  }

  pub fn lookup(&self, loc: &LLoc) -> LExprCell {
    let tree = self.tree.data.borrow();
    assert_eq!(loc.label, tree.exps[loc.pos].label);
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      loc.pos,
      label:    loc.label.clone(),
    }
  }

  pub fn lookup_exp<L: AsRef<LLabel>>(&self, loc: &L) -> LExprCell {
    let label = loc.as_ref();
    let tree = self.tree.data.borrow();
    let pos = match tree.index.get(label) {
      None => panic!(),
      Some(pos) => *pos,
    };
    assert_eq!(label, &tree.exps[pos].label);
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      pos,
      label:    label.clone(),
    }
  }

  pub fn append_mexp(&self) {
    // TODO
    unimplemented!();
  }

  pub fn append(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LTerm) -> LExprCell {
    let new_label = builder.fresh_label();
    self._append(new_label, builder, mk_term)
  }

  pub fn _append(&self, new_label: LLabel, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LTerm) -> LExprCell {
    //let new_term = (mk_term)(());
    let new_term = (mk_term)(builder);
    let new_pos = {
      let mut view = self.view.data.borrow_mut();
      let mut tree = self.tree.data.borrow_mut();
      let root = view.root.clone();
      let new_pos = tree.exps.len();
      view.version += 1;
      assert!(view.version != 0);
      // TODO
      /*match &new_term {
        &LTerm::PtlD(..) => tree.index.ptld.insert((root, LLoc::new(new_label.clone(), new_pos))),
        &LTerm::AdjD(..) => tree.index.adjd.insert((root, LLoc::new(new_label.clone(), new_pos))),
        &LTerm::TngD(..) => tree.index.tngd.insert((root, LLoc::new(new_label.clone(), new_pos))),
        &LTerm::Jac(..) => tree.index.jac.insert((root, LLoc::new(new_label.clone(), new_pos))),
        &LTerm::Adj(..) => tree.index.adj.insert((root, LLoc::new(new_label.clone(), new_pos))),
        &LTerm::Tng(..) => tree.index.tng.insert((root, LLoc::new(new_label.clone(), new_pos))),
        _ => false,
      };*/
      tree.exps.push(LExpr{
        version:  view.version,
        label:    new_label.clone(),
        term:     new_term,
      });
      tree.history.push((view.version, LDelta::Append(LLoc::new(new_label.clone(), new_pos))));
      assert_eq!(view.version, tree.history.len());
      tree.index.insert(new_label.clone(), new_pos);
      new_pos
    };
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      new_pos,
      label:    new_label,
    }
  }

  pub fn unsafe_rewrite(&self, /*builder: &mut LBuilder,*/ rw_term: &mut dyn FnMut(&mut LTerm)) {
    // TODO
    let mut view = self.view.data.borrow_mut();
    let mut tree = self.tree.data.borrow_mut();
    let root = view.root.clone();
    view.version += 1;
    assert!(view.version != 0);
    (rw_term)(&mut tree.exps[self.pos].term);
    tree.exps[self.pos].version = view.version;
    tree.history.push((view.version, LDelta::Rewrite(LLoc::new(self.label.clone(), self.pos))));
    assert_eq!(view.version, tree.history.len());
  }

  /*pub fn unsafe_rewrite(self, mk_term: &dyn Fn() -> LTerm) -> LExprCell {
    // FIXME: should invalidate associated info, like the ctx tree.
    let new_term = (mk_term)();
    {
      let mut tree = self.tree.data.borrow_mut();
      assert_eq!(self.label, tree.exps[self.pos].label);
      tree.deltas.push(LLoc::new(self.label.clone(), self.pos));
      tree.exps[self.pos] = LExpr{
        label:  self.label.clone(),
        term:   new_term,
      };
    }
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      self.pos,
      label:    self.label,
    }
  }*/
}

pub type LCodeRef = Rc<LCode>;

pub struct LCode {
  pub mexps:    Vec<LMExpr>,
  pub exps:     Vec<LExpr>,
}

#[derive(Clone)]
pub struct LExprRef {
  pub code:     LCodeRef,
  pub pos:      usize,
  pub label:    LLabel,
  //pub term:     LTerm,
}

impl LExprRef {
  /*pub fn jump(self, rel: LRel) -> LExprRef {
    let new_posi = self.pos as isize + rel.offset;
    assert!(new_posi >= 0);
    let new_pos = new_posi as usize;
    let new_exp = self.code.exps[new_pos].clone();
    assert_eq!(new_exp.label, rel.label);
    LExprRef{
      code:     self.code,
      pos:      new_pos,
      label:    new_exp.label,
      term:     new_exp.term,
    }
  }*/

  pub fn jump(&self, loc: &LLoc) -> LExprRef {
    // TODO
    unimplemented!();
  }

  pub fn term(&self) -> LTerm {
    // TODO
    unimplemented!();
  }
}

pub struct LModule {
  // TODO
  pub tree:     LTreeCell,
  //pub code:     LCodeRef,
  pub end_ctx:  Option<LCtxRef>,
  pub end_tctx: Option<LTyctxRef>,
}
