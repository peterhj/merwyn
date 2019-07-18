// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::mach::{MAddr, MBLambda, MCUnsafeLambda};

use rpds::{HashTrieMap, Queue, RedBlackTreeMap, Stack};

use std::cell::{RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{Write as FmtWrite, Error as FmtError};
use std::io::{Write as IoWrite, Cursor, Error as IoError, stdout};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

type RBTreeMap<K, V> = RedBlackTreeMap<K, V>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LLabel(u64);

impl AsRef<LLabel> for LLabel {
  fn as_ref(&self) -> &LLabel {
    self
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LMLabel(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LIdent(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LVar(u64);

/*#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LEnvKey {
  Var(LVar),
  Pos(usize),
}*/

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

pub type LETerm = LTerm<usize, usize>;

#[derive(Clone, Debug)]
pub enum LTerm<E=LLoc, ME=LMLoc> {
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
  ACons(LVar, Option<LIdent>, E, E),
  AConcat(E, E),
  AApp(Vec<(usize, LVar, Option<LIdent>)>, E),
  ERet(Vec<LVar>, Vec<(usize, LVar)>, E),
  PtlD(E),
  AdjD(E),
  TngD(E),
  Jac(E),
  Adj(E),
  Tng(E),
  Let(LVar, E, E),
  Fix(LVar, E),
  //SFix(Vec<(LVar, E)>),
  //Alt(LVar, LVar, E, E),
  Match(E, Vec<(LPatRef, E)>),
  Cons(E, E),
  Concat(E, E),
  STuple(Vec<E>),
  Tuple(Vec<E>),
  UnitLit,
  BitLit(bool),
  IntLit(i64),
  FlpLit(f64),
  Lookup(LVar),
  ProjectIdent(E, LIdent),
  Unbind(LVar, E),
  MX(ME),
}

#[derive(Clone)]
pub struct LMExpr {
  pub mlabel:   LMLabel,
  pub mterm:    LMTerm,
}

#[derive(Clone)]
pub enum LMTerm {
  Deref(MAddr),
  BLam(LMLambdaDef<MBLambda>),
  CLam(LMLambdaDef<MCUnsafeLambda>),
}

#[derive(Clone)]
pub struct LMLambdaDef<Lam> {
  pub ar:   usize,
  pub cg:   Option<Rc<dyn Fn() -> Lam>>,
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

enum RegisterAdj {
  Primal,
  Bridge(LLabel),
  Dual(LLabel),
  Pair(LLabel),
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
  //adj_exp:      HashTrieMap<LLabel, LLabel>,
  //adj_snd_exp:  HashTrieMap<LLabel, LLabel>,
  reg_adj:      HashTrieMap<LLabel, RegisterAdj>,
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

  pub fn lookup_ident(&self, ident: &LIdent) -> String {
    match self.hash_to_name.get(ident) {
      None => panic!(),
      Some(name) => name.to_owned(),
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

  pub fn fresh_ident_var(&mut self, ident: LIdent) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    let new_var = LVar(self.var_ctr);
    assert!(!self.var_to_bind.contains_key(&new_var));
    self.var_to_bind.insert_mut(new_var.clone(), LVarBinder::Ident(ident));
    new_var
  }

  pub fn lookup_var(&self, var: &LVar) -> LVarBinder {
    match self.var_to_bind.get(var) {
      None => panic!("bug"),
      Some(binder) => binder.clone(),
    }
  }

  pub fn _lookup_adj_var(&self, var: &LVar) -> Option<LVar> {
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

  /*pub fn _lookup_adj_exp<L: AsRef<LLabel>>(&mut self, loc: &L) -> Option<LLabel> {
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
  }*/

  pub fn compile(&mut self, htree: Rc<HExpr>) -> Result<LModule, ()> {
    // TODO
    unimplemented!();
  }

  pub fn _compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef, top_tctx: LTyctxRef) -> Result<LModule, ()> {
    // TODO
    let tree = self._lower(htree, top_ctx.clone());
    let tree = self._normalize(tree);
    let tree = self._recontext(tree, top_ctx.clone());
    // FIXME: derive tenv from base tctx.
    let mut tenv = TyEnv::default();
    //let mut tenv = TyEnv::from_tctx(&top_tctx);
    let mut t_work = TyWork::default();
    self.tyinf.gen(&tree, &mut tenv, &mut t_work);
    self.tyinf.solve(tree.root(), &mut tenv, &mut t_work);
    //println!("DEBUG: compile: tyinf result: {:?}", ty_res);
    //println!("DEBUG: compile:   defer: {:?}", t_work.defer_cs);
    //println!("DEBUG: compile:   unsat: {:?}", t_work.unsat);
    if t_work.unsat() {
      return Err(());
    }
    /*let tree = match self._resolve_adj(tree, &mut tenv) {
      ResolveAdjResult::Primal(tree) |
      ResolveAdjResult::Bridge(tree) => tree,
      _ => return Err(()),
    };*/
    let mut tree = tree;
    while t_work.defer_adj() {
      match self._resolve_adj(tree, &mut tenv) {
        ResolveAdjResult::Primal(_) => unreachable!(),
        ResolveAdjResult::Bridge(new_tree) => {
          tree = new_tree;
          self.tyinf.gen(&tree, &mut tenv, &mut t_work);
          self.tyinf.solve(tree.root(), &mut tenv, &mut t_work);
          break;
        }
        ResolveAdjResult::Defer(old_tree, a_work) => {
          tree = old_tree;
          self.tyinf.gen_inc_adj(&tree, &a_work, &mut tenv, &mut t_work);
          self.tyinf.solve(tree.root(), &mut tenv, &mut t_work);
        }
        ResolveAdjResult::Error(_, _) => {
          // TODO: error reporting.
          return Err(());
        }
      }
    }
    let tree = self._recontext(tree, top_ctx.clone());
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

  pub fn _write<W: IoWrite>(&self, tree: LTreeCell, writer: &mut W) -> Result<(), IoError> {
    let mut print_box = PrintBox{left_indent: 0, line_nr: 1};
    print_box.print(self, tree, writer)
  }

  pub fn _print(&self, tree: LTreeCell) {
    assert!(self._write(tree, &mut stdout().lock()).is_ok());
  }
}

struct LowerWork {
  errors:   VecDeque<()>,
}

impl LBuilder {
  fn _lower_ty_rec(&mut self, htree: Rc<HExpr>) -> LTyRef {
    // TODO
    unimplemented!();
  }

  fn _lower_pat_rec(&mut self, htree: Rc<HExpr>, _other: ()) -> LPatRef {
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

  fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_ident(op_hash) {
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

  fn _lower_binop(&mut self, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_ident(op_hash) {
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

  fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, /*up: LLoc, label: LLabel,*/ pos: usize) -> (LLabel, usize) {
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
          let p_var = self.fresh_ident_var(p_hash.clone());
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
      &HExpr::PartialAltD(..) => {
        unimplemented!();
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
        let n_var = self.fresh_ident_var(n_hash.clone());
        let prev_n_var = if attrs.alt {
          match ctx.lookup_ident(n_hash.clone()) {
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
      &HExpr::FlpLit(x) => {
        let label = self.fresh_label();
        let e = LExpr{
          version:  0,
          label:    label.clone(),
          term:     LTerm::FlpLit(x)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.lookup_name(name);
        let name_var = match ctx.lookup_ident(name_hash) {
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
  fn _normalize_kont(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
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
      &LTerm::FlpLit(_) => kont(self, exp),
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

  fn _normalize_term(&mut self, exp: LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |_, exp| exp)
  }

  fn _normalize_names(&mut self, mut pre_exps: Queue<LExprCell>, post_exps: Queue<LExprCell>, kont: &mut dyn FnMut(&mut Self, Queue<LExprCell>) -> LExprCell) -> LExprCell {
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

  fn _normalize_name(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |this, exp| {
      match &exp.term() {
        &LTerm::BitLit(_) => kont(this, exp),
        &LTerm::IntLit(_) => kont(this, exp),
        &LTerm::FlpLit(_) => kont(this, exp),
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
  fn _recontext_exp(&mut self, exp: LExprCell, ctx: LCtxRef) {
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
      &LTerm::Env(_) => {}
      &LTerm::ACons(.., ref value, ref target) => {
        self._recontext_exp(exp.lookup(value), ctx.clone());
        self._recontext_exp(exp.lookup(target), ctx.clone());
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        self._recontext_exp(exp.lookup(lhs), ctx.clone());
        self._recontext_exp(exp.lookup(rhs), ctx.clone());
      }
      &LTerm::AApp(.., ref target) => {
        self._recontext_exp(exp.lookup(target), ctx.clone());
      }
      &LTerm::ERet(.., ref target) => {
        self._recontext_exp(exp.lookup(target), ctx.clone());
      }
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
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        self._recontext_exp(exp.lookup(query), ctx.clone());
        for &(ref pat, ref arm) in pat_arms.iter() {
          let pvs = pat.vars();
          let mut arm_ctx = ctx.clone();
          for pv in pvs.iter() {
            arm_ctx.bind_mut(self.lookup_var(pv), pv.clone());
          }
          self._recontext_exp(exp.lookup(arm), arm_ctx);
        }
      }
      /*&LTerm::Alt(ref name, ref alt_name, ref body, ref rest) => {
        let mut rest_ctx = ctx.clone();
        rest_ctx.bind_mut(self.lookup_var(alt_name), alt_name.clone());
        self._recontext_exp(exp.lookup(body), ctx);
        self._recontext_exp(exp.lookup(rest), rest_ctx);
      }*/
      &LTerm::STuple(ref elems) => {
        for elem in elems.iter() {
          self._recontext_exp(exp.lookup(elem), ctx.clone());
        }
      }
      &LTerm::BitLit(_) => {}
      &LTerm::IntLit(_) => {}
      &LTerm::FlpLit(_) => {}
      &LTerm::Lookup(_) => {}
      &LTerm::ProjectIdent(ref env, _) => {
        self._recontext_exp(exp.lookup(env), ctx);
      }
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _recontext: unhandled term: {:?}", t);
      }
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

enum ResolveAdj<E> {
  Primal(E),
  Bridge(E),
  Dual(E, E),
  Pair(E),
  Defer,
  Error,
}

enum ResolveAdjResult<E> {
  Primal(E),
  Bridge(E),
  Defer(E, AdjWork),
  Error(E, AdjWork),
}

#[derive(Debug)]
enum AdjError {
  //Nonscalar,
  Nonsmooth,
  Type,
}

#[derive(Default)]
struct AdjWork {
  appended:     VecDeque<LLabel>,
  deferred:     VecDeque<LLabel>,
  errored:      VecDeque<(LLabel, AdjError)>,
}

impl LBuilder {
  fn _resolve_adj(&mut self, tree: LTreeCell, tenv: &mut TyEnv) -> ResolveAdjResult<LTreeCell> {
    let mut work = AdjWork::default();
    match self._resolve_adj_exp(tree.root(), tenv, &mut work) {
      ResolveAdj::Primal(_) => ResolveAdjResult::Primal(tree),
      ResolveAdj::Bridge(new_root) => {
        new_root.unsafe_set_self_root();
        ResolveAdjResult::Bridge(LTreeCell{
          view: new_root.view.into(),
          data: new_root.tree.data.clone(),
        })
      }
      ResolveAdj::Dual(_, _) |
      ResolveAdj::Pair(_) => unreachable!(),
      ResolveAdj::Defer => ResolveAdjResult::Defer(tree, work),
      ResolveAdj::Error => ResolveAdjResult::Error(tree, work),
    }
  }

  fn _register_adj(&mut self, exp: &LExprCell, a_work: &mut AdjWork, adj: ResolveAdj<LExprCell>) -> ResolveAdj<LExprCell> {
    match &adj {
      &ResolveAdj::Primal(_) => {
        self.reg_adj.insert_mut(exp.as_ref().clone(), RegisterAdj::Primal);
      }
      &ResolveAdj::Bridge(ref adj_e) => {
        a_work.appended.push_front(adj_e.as_ref().clone());
        self.reg_adj.insert_mut(exp.as_ref().clone(), RegisterAdj::Bridge(adj_e.as_ref().clone()));
      }
      &ResolveAdj::Dual(_, ref adj_e) => {
        a_work.appended.push_front(adj_e.as_ref().clone());
        self.reg_adj.insert_mut(exp.as_ref().clone(), RegisterAdj::Dual(adj_e.as_ref().clone()));
      }
      &ResolveAdj::Pair(ref adj_e) => {
        a_work.appended.push_front(adj_e.as_ref().clone());
        self.reg_adj.insert_mut(exp.as_ref().clone(), RegisterAdj::Pair(adj_e.as_ref().clone()));
      }
      _ => unreachable!(),
    }
    adj
  }

  fn _resolve_adj_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    /* NB: An example where `resolve_` does not return a primal or bridge
       expr:

          \f, x. d[f[x]].x
       =>
          \(f, f'), x. let match (_, a) = f'[x] in a[1.0].x

       i.e. there is no way to preserve the original signature.
    */
    match self.reg_adj.get(exp.as_ref()) {
      Some(&RegisterAdj::Primal) => {
        return ResolveAdj::Primal(exp);
      }
      Some(&RegisterAdj::Bridge(ref adj_e)) => {
        return ResolveAdj::Bridge(exp.lookup_exp(adj_e));
      }
      Some(_) => unreachable!(),
      None => {}
    }
    match &exp.term() {
      &LTerm::PtlD(ref target) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Flp => {
              let target_e = exp.lookup(target);
              let adj_target_e = match self._force_adj_dual_exp(target_e, tenv, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(_) |
                ResolveAdj::Pair(_) => unreachable!(),
                ResolveAdj::Dual(_, adj_target_e) => adj_target_e,
                ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              };
              let unit_sink_e = exp.append(self, &mut |_| LTerm::FlpLit(1.0));
              let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                  adj_target_e.loc(),
                  vec![unit_sink_e.loc()]
              ));
              self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
            }
            _ => {
              // TODO: distinguish b/w nonscalar and nonsmooth cases.
              work.errored.push_back((exp.label(), AdjError::Nonsmooth));
              ResolveAdj::Error
            }
          }
        } else {
          work.deferred.push_back(exp.label());
          ResolveAdj::Defer
        }
      }
      &LTerm::End => {
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::Apply(ref head, ref args) => {
        let head_e = exp.lookup(head);
        match self._resolve_adj_exp(head_e, tenv, work) {
          ResolveAdj::Primal(head_e) => {
            let mut any_bridge = false;
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args.iter() {
              let arg_e = exp.lookup(arg);
              match self._resolve_adj_exp(arg_e, tenv, work) {
                ResolveAdj::Primal(arg_e) => {
                  new_args.push(arg_e);
                }
                ResolveAdj::Bridge(arg_e) => {
                  any_bridge = true;
                  new_args.push(arg_e);
                }
                ResolveAdj::Dual(_, _) |
                ResolveAdj::Pair(_) => unreachable!(),
                ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              }
            }
            if any_bridge {
              let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                  head_e.loc(),
                  new_args.iter().map(|e| e.loc()).collect()
              ));
              self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
            } else {
              self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
            }
          }
          ResolveAdj::Bridge(new_head_e) => {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args.iter() {
              let arg_e = exp.lookup(arg);
              match self._resolve_adj_exp(arg_e, tenv, work) {
                ResolveAdj::Primal(arg_e) => {
                  new_args.push(arg_e);
                }
                ResolveAdj::Bridge(arg_e) => {
                  new_args.push(arg_e);
                }
                ResolveAdj::Dual(_, _) |
                ResolveAdj::Pair(_) => unreachable!(),
                ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              }
            }
            let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                new_head_e.loc(),
                new_args.iter().map(|e| e.loc()).collect()
            ));
            self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
          }
          ResolveAdj::Dual(_, _) |
          ResolveAdj::Pair(_) => unreachable!(),
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body_e = exp.lookup(body);
        match self._resolve_adj_exp(body_e, tenv, work) {
          ResolveAdj::Primal(_) => {
            self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
          }
          ResolveAdj::Bridge(new_body_e) => {
            // FIXME: need to look into the params types.
            // FIXME: this case below assumes all types are scalar or vector,
            // rather than functional.
            let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
                params.clone(),
                new_body_e.loc()
            ));
            self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
          }
          ResolveAdj::Dual(_, _) |
          ResolveAdj::Pair(_) => unreachable!(),
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body_e = exp.lookup(body);
        let rest_e = exp.lookup(rest);
        match self._resolve_adj_exp(rest_e, tenv, work) {
          ResolveAdj::Primal(rest_e) => {
            match self._resolve_adj_exp(body_e, tenv, work) {
              ResolveAdj::Primal(_) => {
                self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
              }
              ResolveAdj::Bridge(new_body_e) => {
                let new_exp = exp.append(self, &mut |_| LTerm::Let(
                    name.clone(),
                    new_body_e.loc(),
                    rest_e.loc()
                ));
                self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
              }
              ResolveAdj::Dual(_, _) |
              ResolveAdj::Pair(_) => unreachable!(),
              ResolveAdj::Defer => ResolveAdj::Defer,
              ResolveAdj::Error => ResolveAdj::Error,
            }
          }
          ResolveAdj::Bridge(new_rest_e) => {
            match self._lookup_adj_var(name) {
              None => match self._resolve_adj_exp(body_e, tenv, work) {
                ResolveAdj::Primal(body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      body_e.loc(),
                      new_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
                }
                ResolveAdj::Bridge(new_body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      new_body_e.loc(),
                      new_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
                }
                ResolveAdj::Dual(_, _) |
                ResolveAdj::Pair(_) => unreachable!(),
                ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              },
              Some(adj_name) => match self._force_adj_pair_exp(body_e, tenv, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(_) |
                ResolveAdj::Dual(_, _) => unreachable!(),
                ResolveAdj::Pair(adj_body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Match(
                      adj_body_e.loc(),
                      vec![(
                        LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                        new_rest_e.loc()
                      )]
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
                }
                ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              }
            }
          }
          ResolveAdj::Dual(_, _) |
          ResolveAdj::Pair(_) => unreachable!(),
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        unimplemented!();
      }
      &LTerm::STuple(ref elems) => {
        // TODO
        unimplemented!();
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) |
      &LTerm::Lookup(_) => {
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::ProjectIdent(ref target, ref ident) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            //&LTy::Env(ref keys, ref idents) => {
            &LTy::Env(ref _idxs, ref keys, ref idents) => {
              match idents.get(ident) {
                Some(var) => {
                  match keys.get(var) {
                    Some(_) => {}
                    None => unreachable!(),
                  }
                  let target_e = exp.lookup(target);
                  match self._resolve_adj_exp(target_e, tenv, work) {
                    ResolveAdj::Primal(target_e) => {
                      let lookup_e = exp.append(self, &mut |_| LTerm::Lookup(var.clone()));
                      let new_exp = exp.append(self, &mut |_| LTerm::ImportR(
                          vec![var.clone()],
                          target_e.loc(),
                          lookup_e.loc()
                      ));
                      self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
                    }
                    ResolveAdj::Bridge(new_target_e) => {
                      let lookup_e = exp.append(self, &mut |_| LTerm::Lookup(var.clone()));
                      let new_exp = exp.append(self, &mut |_| LTerm::ImportR(
                          vec![var.clone()],
                          new_target_e.loc(),
                          lookup_e.loc()
                      ));
                      self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp))
                    }
                    ResolveAdj::Dual(_, _) |
                    ResolveAdj::Pair(_) => unreachable!(),
                    ResolveAdj::Defer => ResolveAdj::Defer,
                    ResolveAdj::Error => ResolveAdj::Error,
                  }
                }
                None => {
                  work.errored.push_back((exp.label(), AdjError::Type));
                  ResolveAdj::Error
                }
              }
            }
            _ => {
              work.errored.push_back((exp.label(), AdjError::Type));
              ResolveAdj::Error
            }
          }
        } else {
          work.deferred.push_back(exp.label());
          ResolveAdj::Defer
        }
      }
      // TODO
      _ => unimplemented!(),
    }
  }

  fn _force_adj_dual_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    match self.reg_adj.get(exp.as_ref()) {
      Some(&RegisterAdj::Dual(ref adj_e)) => {
        let adj_exp = exp.lookup_exp(adj_e);
        return ResolveAdj::Dual(exp, adj_exp);
      }
      Some(_) => unreachable!(),
      None => {}
    }
    match &exp.term() {
      // TODO: cases.
      &LTerm::FlpLit(_) => {
        let tmp_sink = self.fresh_anon_var();
        let nil_env_e = exp.append(self, &mut |_| LTerm::Env(vec![]));
        let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
            vec![tmp_sink.clone()],
            nil_env_e.loc()
        ));
        self._register_adj(&exp, work, ResolveAdj::Dual(exp.clone(), new_exp))
      }
      &LTerm::Lookup(ref var) => {
        let adj_var = self.lookup_adj_var(var);
        let new_exp = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
        self._register_adj(&exp, work, ResolveAdj::Dual(exp.clone(), new_exp))
      }
      _ => unimplemented!(),
    }
  }

  fn _force_adj_pair_exp(&mut self, exp: LExprCell, tenv: &mut TyEnv, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    match self.reg_adj.get(exp.as_ref()) {
      Some(&RegisterAdj::Pair(ref adj_e)) => {
        return ResolveAdj::Pair(exp.lookup_exp(adj_e));
      }
      Some(_) => unreachable!(),
      None => {}
    }
    match &exp.term() {
      // TODO: cases.
      &LTerm::Apply(ref head, ref args) => {
        let head_e = exp.lookup(head);
        match self._force_adj_dual_exp(head_e, tenv, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(_) |
          ResolveAdj::Pair(_) => unreachable!(),
          ResolveAdj::Dual(_, adj_head_e) => {
            let tmp_new = self.fresh_anon_var();
            let tmp_adj = self.lookup_adj_var(&tmp_new);
            let tmp_sink = self.fresh_anon_var();
            let adj_app_e = exp.append(self, &mut |_| LTerm::Apply(
                adj_head_e.loc(),
                args.clone()
            ));
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj.clone()));
            let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
            let adj_app_app_e = exp.append(self, &mut |_| LTerm::Apply(
                tmp_adj_e.loc(),
                vec![tmp_sink_e.loc()]
            ));
            let mut adj_app_app_fixup_args = Vec::with_capacity(args.len());
            for (idx, arg) in args.iter().enumerate() {
              let arg_e = exp.lookup(arg);
              match &arg_e.term() {
                &LTerm::FlpLit(_) => {}
                &LTerm::Lookup(ref arg_var) => {
                  let arg_ident = match self.lookup_var(arg_var) {
                    LVarBinder::Ident(ident) => Some(ident),
                    _ => None,
                  };
                  adj_app_app_fixup_args.push((idx, arg_var.clone(), arg_ident));
                }
                _ => unimplemented!(),
              }
            }
            let adj_app_app_fixup_e = exp.append(self, &mut |_| LTerm::AApp(
                adj_app_app_fixup_args.clone(),
                adj_app_app_e.loc()
            ));
            let mut target_e = adj_app_app_fixup_e;
            for arg in args.iter().rev() {
              let arg_e = exp.lookup(arg);
              match &arg_e.term() {
                &LTerm::FlpLit(_) => {}
                &LTerm::Lookup(ref arg_var) => {
                  let arg_adj = self.lookup_adj_var(arg_var);
                  let adj_arg_e = exp.append(self, &mut |_| LTerm::Lookup(arg_adj.clone()));
                  let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
                  let adj_arg_app_e = exp.append(self, &mut |_| LTerm::Apply(
                      adj_arg_e.loc(),
                      vec![tmp_sink_e.loc()]
                  ));
                  target_e = exp.append(self, &mut |_| LTerm::AConcat(
                      adj_arg_app_e.loc(),
                      target_e.loc()
                  ));
                }
                _ => unimplemented!(),
              }
            }
            let tmp_new_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_new.clone()));
            let linear_e = exp.append(self, &mut |_| LTerm::Lambda(
                vec![tmp_sink.clone()],
                target_e.loc()
            ));
            let new_pair_e = exp.append(self, &mut |_| LTerm::STuple(
                vec![tmp_new_e.loc(), linear_e.loc()]
            ));
            let new_exp = exp.append(self, &mut |_| LTerm::Match(
                adj_app_e.loc(),
                vec![(
                    LPat::STuple(vec![tmp_new.clone().into(), tmp_adj.clone().into()]).into(),
                    new_pair_e.loc()
                )]
            ));
            self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
          }
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body_e = exp.lookup(body);
        match self._force_adj_pair_exp(body_e, tenv, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(_) |
          ResolveAdj::Dual(_, _) => unreachable!(),
          ResolveAdj::Pair(adj_body_e) => {
            let tmp_new = self.fresh_anon_var();
            let tmp_adj = self.lookup_adj_var(&tmp_new);
            let tmp_sink = self.fresh_anon_var();
            let mut fixup_params = Vec::with_capacity(params.len());
            for (idx, param) in params.iter().enumerate() {
              fixup_params.push((idx, param.clone()));
            }
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj.clone()));
            let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
            let adj_body_app_e = exp.append(self, &mut |_| LTerm::Apply(
                tmp_adj_e.loc(),
                vec![tmp_sink_e.loc()]
            ));
            let adj_body_app_fixup_e = exp.append(self, &mut |_| LTerm::ERet(
                // FIXME: restrict free vars (use ctx info).
                vec![],
                fixup_params.clone(),
                adj_body_app_e.loc()
            ));
            let tmp_new_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_new.clone()));
            let linear_e = exp.append(self, &mut |_| LTerm::Lambda(
                vec![tmp_sink.clone()],
                adj_body_app_fixup_e.loc()
            ));
            let new_pair_e = exp.append(self, &mut |_| LTerm::STuple(
                vec![tmp_new_e.loc(), linear_e.loc()]
            ));
            let adj_body_fixup_e = exp.append(self, &mut |_| LTerm::Match(
                adj_body_e.loc(),
                vec![(
                    LPat::STuple(vec![tmp_new.clone().into(), tmp_adj.clone().into()]).into(),
                    new_pair_e.loc()
                )]
            ));
            let adj_lam_e = exp.append(self, &mut |_| LTerm::Lambda(
                params.clone(),
                adj_body_fixup_e.loc()
            ));

            let tmp_new_name = self.fresh_anon_var();
            let tmp_adj_name = self.lookup_adj_var(&tmp_new_name);
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj_name.clone()));
            let mut new_params = Vec::with_capacity(params.len());
            for param in params.iter() {
              match self.lookup_var(param) {
                LVarBinder::Ident(ident) => {
                  new_params.push(self.fresh_ident_var(ident));
                }
                _ => {
                  new_params.push(self.fresh_anon_var());
                }
              }
            }
            let mut new_params_e = Vec::with_capacity(params.len());
            for np in new_params.iter() {
              new_params_e.push(exp.append(self, &mut |_| LTerm::Lookup(np.clone())));
            }
            let adj_app_e = exp.append(self, &mut |_| LTerm::Apply(
                tmp_adj_e.loc(),
                new_params_e.iter().map(|e| e.loc()).collect()
            ));
            let result_pri_name = self.fresh_anon_var();
            let result_adj_name = self.lookup_adj_var(&result_pri_name);
            let result_pri_e = exp.append(self, &mut |_| LTerm::Lookup(result_pri_name.clone()));
            let new_body_e = exp.append(self, &mut |_| LTerm::Match(
                adj_app_e.loc(),
                vec![(
                  LPat::STuple(vec![result_pri_name.clone().into(), result_adj_name.clone().into()]).into(),
                  result_pri_e.loc()
                )]
            ));
            let new_lam_e = exp.append(self, &mut |_| LTerm::Lambda(
                new_params.clone(),
                new_body_e.loc()
            ));
            let tmp_new_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_new_name.clone()));
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj_name.clone()));
            let pair_e = exp.append(self, &mut |_| LTerm::STuple(
                vec![tmp_new_e.loc(), tmp_adj_e.loc()]
            ));
            // FIXME: in the future this binding should have an inlining hint.
            let bind_new_e = exp.append(self, &mut |_| LTerm::Let(
                tmp_new_name.clone(),
                new_lam_e.loc(),
                pair_e.loc()
            ));
            let new_exp = exp.append(self, &mut |_| LTerm::Let(
                tmp_adj_name.clone(),
                adj_lam_e.loc(),
                bind_new_e.loc()
            ));
            self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
          }
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      /*&LTerm::MXBLam(..) => {
        // FIXME
        unimplemented!();
      }*/
      /*&LTerm::MXCLam(..) => {
        // FIXME
        unimplemented!();
      }*/
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        let body_e = exp.lookup(body);
        let rest_e = exp.lookup(rest);
        match self._force_adj_pair_exp(rest_e, tenv, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(_) |
          ResolveAdj::Dual(_, _) => unreachable!(),
          ResolveAdj::Pair(adj_rest_e) => {
            match self._lookup_adj_var(name) {
              None => match self._resolve_adj_exp(body_e, tenv, work) {
                ResolveAdj::Primal(body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      body_e.loc(),
                      adj_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
                }
                ResolveAdj::Bridge(new_body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      new_body_e.loc(),
                      adj_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
                }
                ResolveAdj::Dual(_, _) |
                ResolveAdj::Pair(_) => unreachable!(),
                ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              },
              Some(adj_name) => match self._force_adj_pair_exp(body_e, tenv, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(_) |
                ResolveAdj::Dual(_, _) => unreachable!(),
                ResolveAdj::Pair(adj_body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Match(
                      adj_body_e.loc(),
                      vec![(
                        LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                        adj_rest_e.loc()
                      )]
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
                }
                ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              }
            }
          }
          ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        unimplemented!();
      }
      &LTerm::FlpLit(x) => {
        let tmp_sink = self.fresh_anon_var();
        let nil_env_e = exp.append(self, &mut |_| LTerm::Env(vec![]));
        let adj_e = exp.append(self, &mut |_| LTerm::Lambda(
            vec![tmp_sink.clone()],
            nil_env_e.loc()
        ));
        let new_exp = exp.append(self, &mut |_| LTerm::STuple(
            vec![exp.loc(), adj_e.loc()]
        ));
        self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
      }
      &LTerm::Lookup(ref var) => {
        let adj_var = self.lookup_adj_var(var);
        let adj_e = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
        let new_exp = exp.append(self, &mut |_| LTerm::STuple(
            vec![exp.loc(), adj_e.loc()]
        ));
        self._register_adj(&exp, work, ResolveAdj::Pair(new_exp))
      }
      _ => unimplemented!(),
    }
  }
}

impl LBuilder {
  fn _resolve_post_adj(&mut self, tree: LTreeCell, tenv: &mut TyEnv) -> LTreeCell {
    // TODO
    unimplemented!();
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Tyexp {
  Var(LTyvar),
  Fun(Vec<TyexpRef>, TyexpRef),
  Env(RBTreeMap<usize, LTyvar>, RBTreeMap<LVar, LTyvar>, RBTreeMap<LIdent, LVar>),
  STup(Vec<TyexpRef>),
  Tup,
  Bit,
  Int,
  Flp,
  VFlp,
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
pub enum LTy {
  Fun(Vec<LTyRef>, LTyRef),
  Env(RBTreeMap<usize, LTyRef>, RBTreeMap<LVar, LTyRef>, RBTreeMap<LIdent, LVar>),
  STup(Vec<LTyRef>),
  Tup,
  Bit,
  Int,
  Flp,
  VFlp,
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
  //IsPtlD(TyexpRef, TyexpRef),
  //IsProjIdent(TyexpRef, TyexpRef, LIdent),
  //IsACons(LVar, LTy, LTy, LTy),
  //IsAConcat(LTy, LTy, LTy),
  //IsAApp(Vec<(usize, LVar)>, LTyvar, LTy),
  //IsERet(Vec<(usize, LVar)>, LTyvar, LTy),
  IsACons(TyexpRef, LVar, Option<LIdent>, TyexpRef, TyexpRef),
  IsAConcat(TyexpRef, TyexpRef, TyexpRef),
  IsAApp(TyexpRef, Vec<(usize, LVar)>, TyexpRef),
  IsERet(TyexpRef, Vec<LVar>, Vec<(usize, LVar)>, TyexpRef),
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

#[derive(Default, Debug)]
struct TyWork {
  //tenv:     TyEnv,
  cons:     VecDeque<TyConRef>,
  unsat:    VecDeque<TyConRef>,
  a_defer:  VecDeque<LLabel>,
}

impl TyWork {
  fn _reset(&mut self) {
    self.cons.clear();
    self.unsat.clear();
    self.a_defer.clear();
  }

  fn unsat(&self) -> bool {
    !self.unsat.is_empty()
  }

  fn defer_adj(&self) -> bool {
    !self.a_defer.is_empty()
  }
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
  //tag:  HashMap<LTyvar, Tytag>,
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
    /*match self.tag.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.tag.remove(&lw);
        self.tag.insert(rw.clone(), t);
      }
    }*/
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
      &Tyexp::Env(_, _, _) => {
        query
      }
      &Tyexp::STup(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          elems_.push(self.reduce_texp(elem.clone()));
        }
        Tyexp::STup(elems_).into()
      }
      &Tyexp::Tup |
      &Tyexp::Bit |
      &Tyexp::Int |
      &Tyexp::Flp |
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
      &Tyexp::Flp => Ok(LTy::Flp.into()),
      &Tyexp::Unit => Ok(LTy::Unit.into()),
      _ => Err(()),
    }
  }
}

#[derive(Clone, Default)]
struct IncTyInfMachine {
}

impl IncTyInfMachine {
  fn _gen_pat(&mut self, pat: LPatRef, tenv: &mut TyEnv, work: &mut TyWork) -> TyexpRef {
    // TODO
    unimplemented!();
  }

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
      &LTerm::ImportR(ref _vars, ref _env, ref _body) => {
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }
      &LTerm::Export => {
        // TODO
        let ctx = exp.ctx();
        let idxs: RBTreeMap<usize, LTyvar> = RBTreeMap::default();
        let mut keys: RBTreeMap<LVar, LTyvar> = RBTreeMap::default();
        let mut idents: RBTreeMap<LIdent, LVar> = RBTreeMap::default();
        for (binder, var) in ctx.bind_to_var.iter() {
          keys.insert_mut(var.clone(), tenv.lookup_var(var));
          match binder {
            &LVarBinder::Ident(ref hash) => {
              idents.insert_mut(hash.clone(), var.clone());
            }
            &LVarBinder::Anon => {}
          }
        }
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Env(idxs, keys, idents).into()));
        work.cons.push_front(con);
      }
      &LTerm::Env(ref kvs) => {
        // TODO
        if kvs.is_empty() {
          let idxs = RBTreeMap::default();
          let keys = RBTreeMap::default();
          let idents = RBTreeMap::default();
          let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Env(idxs, keys, idents).into()));
          work.cons.push_front(con);
        } else {
          unimplemented!();
        }
      }
      &LTerm::ACons(ref key, ref ident, ref value, ref target) => {
        // TODO
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        // TODO
      }
      &LTerm::AApp(ref args, ref target) => {
        // TODO
      }
      &LTerm::ERet(ref free, ref params, ref target) => {
        // TODO
      }
      &LTerm::PtlD(ref target) => {
        self._gen_exp(exp.lookup(target), tenv, work);
        work.a_defer.push_front(exp.as_ref().clone());
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
      &LTerm::Match(ref query, ref pat_arms) => {
        self._gen_exp(exp.lookup(query), tenv, work);
        for &(ref pat, ref arm) in pat_arms.iter() {
          // FIXME
          //let pat_ty = self._gen_pat(pat.clone(), tenv, work);
          //let pat_con = TyConRef::new(TyCon::Eq_(tenv.lookup_exp(query).into(), pat_ty));
          let arm_con = TyConRef::new(TyCon::Eq_(ety.clone().into(), tenv.lookup_exp(arm).into()));
          work.cons.push_front(arm_con);
          //work.cons.push_front(pat_con);
        }
      }
      &LTerm::STuple(ref elems) => {
        let mut elem_tys = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          self._gen_exp(exp.lookup(elem), tenv, work);
          elem_tys.push(tenv.lookup_exp(elem).into());
        }
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::STup(elem_tys).into()));
        work.cons.push_front(con);
      }
      &LTerm::BitLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Bit.into()));
        work.cons.push_front(con);
      }
      &LTerm::IntLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Int.into()));
        work.cons.push_front(con);
      }
      &LTerm::FlpLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Flp.into()));
        work.cons.push_front(con);
      }
      &LTerm::Lookup(ref name) => {
        let name_v = tenv.lookup_var(name);
        let con = TyConRef::new(TyCon::Eq_(ety.into(), name_v.into()));
        work.cons.push_front(con);
      }
      &LTerm::ProjectIdent(ref env, ref hash) => {
        let env_con = self._gen_exp(exp.lookup(env), tenv, work);
        work.a_defer.push_front(exp.as_ref().clone());
      }
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _gen_exp: unhandled term: {:?}", t);
      }
    }
  }

  fn gen(&mut self, tree: &LTreeCell, tenv: &mut TyEnv, work: &mut TyWork) {
    work._reset();
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

  fn gen_inc_adj(&mut self, tree: &LTreeCell, a_work: &AdjWork, tenv: &mut TyEnv, work: &mut TyWork) {
    // TODO
    unimplemented!();
  }

  fn _solve_eq_var(&mut self, lv: LTyvar, rv: LTyvar, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
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

  fn _solve_eq_exp(&mut self, v: LTyvar, query: TyexpRef, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
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

  fn solve(&mut self, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    let con = match work.cons.pop_front() {
      None => {
        //self._debug_solve_dump();
        //return Ok(());
        return;
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
          (&Tyexp::Env(ref l_idxs, ref l_keys, ref l_idents), &Tyexp::Env(ref r_idxs, ref r_keys, ref r_idents)) => {
            // TODO
            //unimplemented!();
            self.solve(root, tenv, work)
          }
          (&Tyexp::STup(ref l_elems), &Tyexp::STup(ref r_elems)) => {
            // TODO
            if l_elems.len() != r_elems.len() {
              println!("WARNING: Eq_: stup arity mismatch");
              work.unsat.push_back(con.clone());
            }
            //unimplemented!();
            self.solve(root, tenv, work)
          }
          (&Tyexp::Tup, &Tyexp::Tup) |
          (&Tyexp::Bit, &Tyexp::Bit) |
          (&Tyexp::Int, &Tyexp::Int) |
          (&Tyexp::Flp, &Tyexp::Flp) |
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
      /*&TyCon::IsPtlD(ref e, ref target) => {
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
              &Tyexp::Flp => {
                println!("DEBUG: IsPtlD: differentiating a scalar Fun (... -> Flp)");
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
          &Tyexp::Flp => {
            println!("DEBUG: IsPtlD: differentiating a Flp");
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
      }*/
      /*&TyCon::IsPtlD(ref e, ref tg) => {
        // TODO
        match tenv.mgu(tg.clone()).map(|t| &**t) {
          None => {
            /* FIXME: defer this constraint */
          }
          Some((_, &LTy::Flp)) => {
            // TODO TODO TODO: generate an adj hyp.
            println!("DEBUG: IsPtlD: differentiating a scalar type");
            let adj_ret_v = tenv.fresh_tvar();
            let adj_ty = Tyexp::Fun(vec![Tyexp::Flp.into()], adj_ret_v.into()).into();
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
      /*&TyCon::IsProjIdent(ref ety, ref env_ty, ref hash) => {
        // TODO
        match tenv.mgu_texp(env_ty.clone()).as_ref().map(|t| &**t) {
          None => {
            /* FIXME: defer this constraint */
            self.solve(root, tenv, work)
          }
          Some(&LTy::Env(ref keys, ref idents)) => {
            match idents.get(hash) {
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
      }*/
      &TyCon::IsACons(ref query, ref key, ref ident, ref value, ref target) => {
        // TODO
        unimplemented!();
      }
      &TyCon::IsAConcat(ref query, ref lhs, ref rhs) => {
        // TODO
        unimplemented!();
      }
      &TyCon::IsAApp(ref query, ref args, ref target) => {
        // TODO
        unimplemented!();
      }
      &TyCon::IsERet(ref query, ref free, ref params, ref target) => {
        // TODO
        unimplemented!();
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

impl Default for LCtxRef {
  fn default() -> LCtxRef {
    LCtxRef::empty_top_level()
  }
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

  pub fn lookup_ident(&self, hash: LIdent) -> Option<LVar> {
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
  pub mlabel:   LMLabel,
  pub mpos:     usize,
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

/*#[derive(Default, Debug)]
pub struct LTreeIndex {
  ptld:     BTreeSet<(LLoc, LLoc)>,
  adjd:     BTreeSet<(LLoc, LLoc)>,
  tngd:     BTreeSet<(LLoc, LLoc)>,
  jac:      BTreeSet<(LLoc, LLoc)>,
  adj:      BTreeSet<(LLoc, LLoc)>,
  tng:      BTreeSet<(LLoc, LLoc)>,
}*/

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
  pub fn label(&self) -> LLabel {
    self.label.clone()
  }

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

  pub fn append(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(()/*&mut LBuilder*/) -> LTerm) -> LExprCell {
    let new_label = builder.fresh_label();
    self._append(new_label, builder, mk_term)
  }

  pub fn _append(&self, new_label: LLabel, builder: &mut LBuilder, mk_term: &mut dyn FnMut(()/*&mut LBuilder*/) -> LTerm) -> LExprCell {
    let new_term = (mk_term)(());
    //let new_term = (mk_term)(builder);
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
  pub mterms:   Vec<LMTerm>,
  pub terms:    Vec<LETerm>,
}

#[derive(Clone)]
pub struct LTermRef {
  pub code:     LCodeRef,
  pub pos:      usize,
  //pub label:    LLabel,
  //pub term:     LTerm,
}

impl LTermRef {
  pub fn jump(&self, pos: usize) -> LTermRef {
    // TODO
    unimplemented!();
  }

  pub fn term(&self) -> LETerm {
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

struct PrintBox {
  left_indent:  usize,
  line_nr:      usize,
}

impl Default for PrintBox {
  fn default() -> PrintBox {
    PrintBox{
      left_indent:  0,
      line_nr:      1,
    }
  }
}

impl PrintBox {
  fn _newline<W: IoWrite>(&mut self, writer: &mut W) -> Result<(), IoError> {
    writeln!(writer, "")?;
    for _ in 0 .. self.left_indent {
      write!(writer, " ")?;
    }
    self.line_nr += 1;
    Ok(())
  }

  fn _print_pat<W: IoWrite>(&mut self, builder: &LBuilder, pat: LPatRef, writer: &mut W) -> Result<(), IoError> {
    let mut buffer = Cursor::new(vec![]);
    match &*pat {
      &LPat::STuple(ref elems) => {
        // TODO
        let mut block = false;
        write!(&mut buffer, "(")?;
        for (e_idx, elem) in elems.iter().enumerate() {
          let mut elem_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          elem_box._print_pat(builder, elem.clone(), &mut buffer)?;
          if elem_box.line_nr > 1 {
            // TODO
            block = true;
            unimplemented!();
          } else {
            if e_idx == elems.len() - 1 {
              write!(&mut buffer, ",")?;
            } else {
              write!(&mut buffer, ", ")?;
            }
          }
        }
        if block {
          // TODO
          unimplemented!();
        } else {
          write!(&mut buffer, ")")?;
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      &LPat::Var(ref var) => {
        match builder.lookup_var(var) {
          LVarBinder::Ident(ident) => {
            let ident_s = builder.lookup_ident(&ident);
            write!(&mut buffer, "${}({})", var.0, ident_s)?;
          }
          _ => {
            write!(&mut buffer, "${}", var.0)?;
          }
        }
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      _ => unimplemented!(),
    }
  }

  fn _print_exp<W: IoWrite>(&mut self, builder: &LBuilder, exp: LExprCell, writer: &mut W) -> Result<(), IoError> {
    let mut buffer = Cursor::new(vec![]);
    match &exp.term() {
      &LTerm::Env(ref kvs) => {
        if kvs.is_empty() {
          write!(&mut buffer, "<env>{{}}")?;
          writer.write_all(&buffer.into_inner())?;
          Ok(())
        } else {
          unimplemented!();
        }
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        // TODO
        //write!(&mut buffer, "<A++>(...)")?;
        write!(&mut buffer, "(")?;
        let mut lhs_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        lhs_box._print_exp(builder, exp.lookup(lhs), &mut buffer)?;
        if lhs_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, " <A++> ")?;
        let mut rhs_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        rhs_box._print_exp(builder, exp.lookup(rhs), &mut buffer)?;
        if rhs_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, ")")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::AApp(ref args, ref target) => {
        // TODO
        write!(&mut buffer, "<A-app>(")?;
        for &(ref idx, ref key, ref ident) in args.iter() {
          if ident.is_some() {
            let ident_s = builder.lookup_ident(ident.as_ref().unwrap());
            write!(&mut buffer, "{} => ${}({})", idx, key.0, ident_s)?;
          } else {
            write!(&mut buffer, "{} => ${}", idx, key.0)?;
          }
        }
        write!(&mut buffer, "; ")?;
        let mut target_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        target_box._print_exp(builder, exp.lookup(target), &mut buffer)?;
        if target_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, ")")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::ERet(ref _free, ref params, ref target) => {
        // TODO
        write!(&mut buffer, "<E-ret>(... ")?;
        for &(ref idx, ref key) in params.iter() {
          write!(&mut buffer, "${} => {}", key.0, idx)?;
        }
        write!(&mut buffer, "; ")?;
        let mut target_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        target_box._print_exp(builder, exp.lookup(target), &mut buffer)?;
        if target_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, ")")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::PtlD(ref target) => {
        write!(&mut buffer, "d[")?;
        let mut target_box = PrintBox{
          left_indent:  self.left_indent,
          line_nr:      1,
        };
        target_box._print_exp(builder, exp.lookup(target), &mut buffer)?;
        if target_box.line_nr > 1 {
          unimplemented!();
        } else {
          write!(buffer, "]")?;
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      &LTerm::Apply(ref head, ref args) => {
        // TODO
        let mut head_box = PrintBox{
          left_indent:  self.left_indent,
          line_nr:      1,
        };
        head_box._print_exp(builder, exp.lookup(head), &mut buffer)?;
        if head_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, "[")?;
        for (a_idx, arg) in args.iter().enumerate() {
          let mut arg_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          arg_box._print_exp(builder, exp.lookup(arg), &mut buffer)?;
          if arg_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          if a_idx == args.len() - 1 {
          } else {
            write!(&mut buffer, ", ")?;
          }
        }
        write!(&mut buffer, "]")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::Lambda(ref params, ref body) => {
        write!(&mut buffer, "\\")?;
        for (p_idx, param) in params.iter().enumerate() {
          match builder.lookup_var(param) {
            LVarBinder::Ident(ident) => {
              let ident_s = builder.lookup_ident(&ident);
              write!(&mut buffer, "${}({})", param.0, ident_s)?;
            }
            _ => {
              write!(&mut buffer, "${}", param.0)?;
            }
          }
          if p_idx == params.len() - 1 {
          } else {
            write!(&mut buffer, ", ")?;
          }
        }
        write!(&mut buffer, ". ")?;
        let mut body_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        body_box._print_exp(builder, exp.lookup(body), &mut buffer)?;
        if body_box.line_nr > 1 {
          writer.write_all(&buffer.into_inner())?;
          self.line_nr += body_box.line_nr - 1;
        } else {
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        match builder.lookup_var(name) {
          LVarBinder::Ident(ident) => {
            let ident_s = builder.lookup_ident(&ident);
            write!(&mut buffer, "let ${}({}) = ", name.0, ident_s)?;
          }
          _ => {
            write!(&mut buffer, "let ${} = ", name.0)?;
          }
        }
        let mut body_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        body_box._print_exp(builder, exp.lookup(body), &mut buffer)?;
        if body_box.line_nr > 1 {
          writer.write_all(&buffer.into_inner())?;
          self.line_nr += body_box.line_nr - 1;
          self._newline(writer)?;
          write!(writer, " in")?;
          self._newline(writer)?;
        } else {
          write!(&mut buffer, " in")?;
          writer.write_all(&buffer.into_inner())?;
          self._newline(writer)?;
        }
        self._print_exp(builder, exp.lookup(rest), writer)
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        if pat_arms.len() == 1 {
          let (pat, arm) = pat_arms.iter().next().unwrap().clone();
          write!(&mut buffer, "let ")?;
          let mut pat_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          pat_box._print_pat(builder, pat, &mut buffer)?;
          if pat_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          write!(&mut buffer, " = ")?;
          let mut query_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          query_box._print_exp(builder, exp.lookup(query), &mut buffer)?;
          if query_box.line_nr > 1 {
            writer.write_all(&buffer.into_inner())?;
            self.line_nr += query_box.line_nr - 1;
            self._newline(writer)?;
            write!(writer, " in")?;
            self._newline(writer)?;
          } else {
            write!(&mut buffer, " in")?;
            writer.write_all(&buffer.into_inner())?;
            self._newline(writer)?;
          }
          self._print_exp(builder, exp.lookup(&arm), writer)
        } else {
          unimplemented!();
        }
      }
      &LTerm::STuple(ref elems) => {
        // TODO
        let mut block = false;
        write!(&mut buffer, "(")?;
        for (e_idx, elem) in elems.iter().enumerate() {
          let mut elem_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          elem_box._print_exp(builder, exp.lookup(elem), &mut buffer)?;
          if elem_box.line_nr > 1 {
            block = true;
            unimplemented!();
          } else {
            if e_idx == elems.len() - 1 {
              write!(&mut buffer, ",")?;
            } else {
              write!(&mut buffer, ", ")?;
            }
          }
        }
        if block {
          unimplemented!();
        } else {
          write!(&mut buffer, ")")?;
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      &LTerm::IntLit(x) => {
        write!(&mut buffer, "{:?}n", x)?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::FlpLit(x) => {
        write!(&mut buffer, "{:?}f", x)?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::Lookup(ref var) => {
        match builder.lookup_var(var) {
          LVarBinder::Ident(ident) => {
            let ident_s = builder.lookup_ident(&ident);
            write!(&mut buffer, "${}({})", var.0, ident_s)?;
          }
          _ => {
            write!(&mut buffer, "${}", var.0)?;
          }
        }
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::ProjectIdent(ref target, ref ident) => {
        let ident_s = builder.lookup_ident(&ident);
        let mut target_box = PrintBox{
          left_indent:  self.left_indent,
          line_nr:      1,
        };
        target_box._print_exp(builder, exp.lookup(target), &mut buffer)?;
        if target_box.line_nr > 1 {
          unimplemented!();
        } else {
          write!(buffer, ".{}", ident_s)?;
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      _ => {
        // TODO
        write!(&mut buffer, "...")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
    }
  }

  fn print<W: IoWrite>(&mut self, builder: &LBuilder, tree: LTreeCell, writer: &mut W) -> Result<(), IoError> {
    self._print_exp(builder, tree.root(), writer)?;
    self._newline(writer)
  }
}
