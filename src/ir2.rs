// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::builtins::top2::{_include_top_level_exp};
//use crate::coll::{HTrieMap, HTrieSet};
//use crate::coll::{RBTreeMap, RBTreeSet, DebugRBTreeMap, DebugRBTreeSet};
use crate::coll::{HTreapMap};
//use crate::coll::{HTreapSet};
use crate::coll::{IHTreapMap};
use crate::coll::{IHTreapSet};
use crate::lang::{HExpr};
use crate::mach::{MAddr, MLamTerm, /*MUnsafeCTerm*/};

use std::borrow::{Borrow};
use std::cell::{RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{Write as IoWrite, Cursor, Error as IoError, stdout};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LLabel(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LMLabel(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LIdent(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LVar(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LTyvar(u64);

#[derive(Clone, Debug)]
pub enum LPat {
  Cons(LPatRef, LPatRef),
  Concat(LPatRef, LPatRef),
  STuple(Vec<LPatRef>),
  HTuple(Vec<LPatRef>),
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
      &LPat::HTuple(ref elems) => {
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

  pub fn vars_set(&self) -> (Vec<LVar>, HashSet<LVar>) {
    let mut vars_buf = Vec::new();
    let mut vars_set = HashSet::new();
    self._vars(&mut vars_set, &mut vars_buf);
    (vars_buf, vars_set)
  }
}

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

impl<'a> Borrow<LLabel> for &'a LLoc {
  fn borrow(&self) -> &LLabel {
    &self.label
  }
}

impl Borrow<LLabel> for LLoc {
  fn borrow(&self) -> &LLabel {
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
pub enum LEnvMask {
  Empty,
  Var(LVar),
  //List(/*Vec<usize>,*/ Vec<LVar>),
  //Set(HTrieSet<LVar>),
  Set(IHTreapSet<LVar>),
  All,
}

#[derive(Clone, Debug)]
pub enum LTerm<E=LLoc, ME=LMLoc> {
  Top,
  Break(E),
  Return(E),
  Module(Vec<E>, E),
  TodoRequire,
  Export,
  Import(LEnvMask, E, E),
  EApply(Vec<(usize, LVar)>, E, E),
  EnvIdxs(Vec<(usize, E)>),
  EnvVars(Vec<(LVar, E)>),
  EnvIdxsLazy(Vec<(usize, E)>),
  EnvVarsLazy(Vec<(LVar, E)>),
  EImportVar(LVar, E, E),
  EImportVars(IHTreapSet<LVar>, E, E),
  EConsIdxLazy(usize, E, E),
  EConsVarLazy(LVar, E, E),
  EPopConsIdxLazy(usize, LVar, E, E),
  EPopIdx(usize, LVar, E),
  EPopVars(Vec<(LVar, usize)>, E),
  ESymmVars(E, E),
  AApply(E, Vec<(usize, LVar, LVarBinder, LVar)>),
  AReturn(/*LEnvMask,*/ Vec<(usize, LVar)>, E),
  ACons(/*LEnvMask,*/ LVar, LVarBinder, E, E),
  AConcat(E, E),
  PtlD(E),
  AdjD(E),
  TngD(E),
  Jac(E),
  //Adj(E),
  //Tng(E),
  Apply(E, Vec<E>),
  Lambda(Vec<LVar>, E),
  FixLambda(LVar, Vec<LVar>, E),
  Let(LVar, E, E),
  Fix(LVar, E),
  SFix(Vec<LVar>, E),
  //Alt(LVar, LVar, E, E),
  Match(E, Vec<(LPatRef, E)>),
  Mismatch(E, Vec<(LPatRef, E)>),
  Cons(E, E),
  Concat(E, E),
  STuple(Vec<E>),
  Tuple(Vec<E>),
  BitLit(bool),
  IntLit(i64),
  FlpLit(f64),
  UnitLit,
  Index(usize),
  Lookup(LVar),
  LookupIdent(LIdent),
  ProjectVar(E, LVar),
  ProjectIdent(E, LIdent),
  //ProjectIdents(E, Vec<LIdent>),
  Unbind(LVar, E),
  MX(ME),
  Bot,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  // TODO
  pub version:  usize,
  //pub up:       LLoc,
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Clone, Debug)]
pub struct LMLoc {
  pub label:    LMLabel,
  pub pos:      usize,
}

impl<'a> Borrow<LMLabel> for &'a LMLoc {
  fn borrow(&self) -> &LMLabel {
    &self.label
  }
}

impl Borrow<LMLabel> for LMLoc {
  fn borrow(&self) -> &LMLabel {
    &self.label
  }
}

pub type LMLambdaDef = LXLambdaDef<MLamTerm>;
//pub type LMUnsafeCLambdaDef = LXLambdaDef<MUnsafeCLamTerm>;

#[derive(Clone)]
pub struct LXLambdaDef<Term> {
  pub ar:   usize,
  pub mk:   Rc<dyn Fn(/*&mut LBuilder,*/ /*LCtxRef*/) -> Term>,
  pub ty:   Option<Rc<dyn Fn(&mut LBuilder, /*LCtxRef*/) -> (Vec<LTy>, LTy)>>,
  pub adj:  Option<Rc<dyn Fn(&LXLambdaDef<Term>, LExprCell, LCtxRef, &mut LBuilder, /*Vec<LVar>, LVar*/) -> LTerm>>,
}

#[derive(Clone)]
pub enum LMTerm/*<E=LMLoc>*/ {
  Deref(MAddr),
  Lambda(LMLambdaDef, MLamTerm),
  //UnsafeCLambda(LMUnsafeCLambdaDef, MUnsafeCLamTerm),
}

#[derive(Clone)]
pub struct LMExpr {
  pub version:  usize,
  pub label:    LMLabel,
  pub term:     LMTerm,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LVarBinder {
  Ident(LIdent),
  Anon,
}

impl From<LIdent> for LVarBinder {
  fn from(ident: LIdent) -> LVarBinder {
    LVarBinder::Ident(ident)
  }
}

#[derive(Clone, Debug)]
enum RegisterAdj {
  Primal,
  Bridge(LLabel, bool),
  Dual(LLabel),
  Pair(LLabel, bool),
}

#[derive(Clone, Default)]
pub struct LBuilder {
  label_ctr:    u64,
  mlabel_ctr:   u64,
  ident_ctr:    u64,
  var_ctr:      u64,
  tyvar_ctr:    u64,
  name_to_id:   HTreapMap<String, LIdent>,
  id_to_name:   HTreapMap<LIdent, String>,
  var_to_bind:  IHTreapMap<LVar, LVarBinder>,
  adj_var:      IHTreapMap<LVar, LVar>,
  //reg_adj:      IHTreapMap<LLabel, RegisterAdj>,
}

impl LBuilder {
  pub fn fresh_label(&mut self) -> LLabel {
    self.label_ctr += 1;
    assert!(self.label_ctr != 0);
    LLabel(self.label_ctr)
  }

  pub fn fresh_mlabel(&mut self) -> LMLabel {
    self.mlabel_ctr += 1;
    assert!(self.mlabel_ctr != 0);
    LMLabel(self.mlabel_ctr)
  }

  pub fn lookup_name<S: ?Sized + Borrow<str>>(&mut self, name: &S) -> LIdent {
    let name = name.borrow();
    match self.name_to_id.get(name) {
      None => panic!(),
      Some(id) => id.clone(),
    }
  }

  pub fn lookup_or_fresh_name<S: ?Sized + Borrow<str>>(&mut self, name: &S) -> LIdent {
    let name = name.borrow();
    match self.name_to_id.get(name) {
      None => {
        self.ident_ctr += 1;
        assert!(self.ident_ctr != 0);
        let new_ident = LIdent(self.ident_ctr);
        self.name_to_id.insert_mut(name.to_owned(), new_ident.clone());
        self.id_to_name.insert_mut(new_ident.clone(), name.to_owned());
        new_ident
      }
      Some(id) => id.clone(),
    }
  }

  pub fn lookup_ident(&self, ident: &LIdent) -> String {
    match self.id_to_name.get(ident) {
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

  /*pub fn fresh_tvar(&mut self) -> LTyvar {
    self.tyvar_ctr += 1;
    assert!(self.tyvar_ctr != 0);
    LTyvar(self.tyvar_ctr)
  }*/

  pub fn _lookup_var(&self, var: &LVar) -> Option<LVarBinder> {
    match self.var_to_bind.get(var) {
      None => None,
      Some(binder) => Some(binder.clone()),
    }
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

  pub fn lookup_or_fresh_adj_var(&mut self, var: &LVar) -> LVar {
    match self.adj_var.get(var) {
      None => {
        let adj = self.fresh_anon_var();
        self.adj_var.insert_mut(var.clone(), adj.clone());
        adj
      }
      Some(adj) => adj.clone(),
    }
  }

  pub fn compile(&mut self, htree: Rc<HExpr>) -> Result<LModule, ()> {
    // TODO
    unimplemented!();
  }

  pub fn _include_top_level(&mut self, tree: LTreeCell) -> LTreeCell {
    let new_root = _include_top_level_exp(tree.root(), self);
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }

  pub fn _compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef, top_tctx: LTyctxRef) -> Result<LModule, ()> {
    // TODO
    // FIXME: derive env from base ctx.
    // FIXME: derive tenv from base tctx.
    let mut env = Env::default();
    let mut tenv = TyEnv::default();
    let tree = LTreeCell::empty(self);
    let tree = self._lower2(tree, top_ctx.clone(), htree, &mut env);
    let tree = self._include_top_level(tree);
    println!("DEBUG: _compile: original, printing tree...");
    self._print(tree.clone());
    self._ctx(tree.clone(), top_ctx.clone(), &mut env, &mut tenv);
    let tree = self._resolve_ctx(tree, &mut env);
    let tree = self._normalize(tree);
    self._ctx(tree.clone(), top_ctx.clone(), &mut env, &mut tenv);
    println!("DEBUG: _compile: normalized, printing tree...");
    self._print(tree.clone());
    let mut t_work = TyWork::default();
    self.gen(&tree, &mut tenv, &mut t_work);
    self.solve(tree.root(), &mut tenv, &mut t_work);
    if t_work.unsat() {
      return Err(());
    }
    //self._print_tys(&mut tenv);
    let mut tree = tree;
    if t_work.defer_adj() {
      let mut term = false;
      loop {
        match self._resolve_adj(tree.clone(), &mut env, &mut tenv, &mut t_work) {
          ResolveAdjResult::Primal(_) => unreachable!(),
          ResolveAdjResult::Bridge(new_tree, incomplete) => {
            if incomplete {
              println!("DEBUG: _compile: resolved adj to incomplete bridge, printing tree...");
            } else {
              println!("DEBUG: _compile: resolved adj to bridge, printing tree...");
            }
            self._print(new_tree.clone());
            self.gen(&new_tree, &mut tenv, &mut t_work);
            self.solve(new_tree.root(), &mut tenv, &mut t_work);
            //self._print_tys(&mut tenv);
            tree = new_tree;
            if !incomplete {
              term = true;
              //tree = new_tree;
              break;
            }
          }
          ResolveAdjResult::Error(_, a_work) => {
            // TODO: error reporting.
            println!("DEBUG: _compile: adj resolution error: {:?}", a_work.errored);
            return Err(());
          }
        }
      }
      assert!(term);
      self._ctx(tree.clone(), top_ctx.clone(), &mut env, &mut tenv);
      tree = self._resolve_post_adj(tree, &mut env, &mut tenv);
    }
    if t_work.unsat() {
      return Err(());
    }
    self._print(tree.clone());
    let end_ctx = None;
    let end_tctx = None;
    /*let tree = self._ctx(tree, top_ctx.clone());
    let end_ctx = tree.root_ctx();
    let end_tctx = match end_ctx {
      None => None,
      Some(ref ctx) => tree.final_tctx(ctx, &mut tenv),
    };*/
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

  fn _print_tys(&self, tenv: &mut TyEnv) {
    // TODO
    /*for (var, _) in tenv.var.clone().iter() {
      match tenv.mgu_var(var.clone()) {
        None => {
          println!("# ${} : ?", var.0);
        }
        Some((_, _, ty)) => {
          println!("# ${} : {:?}", var.0, &*ty);
        }
      }
    }*/
  }
}

struct LowerWork {
  errors:   VecDeque<()>,
}

impl LBuilder {
  fn _lower_ty_rec(&mut self, htree: Rc<HExpr>) -> Result<LTyRef, ()> {
    // TODO
    unimplemented!();
  }

  fn _lower_pat_rec(&mut self, hexp: Rc<HExpr>, ctx: &mut LCtxRef) -> Result<LPatRef, ()> {
    // TODO
    match &*hexp {
      &HExpr::STuple(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          let elem_ = self._lower_pat_rec(elem.clone(), ctx)?;
          elems_.push(elem_);
        }
        Ok(LPat::STuple(elems_).into())
      }
      &HExpr::Tuple(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          let elem_ = self._lower_pat_rec(elem.clone(), ctx)?;
          elems_.push(elem_);
        }
        Ok(LPat::HTuple(elems_).into())
      }
      &HExpr::TeeLit => {
        Ok(LPat::BitLit(true).into())
      }
      &HExpr::BotLit => {
        Ok(LPat::BitLit(false).into())
      }
      &HExpr::IntLit(x) => {
        Ok(LPat::IntLit(x).into())
      }
      &HExpr::PlacePat => {
        let place = self.fresh_anon_var();
        /*ctx.bind_anon_mut(place.clone());*/
        Ok(LPat::Var(place).into())
      }
      &HExpr::Ident(ref name) => {
        let ident = self.lookup_or_fresh_name(name);
        let var = self.fresh_ident_var(ident.clone());
        ctx.bind_ident_mut(ident, var.clone());
        Ok(LPat::Var(var).into())
      }
      _ => Err(())
    }
  }

  fn _lower2_unop(&mut self, root: LExprCell, ctx: LCtxRef, op_name: &str, arg: Rc<HExpr>, env: &mut Env) -> LExprCell {
    let op_ident = self.lookup_or_fresh_name(op_name);
    let op_var = match ctx._lookup_ident(op_ident) {
      Some(v) => v,
      None => {
        // TODO: propagate errors.
        println!("error: unknown var '{}'", op_name);
        self.fresh_anon_var()
      }
    };
    let op = root.append(self, &mut |_| LTerm::Lookup(op_var.clone()));
    let arg = self._lower2_exp(root.clone(), ctx.clone(), arg, env);
    root.append(self, &mut |_| LTerm::Apply(
        op.loc(),
        vec![arg.loc()]
    ))
  }

  fn _lower2_binop(&mut self, root: LExprCell, ctx: LCtxRef, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, env: &mut Env) -> LExprCell {
    let op_ident = self.lookup_or_fresh_name(op_name);
    let op_var = match ctx._lookup_ident(op_ident) {
      Some(v) => v,
      None => {
        // TODO: propagate errors.
        println!("error: unknown var '{}'", op_name);
        self.fresh_anon_var()
      }
    };
    let op = root.append(self, &mut |_| LTerm::Lookup(op_var.clone()));
    let lhs = self._lower2_exp(root.clone(), ctx.clone(), lhs, env);
    let rhs = self._lower2_exp(root.clone(), ctx.clone(), rhs, env);
    root.append(self, &mut |_| LTerm::Apply(
        op.loc(),
        vec![lhs.loc(), rhs.loc()]
    ))
  }

  fn _lower2_exp(&mut self, root: LExprCell, ctx: LCtxRef, hexp: Rc<HExpr>, env: &mut Env) -> LExprCell {
    // TODO: ctx.
    let new_exp = match &*hexp {
      &HExpr::End => {
        root.append(self, &mut |_| LTerm::Top)
      }
      &HExpr::PartialD(ref target) => {
        let target = self._lower2_exp(root.clone(), ctx.clone(), target.clone(), env);
        root.append(self, &mut |_| LTerm::PtlD(target.loc()))
      }
      &HExpr::Apply(ref head, ref args) => {
        let head = self._lower2_exp(root.clone(), ctx.clone(), head.clone(), env);
        let mut args_: Vec<_> = Vec::with_capacity(args.len());
        for arg in args.iter() {
          let arg = self._lower2_exp(root.clone(), ctx.clone(), arg.clone(), env);
          args_.push(arg.loc());
        }
        root.append(self, &mut |_| LTerm::Apply(
            head.loc(),
            args_.clone()
        ))
      }
      &HExpr::Lambda(ref params, ref body) => {
        let mut param_vars = Vec::with_capacity(params.len());
        let mut body_ctx = ctx.clone();
        for p in params.iter() {
          let p_name = match &**p {
            &HExpr::Ident(ref p_name) => p_name,
            _ => panic!(),
          };
          let p_ident = self.lookup_or_fresh_name(p_name);
          let p_var = self.fresh_ident_var(p_ident.clone());
          body_ctx.bind_ident_mut(p_ident, p_var.clone());
          param_vars.push(p_var);
        }
        let body = self._lower2_exp(root.clone(), body_ctx, body.clone(), env);
        root.append(self, &mut |_| LTerm::Lambda(
            param_vars.clone(),
            body.loc()
        ))
      }
      &HExpr::Let(ref decos, ref lhs, ref body, ref rest) => {
        // TODO: decorators.
        let body_ctx = ctx.clone();
        let mut rest_ctx = ctx.clone();
        let decos = decos.clone().unwrap_or_default();
        match &**lhs {
          &HExpr::Ident(ref name) => {
            let name_ident = self.lookup_or_fresh_name(name);
            let name_var = self.fresh_ident_var(name_ident.clone());
            rest_ctx.bind_ident_mut(name_ident, name_var.clone());
            let body = self._lower2_exp(root.clone(), body_ctx, body.clone(), env);
            let rest = self._lower2_exp(root.clone(), rest_ctx, rest.clone(), env);
            root.append(self, &mut |_| LTerm::Let(
                name_var.clone(),
                body.loc(),
                rest.loc()
            ))
          }
          &HExpr::Apply(ref name, ref params) => {
            // TODO
            unimplemented!();
          }
          _ => {
            let pat = match self._lower_pat_rec(lhs.clone(), &mut rest_ctx) {
              Err(_) => panic!(),
              Ok(pat) => pat,
            };
            let body = self._lower2_exp(root.clone(), body_ctx, body.clone(), env);
            let rest = self._lower2_exp(root.clone(), rest_ctx, rest.clone(), env);
            root.append(self, &mut |_| LTerm::Match(
                body.loc(),
                vec![(pat.clone(), rest.loc())]
            ))
          }
        }
      }
      &HExpr::Match(ref query, ref pat_arms) => {
        let query = self._lower2_exp(root.clone(), ctx.clone(), query.clone(), env);
        let mut pat_arms_ = Vec::with_capacity(pat_arms.len());
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut pat_arm_ctx = ctx.clone();
          let pat = match self._lower_pat_rec(pat.clone(), &mut pat_arm_ctx) {
            Err(_) => panic!(),
            Ok(pat) => pat,
          };
          let arm = self._lower2_exp(root.clone(), pat_arm_ctx, arm.clone(), env);
          pat_arms_.push((pat, arm.loc()));
        }
        root.append(self, &mut |_| LTerm::Match(
            query.loc(),
            pat_arms_.clone()
        ))
      }
      &HExpr::TeeLit => {
        root.append(self, &mut |_| LTerm::BitLit(true))
      }
      &HExpr::BotLit => {
        root.append(self, &mut |_| LTerm::BitLit(false))
      }
      &HExpr::IntLit(x) => {
        root.append(self, &mut |_| LTerm::IntLit(x))
      }
      &HExpr::FlpLit(x) => {
        root.append(self, &mut |_| LTerm::FlpLit(x))
      }
      &HExpr::Ident(ref name) => {
        let name_ident = self.lookup_or_fresh_name(name);
        /*let name_var = match ctx._lookup_ident(name_ident) {
          Some(v) => v,
          None => {
            // FIXME: propagate errors.
            println!("error: unknown var '{}'", name);
            self.fresh_anon_var()
          }
        };
        root.append(self, &mut |_| LTerm::Lookup(name_var.clone()))*/
        root.append(self, &mut |_| LTerm::LookupIdent(name_ident.clone()))
      }
      &HExpr::PathIndex(..) => {
        // TODO
        unimplemented!();
      }
      &HExpr::PathLookup(ref lhs, ref rhs_name) => {
        let name_ident = self.lookup_or_fresh_name(rhs_name);
        let lhs = self._lower2_exp(root.clone(), ctx.clone(), lhs.clone(), env);
        root.append(self, &mut |_| LTerm::ProjectIdent(
            lhs.loc(),
            name_ident.clone()
        ))
      }
      &HExpr::PathELookup(..) => {
        // TODO
        unimplemented!();
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        self._lower2_binop(root, ctx.clone(), "add", lhs.clone(), rhs.clone(), env)
      }
      &HExpr::Mul(ref lhs, ref rhs) => {
        self._lower2_binop(root, ctx.clone(), "mul", lhs.clone(), rhs.clone(), env)
      }
      &HExpr::Neg(ref arg) => {
        self._lower2_unop(root, ctx.clone(), "neg", arg.clone(), env)
      }
      &HExpr::Sub(ref lhs, ref rhs) => {
        self._lower2_binop(root, ctx.clone(), "sub", lhs.clone(), rhs.clone(), env)
      }
      &HExpr::Div(ref lhs, ref rhs) => {
        self._lower2_binop(root, ctx.clone(), "div", lhs.clone(), rhs.clone(), env)
      }
      &HExpr::Eq(ref lhs, ref rhs) => {
        self._lower2_binop(root, ctx.clone(), "eq", lhs.clone(), rhs.clone(), env)
      }
      _ => unimplemented!(),
    };
    env.unsafe_set_ctx(&new_exp, ctx);
    new_exp
  }

  fn _lower2(&mut self, tree: LTreeCell, ctx: LCtxRef, htree: Rc<HExpr>, env: &mut Env) -> LTreeCell {
    let new_root = self._lower2_exp(tree.root(), ctx, htree, env);
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }
}

impl LBuilder {
  fn _normalize_kont(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    match &exp.term() {
      // TODO: cases.
      &LTerm::Top => {
        kont(self, exp)
      }
      &LTerm::Break(ref inner) => {
        let inner = self._normalize_term(exp.lookup(inner));
        let new_exp = exp.append(self, &mut |_| LTerm::Break(inner.loc()));
        kont(self, new_exp)
      }
      &LTerm::Return(ref inner) => {
        let inner = exp.lookup(inner);
        self._normalize_name(inner, &mut |this, inner| {
          let new_exp = exp.append(this, &mut |_| LTerm::Return(inner.loc()));
          kont(this, new_exp)
        })
      }
      &LTerm::Apply(ref head, ref args) => {
        let head = exp.lookup(head);
        self._normalize_name(head, &mut |this, head| {
          let mut pre_args = VecDeque::from_iter(args.iter().map(|a| exp.lookup(a)));
          let mut post_args = Vec::new();
          this._normalize_names(&mut pre_args, &mut post_args, &mut |this, args| {
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
      &LTerm::Export => kont(self, exp),
      &LTerm::Import(ref free, ref env, ref body) => {
        let env = exp.lookup(env);
        let body = exp.lookup(body);
        self._normalize_name(env, &mut |this, env| {
          let body = this._normalize_term(body.clone());
          let new_exp = exp.append(this, &mut |_| LTerm::Import(
              free.clone(),
              env.loc(),
              body.loc(),
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::EConsIdxLazy(idx, ref value, ref target) => {
        let target = exp.lookup(target);
        self._normalize_name(target, &mut |this, target| {
          let value = exp.lookup(value);
          let value = this._normalize_term(value);
          let new_exp = exp.append(this, &mut |_| LTerm::EConsIdxLazy(
              idx,
              value.loc(),
              target.loc()
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::EConsVarLazy(ref var, ref value, ref target) => {
        let target = exp.lookup(target);
        self._normalize_name(target, &mut |this, target| {
          let value = exp.lookup(value);
          let value = this._normalize_term(value);
          let new_exp = exp.append(this, &mut |_| LTerm::EConsVarLazy(
              var.clone(),
              value.loc(),
              target.loc()
          ));
          kont(this, new_exp)
        })
      }
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
      &LTerm::SFix(ref fixnames, ref fixbody) => {
        // TODO
        unimplemented!();
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
      &LTerm::Match(ref query, ref pat_arms) => {
        let query = exp.lookup(query);
        self._normalize_name(query, &mut |this, query| {
          let mut new_pat_arms = Vec::with_capacity(pat_arms.len());
          for &(ref pat, ref arm) in pat_arms.iter() {
            let arm = this._normalize_term(exp.lookup(arm));
            new_pat_arms.push((pat.clone(), arm.loc()));
          }
          let new_exp = exp.append(this, &mut |_| LTerm::Match(
              query.loc(),
              new_pat_arms.clone()
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        let query = exp.lookup(query);
        self._normalize_name(query, &mut |this, query| {
          let mut new_pat_arms = Vec::with_capacity(pat_arms.len());
          for &(ref pat, ref arm) in pat_arms.iter() {
            let arm = this._normalize_term(exp.lookup(arm));
            new_pat_arms.push((pat.clone(), arm.loc()));
          }
          let new_exp = exp.append(this, &mut |_| LTerm::Mismatch(
              query.loc(),
              new_pat_arms.clone()
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::STuple(_) => {
        // TODO
        unimplemented!();
      }
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) |
      &LTerm::Lookup(_) => {
        kont(self, exp)
      }
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
      &LTerm::MX(_) => {
        kont(self, exp)
      }
      _ => {
        unimplemented!();
      }
    }
  }

  fn _normalize_term(&mut self, exp: LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |_, exp| exp)
  }

  fn _normalize_names(&mut self, pre_exps: &mut VecDeque<LExprCell>, post_exps: &mut Vec<LExprCell>, kont: &mut dyn FnMut(&mut Self, &mut Vec<LExprCell>) -> LExprCell) -> LExprCell {
    match pre_exps.pop_front() {
      Some(exp) => {
        self._normalize_name(exp, &mut |this, exp| {
          post_exps.push(exp);
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

  fn _normalize(&mut self, tree: LTreeCell) -> LTreeCell {
    let new_root = self._normalize_term(tree.root());
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }
}

impl LBuilder {
  fn _ctx_exp(&mut self, exp: LExprCell, ctx: LCtxRef, env: &mut Env, tenv: &mut TyEnv) {
    env.unsafe_set_ctx(&exp, ctx.clone());
    match &exp.term() {
      &LTerm::Top => {}
      &LTerm::Break(ref inner) => {
        self._ctx_exp(exp.lookup(inner), ctx, env, tenv);
      }
      &LTerm::Return(ref inner) => {
        self._ctx_exp(exp.lookup(inner), ctx, env, tenv);
      }
      /*&LTerm::Export => {}
      &LTerm::Import(ref free, ref target, ref body) => {
        let target = exp.lookup(target);
        let body = exp.lookup(body);
        self._ctx_exp(target, ctx, env, tenv);
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }*/
      &LTerm::EnvIdxs(_) => {
        // TODO
      }
      &LTerm::EnvVars(_) => {
        // TODO
      }
      &LTerm::EImportVar(ref var, ref target, ref rest) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Env(_, ref var_keys, ref var_ctx) => {
              assert!(var_keys.contains_key(var));
              let mut rest_ctx = LCtxRef::empty();
              match self._lookup_var(var) {
                Some(LVarBinder::Ident(id)) => match var_ctx._lookup_ident(&id) {
                  Some(ref id_var) => if var == id_var {
                    rest_ctx.bind_ident_mut(id, var.clone());
                  },
                  None => {}
                },
                Some(_) | None => unreachable!(),
              }
              self._ctx_exp(exp.lookup(rest), rest_ctx, env, tenv);
            }
            _ => unreachable!(),
          }
        } else {
          unreachable!();
        }
      }
      &LTerm::EImportVars(ref vars, ref target, ref rest) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Env(_, ref var_keys, ref var_ctx) => {
              let rest_var_keys = var_keys.set_intersection(vars);
              assert_eq!(rest_var_keys.len(), vars.len());
              let mut rest_ctx = LCtxRef::empty();
              for var in vars.iter() {
                match self._lookup_var(var) {
                  Some(LVarBinder::Ident(id)) => match var_ctx._lookup_ident(&id) {
                    Some(ref id_var) => if var == id_var {
                      rest_ctx.bind_ident_mut(id, var.clone());
                    },
                    None => {}
                  },
                  Some(_) | None => unreachable!(),
                }
              }
              self._ctx_exp(exp.lookup(rest), rest_ctx, env, tenv);
            }
            _ => unreachable!(),
          }
        } else {
          unreachable!();
        }
      }
      &LTerm::AApply(ref target, ..) => {
        // TODO
        self._ctx_exp(exp.lookup(target), ctx.clone(), env, tenv);
      }
      &LTerm::AReturn(.., ref target) => {
        // TODO
        self._ctx_exp(exp.lookup(target), ctx.clone(), env, tenv);
      }
      &LTerm::ACons(.., ref value, ref target) => {
        // TODO
        self._ctx_exp(exp.lookup(value), ctx.clone(), env, tenv);
        self._ctx_exp(exp.lookup(target), ctx.clone(), env, tenv);
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        // TODO
        self._ctx_exp(exp.lookup(lhs), ctx.clone(), env, tenv);
        self._ctx_exp(exp.lookup(rhs), ctx.clone(), env, tenv);
      }
      &LTerm::PtlD(ref target) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
      }
      &LTerm::AdjD(ref target) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
      }
      &LTerm::TngD(ref target) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
      }
      &LTerm::Apply(ref head, ref args) => {
        self._ctx_exp(exp.lookup(head), ctx.clone(), env, tenv);
        for arg in args.iter() {
          self._ctx_exp(exp.lookup(arg), ctx.clone(), env, tenv);
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut body_ctx = ctx.clone();
        for p in params.iter() {
          match self.lookup_var(p) {
            LVarBinder::Ident(id) => {
              body_ctx.bind_ident_mut(id, p.clone());
            }
            _ => {}
          }
        }
        self._ctx_exp(exp.lookup(body), body_ctx, env, tenv);
      }
      &LTerm::Let(ref var, ref body, ref rest) => {
        let mut rest_ctx = ctx.clone();
        match self.lookup_var(var) {
          LVarBinder::Ident(id) => {
            rest_ctx.bind_ident_mut(id, var.clone());
          }
          _ => {}
        }
        self._ctx_exp(exp.lookup(body), ctx, env, tenv);
        self._ctx_exp(exp.lookup(rest), rest_ctx, env, tenv);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let mut fixctx = ctx.clone();
        match self.lookup_var(fixname) {
          LVarBinder::Ident(id) => {
            fixctx.bind_ident_mut(id, fixname.clone());
          }
          _ => {}
        }
        self._ctx_exp(exp.lookup(fixbody), fixctx, env, tenv);
      }
      &LTerm::SFix(ref fixnames, ref fixbody) => {
        let mut fixctx = ctx.clone();
        for fixname in fixnames.iter() {
          match self.lookup_var(fixname) {
            LVarBinder::Ident(id) => {
              fixctx.bind_ident_mut(id, fixname.clone());
            }
            _ => {}
          }
        }
        self._ctx_exp(exp.lookup(fixbody), fixctx, env, tenv);
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        self._ctx_exp(exp.lookup(query), ctx.clone(), env, tenv);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut arm_ctx = ctx.clone();
          for pv in pat.vars().iter() {
            match self.lookup_var(pv) {
              LVarBinder::Ident(id) => {
                arm_ctx.bind_ident_mut(id, pv.clone());
              }
              _ => {}
            }
          }
          self._ctx_exp(exp.lookup(arm), arm_ctx, env, tenv);
        }
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        self._ctx_exp(exp.lookup(query), ctx.clone(), env, tenv);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut arm_ctx = ctx.clone();
          for pv in pat.vars().iter() {
            match self.lookup_var(pv) {
              LVarBinder::Ident(id) => {
                arm_ctx.bind_ident_mut(id, pv.clone());
              }
              _ => {}
            }
          }
          self._ctx_exp(exp.lookup(arm), arm_ctx, env, tenv);
        }
      }
      /*&LTerm::Alt(ref name, ref alt_name, ref body, ref rest) => {
        let mut rest_ctx = ctx.clone();
        rest_ctx.bind_ident_mut(self.lookup_var(alt_name), alt_name.clone());
        self._ctx_exp(exp.lookup(body), ctx, env, tenv);
        self._ctx_exp(exp.lookup(rest), rest_ctx, env, tenv);
      }*/
      &LTerm::STuple(ref elems) => {
        for elem in elems.iter() {
          self._ctx_exp(exp.lookup(elem), ctx.clone(), env, tenv);
        }
      }
      &LTerm::BitLit(_) => {}
      &LTerm::IntLit(_) => {}
      &LTerm::FlpLit(_) => {}
      &LTerm::Lookup(_) => {}
      &LTerm::LookupIdent(_) => {}
      &LTerm::ProjectVar(ref target, _) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
      }
      &LTerm::ProjectIdent(ref target, _) => {
        self._ctx_exp(exp.lookup(target), ctx, env, tenv);
      }
      &LTerm::MX(_) => {}
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _ctx: unhandled term: {:?}", t);
      }
    }
  }

  fn _ctx(&mut self, tree: LTreeCell, ctx: LCtxRef, env: &mut Env, tenv: &mut TyEnv) {
    self._ctx_exp(tree.root(), ctx, env, tenv);
  }
}

impl LBuilder {
  fn _freectx_once_exp(&mut self, exp: LExprCell, env: &mut Env) -> LFreectxRef {
    match env._freectx(&exp) {
      Some(ctx) => return ctx,
      None => {}
    }
    let ctx = match &exp.term() {
      &LTerm::Top => {
        // FIXME: should yield the full ctx.
        unimplemented!();
      }
      &LTerm::Break(ref inner) => {
        self._freectx_once_exp(exp.lookup(inner), env)
      }
      &LTerm::Return(ref inner) => {
        self._freectx_once_exp(exp.lookup(inner), env)
      }
      &LTerm::Apply(ref head, ref args) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(head), env);
        for arg in args.iter() {
          let arg_ctx = self._freectx_once_exp(exp.lookup(arg), env);
          ctx = ctx.union(arg_ctx);
        }
        ctx
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(body), env);
        for p in params.iter() {
          ctx.freevars.remove_mut(p);
        }
        ctx
      }
      &LTerm::ACons(.., ref value, ref target) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(target), env);
        let value_ctx = self._freectx_once_exp(exp.lookup(value), env);
        ctx = ctx.union(value_ctx);
        ctx
      }
      &LTerm::PtlD(ref target) => {
        self._freectx_once_exp(exp.lookup(target), env)
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(rest), env);
        let mut body_ctx = self._freectx_once_exp(exp.lookup(body), env);
        body_ctx.freevars.remove_mut(name);
        ctx = ctx.union(body_ctx);
        ctx
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(fixbody), env);
        ctx.freevars.remove_mut(fixname);
        ctx
      }
      &LTerm::SFix(ref fixnames, ref fixbody) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(fixbody), env);
        for fixname in fixnames.iter() {
          ctx.freevars.remove_mut(fixname);
        }
        ctx
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(query), env);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut arm_ctx = self._freectx_once_exp(exp.lookup(arm), env);
          for pv in pat.vars().iter() {
            arm_ctx.freevars.remove_mut(pv);
          }
          ctx = ctx.union(arm_ctx);
        }
        ctx
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        let mut ctx = self._freectx_once_exp(exp.lookup(query), env);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut arm_ctx = self._freectx_once_exp(exp.lookup(arm), env);
          for pv in pat.vars().iter() {
            arm_ctx.freevars.remove_mut(pv);
          }
          ctx = ctx.union(arm_ctx);
        }
        ctx
      }
      &LTerm::STuple(ref elems) => {
        let mut ctx = LFreectxRef::default();
        for elem in elems.iter() {
          let elem_ctx = self._freectx_once_exp(exp.lookup(elem), env);
          ctx = ctx.union(elem_ctx);
        }
        ctx
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) => {
        LFreectxRef::default()
      }
      &LTerm::Lookup(ref var) => {
        let mut ctx = LFreectxRef::default();
        ctx.freevars.insert_mut(var.clone());
        ctx
      }
      &LTerm::ProjectVar(ref target, _) => {
        self._freectx_once_exp(exp.lookup(target), env)
      }
      &LTerm::ProjectIdent(ref target, _) => {
        self._freectx_once_exp(exp.lookup(target), env)
      }
      &LTerm::MX(_) => {
        LFreectxRef::default()
      }
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _freectx_once_exp: unhandled term: {:?}", t);
      }
    };
    env.unsafe_set_freectx(&exp, ctx.clone());
    ctx
  }

  fn _freectx_once(&mut self, tree: LTreeCell, env: &mut Env) -> LTreeCell {
    self._freectx_once_exp(tree.root(), env);
    tree
  }
}

impl LBuilder {
  fn _resolve_ctx(&mut self, tree: LTreeCell, env: &mut Env) -> LTreeCell {
    let new_root = self._resolve_ctx_exp(tree.root(), env);
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }

  fn _resolve_ctx_exp(&mut self, exp: LExprCell, env: &mut Env) -> LExprCell {
    match &exp.term() {
      &LTerm::Top => {
        exp
      }
      &LTerm::Break(ref inner) => {
        let inner = self._resolve_ctx_exp(exp.lookup(inner), env);
        exp.append(self, &mut |_| LTerm::Break(inner.loc()))
      }
      &LTerm::Return(ref inner) => {
        let inner = self._resolve_ctx_exp(exp.lookup(inner), env);
        exp.append(self, &mut |_| LTerm::Return(inner.loc()))
      }
      &LTerm::EnvIdxs(_) |
      &LTerm::EnvVars(_) |
      &LTerm::EImportVar(..) |
      &LTerm::EImportVars(..) |
      &LTerm::AApply(..) |
      &LTerm::AReturn(..) |
      &LTerm::ACons(..) => {
        // TODO
        exp
      }
      &LTerm::PtlD(ref target) => {
        let target = self._resolve_ctx_exp(exp.lookup(target), env);
        exp.append(self, &mut |_| LTerm::PtlD(target.loc()))
      }
      &LTerm::Apply(ref head, ref args) => {
        let head = self._resolve_ctx_exp(exp.lookup(head), env);
        let mut args_ = Vec::with_capacity(args.len());
        for arg in args.iter() {
          let arg = self._resolve_ctx_exp(exp.lookup(arg), env);
          args_.push(arg.loc());
        }
        exp.append(self, &mut |_| LTerm::Apply(
            head.loc(),
            args_.clone()
        ))
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._resolve_ctx_exp(exp.lookup(body), env);
        exp.append(self, &mut |_| LTerm::Lambda(
            params.clone(),
            body.loc()
        ))
      }
      &LTerm::FixLambda(..) => {
        unimplemented!();
      }
      &LTerm::Let(ref var, ref body, ref rest) => {
        let body = self._resolve_ctx_exp(exp.lookup(body), env);
        let rest = self._resolve_ctx_exp(exp.lookup(rest), env);
        exp.append(self, &mut |_| LTerm::Let(
            var.clone(),
            body.loc(),
            rest.loc()
        ))
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let query = self._resolve_ctx_exp(exp.lookup(query), env);
        let mut pat_arms_ = Vec::with_capacity(pat_arms.len());
        for (ref pat, ref arm) in pat_arms.iter() {
          let arm = self._resolve_ctx_exp(exp.lookup(arm), env);
          pat_arms_.push((pat.clone(), arm.loc()));
        }
        exp.append(self, &mut |_| LTerm::Match(
            query.loc(),
            pat_arms_.clone()
        ))
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        unimplemented!();
      }
      &LTerm::STuple(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          let elem = self._resolve_ctx_exp(exp.lookup(elem), env);
          elems_.push(elem.loc());
        }
        exp.append(self, &mut |_| LTerm::STuple(elems_.clone()))
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) |
      &LTerm::Lookup(_) => {
        exp
      }
      &LTerm::ProjectVar(ref target, ref var) => {
        let target = self._resolve_ctx_exp(exp.lookup(target), env);
        exp.append(self, &mut |_| LTerm::ProjectVar(
            target.loc(),
            var.clone()
        ))
      }
      &LTerm::ProjectIdent(ref target, ref ident) => {
        let target = self._resolve_ctx_exp(exp.lookup(target), env);
        exp.append(self, &mut |_| LTerm::ProjectIdent(
            target.loc(),
            ident.clone()
        ))
      }
      &LTerm::MX(_) => {
        exp
      }
      &LTerm::LookupIdent(ref ident) => {
        match env._ctx(&exp) {
          None => {
            exp
          }
          Some(ctx) => match ctx._lookup_ident(ident) {
            None => panic!(),
            Some(var) => {
              exp.append(self, &mut |_| LTerm::Lookup(var.clone()))
            }
          }
        }
      }
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _resolve_ctx_exp: unhandled term: {:?}", t);
      }
    }
  }
}

impl LBuilder {
  fn _gc(&mut self, tree: LTreeCell) -> LTreeCell {
    unimplemented!();
  }
}

enum ResolveAdj<E> {
  Primal(E),
  //Bridge(E),
  Bridge(E, bool),
  Dual(E, E, /*bool*/),
  Pair(E, bool),
  //Defer,
  Error,
}

enum ResolveAdjResult<E> {
  Primal(E),
  //Bridge(E),
  Bridge(E, bool),
  //Defer(E, AdjWork),
  Error(E, AdjWork),
}

#[derive(Debug)]
enum AdjError {
  //Nonscalar,
  Nonsmooth,
  NonsmoothParam(LVar),
  EnvMissingIdent(LIdent),
  NonEnvType,
}

#[derive(Default)]
struct AdjWork {
  appended:     VecDeque<LLabel>,
  //deferred:     VecDeque<LLabel>,
  errored:      VecDeque<(LLabel, AdjError)>,
}

impl LBuilder {
  fn _resolve_adj(&mut self, tree: LTreeCell, env: &mut Env, tenv: &mut TyEnv, t_work: &mut TyWork) -> ResolveAdjResult<LTreeCell> {
    let mut work = AdjWork::default();
    match self._resolve_adj_exp(tree.root(), env, tenv, t_work, &mut work) {
      ResolveAdj::Primal(_) => ResolveAdjResult::Primal(tree),
      ResolveAdj::Bridge(new_root, incomplete) => {
        new_root.unsafe_set_self_root();
        ResolveAdjResult::Bridge(LTreeCell{
          view: new_root.view.into(),
          data: new_root.tree.data.clone(),
        }, incomplete)
      }
      ResolveAdj::Dual(..) |
      ResolveAdj::Pair(..) => unreachable!(),
      //ResolveAdj::Defer => ResolveAdjResult::Defer(tree, work),
      ResolveAdj::Error => ResolveAdjResult::Error(tree, work),
    }
  }

  /*fn _register_adj(&mut self, exp: &LExprCell, a_work: &mut AdjWork, adj: ResolveAdj<LExprCell>) -> ResolveAdj<LExprCell> {
    match &adj {
      &ResolveAdj::Primal(_) => {
        match self.reg_adj.get(exp.borrow()) {
          None => {}
          _ => panic!(),
        }
        self.reg_adj.insert_mut(exp.label(), RegisterAdj::Primal);
      }
      &ResolveAdj::Bridge(ref adj_e, incomplete) => {
        match self.reg_adj.get(exp.borrow()) {
          None |
          Some(&RegisterAdj::Bridge(_, true)) => {}
          _ => panic!(),
        }
        a_work.appended.push_front(adj_e.label());
        self.reg_adj.insert_mut(exp.label(), RegisterAdj::Bridge(adj_e.label(), incomplete));
      }
      &ResolveAdj::Dual(_, ref adj_e) => {
        match self.reg_adj.get(exp.borrow()) {
          None |
          Some(&RegisterAdj::Primal) |
          Some(&RegisterAdj::Bridge(..)) => {}
          _ => panic!(),
        }
        a_work.appended.push_front(adj_e.label());
        self.reg_adj.insert_mut(exp.label(), RegisterAdj::Dual(adj_e.label()));
      }
      &ResolveAdj::Pair(ref adj_e, incomplete) => {
        match self.reg_adj.get(exp.borrow()) {
          None |
          Some(&RegisterAdj::Primal) |
          Some(&RegisterAdj::Bridge(..)) |
          Some(&RegisterAdj::Pair(_, true)) => {}
          _ => panic!(),
        }
        a_work.appended.push_front(adj_e.label());
        self.reg_adj.insert_mut(exp.label(), RegisterAdj::Pair(adj_e.label(), incomplete));
      }
      _ => unreachable!(),
    }
    adj
  }*/

  fn _register_adj(&mut self, exp: &LExprCell, a_work: &mut AdjWork, adj: ResolveAdj<LExprCell>) -> ResolveAdj<LExprCell> {
    match &adj {
      &ResolveAdj::Primal(_) => {}
      &ResolveAdj::Bridge(ref adj_e, incomplete) => {
        a_work.appended.push_front(adj_e.label());
      }
      &ResolveAdj::Dual(_, ref adj_e) => {
        a_work.appended.push_front(adj_e.label());
      }
      &ResolveAdj::Pair(ref adj_e, incomplete) => {
        a_work.appended.push_front(adj_e.label());
      }
      _ => unreachable!(),
    }
    adj
  }

  fn _resolve_adj_exp(&mut self, exp: LExprCell, env: &mut Env, tenv: &mut TyEnv, t_work: &mut TyWork, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    /* NB: An example where `resolve_` does not return a primal or bridge
       expr:

          \f, x. d[f[x]].x
       =>
          \(f, f'), x. let match (_, a) = f'[x] in a[1.0].x

       i.e. there is no way to preserve the original signature.
    */
    /*match self.reg_adj.get(exp.borrow()) {
      Some(&RegisterAdj::Primal) => {
        return ResolveAdj::Primal(exp);
      }
      Some(&RegisterAdj::Bridge(ref adj_e, false)) => {
        return ResolveAdj::Bridge(exp.lookup_exp(adj_e), false);
      }
      None |
      Some(&RegisterAdj::Bridge(_, true)) => {}
      Some(_) => unreachable!(),
    }*/
    match &exp.term() {
      &LTerm::Top => {
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::EnvVars(ref keys) => {
        // FIXME
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::AApply(ref target, ref args) => {
        // FIXME
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::AReturn(ref params, ref target) => {
        // FIXME
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::ACons(ref var, ref binder, ref value, ref target) => {
        // FIXME
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::PtlD(ref target) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Flp => {
              let target_e = exp.lookup(target);
              let adj_target_e = match self._force_adj_dual_exp(target_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(..) |
                ResolveAdj::Pair(..) => unreachable!(),
                ResolveAdj::Dual(_, adj_target_e) => adj_target_e,
                //ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              };
              let unit_sink_e = exp.append(self, &mut |_| LTerm::FlpLit(1.0));
              let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                  adj_target_e.loc(),
                  vec![unit_sink_e.loc()]
              ));
              self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, false))
            }
            &LTy::Fun(ref _dom_tys, ref ret_ty) => {
              match &**ret_ty {
                &LTy::Flp => {
                  // TODO: `d[]` syntax for smooth scalar functions.
                  unimplemented!();
                }
                _ => {
                  // TODO: distinguish b/w nonscalar and nonsmooth cases.
                  work.errored.push_back((exp.label(), AdjError::Nonsmooth));
                  ResolveAdj::Error
                }
              }
            }
            _ => {
              // TODO: distinguish b/w nonscalar and nonsmooth cases.
              work.errored.push_back((exp.label(), AdjError::Nonsmooth));
              ResolveAdj::Error
            }
          }
        } else {
          self._register_adj(&exp, work, ResolveAdj::Bridge(exp.clone(), true))
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        let mut incomplete = false;
        let head_e = exp.lookup(head);
        match self._resolve_adj_exp(head_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(head_e) => {
            let mut any_bridge = false;
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args.iter() {
              let arg_e = exp.lookup(arg);
              match self._resolve_adj_exp(arg_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(arg_e) => {
                  new_args.push(arg_e);
                }
                ResolveAdj::Bridge(arg_e, arg_defer) => {
                  incomplete |= arg_defer;
                  any_bridge = true;
                  new_args.push(arg_e);
                }
                ResolveAdj::Dual(..) |
                ResolveAdj::Pair(..) => unreachable!(),
                //ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              }
            }
            if any_bridge {
              let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                  head_e.loc(),
                  new_args.iter().map(|e| e.loc()).collect()
              ));
              self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
            } else {
              assert!(!incomplete);
              self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
            }
          }
          ResolveAdj::Bridge(new_head_e, head_defer) => {
            incomplete |= head_defer;
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args.iter() {
              let arg_e = exp.lookup(arg);
              match self._resolve_adj_exp(arg_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(arg_e) => {
                  new_args.push(arg_e);
                }
                ResolveAdj::Bridge(new_arg_e, arg_defer) => {
                  incomplete |= arg_defer;
                  new_args.push(new_arg_e);
                }
                ResolveAdj::Dual(..) |
                ResolveAdj::Pair(..) => unreachable!(),
                //ResolveAdj::Defer => return ResolveAdj::Defer,
                ResolveAdj::Error => return ResolveAdj::Error,
              }
            }
            let new_exp = exp.append(self, &mut |_| LTerm::Apply(
                new_head_e.loc(),
                new_args.iter().map(|e| e.loc()).collect()
            ));
            self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body_e = exp.lookup(body);
        match self._resolve_adj_exp(body_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) => {
            self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
          }
          ResolveAdj::Bridge(new_body_e, body_defer) => {
            // FIXME: need to look into the params types.
            let mut new_body_fixup_e = new_body_e;
            for param in params.iter().rev() {
              match self._lookup_adj_var(param) {
                None => {}
                Some(adj_param) => {
                  let tmp_sink = self.fresh_anon_var();
                  tenv.annotate(&tmp_sink, tenv.lookup_var(&exp, param).into());
                  let param_target_e = exp.append(self, &mut |_| LTerm::EnvVars(vec![]));
                  let param_adj_e = exp.append(self, &mut |_| LTerm::Lambda(
                      vec![tmp_sink.clone()],
                      param_target_e.loc()
                  ));
                  new_body_fixup_e = exp.append(self, &mut |_| LTerm::Let(
                      adj_param.clone(),
                      param_adj_e.loc(),
                      new_body_fixup_e.loc()
                  ));
                }
              }
            }
            let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
                params.clone(),
                new_body_fixup_e.loc()
            ));
            self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, body_defer))
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::FixLambda(ref fixname, ref params, ref body) => {
        // TODO
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let mut incomplete = false;
        let body_e = exp.lookup(body);
        let rest_e = exp.lookup(rest);
        match self._resolve_adj_exp(rest_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(rest_e) => {
            match self._resolve_adj_exp(body_e, env, tenv, t_work, work) {
              ResolveAdj::Primal(_) => {
                self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
              }
              ResolveAdj::Bridge(new_body_e, body_defer) => {
                incomplete |= body_defer;
                let new_exp = exp.append(self, &mut |_| LTerm::Let(
                    name.clone(),
                    new_body_e.loc(),
                    rest_e.loc()
                ));
                self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
              }
              ResolveAdj::Dual(..) |
              ResolveAdj::Pair(..) => unreachable!(),
              //ResolveAdj::Defer => ResolveAdj::Defer,
              ResolveAdj::Error => ResolveAdj::Error,
            }
          }
          ResolveAdj::Bridge(new_rest_e, rest_defer) => {
            incomplete |= rest_defer;
            match self._lookup_adj_var(name) {
              None => match self._resolve_adj_exp(body_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      body_e.loc(),
                      new_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
                }
                ResolveAdj::Bridge(new_body_e, body_defer) => {
                  incomplete |= body_defer;
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      new_body_e.loc(),
                      new_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
                }
                ResolveAdj::Dual(..) |
                ResolveAdj::Pair(..) => unreachable!(),
                //ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              },
              Some(adj_name) => match self._force_adj_pair_exp(body_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(..) |
                ResolveAdj::Dual(..) => unreachable!(),
                ResolveAdj::Pair(adj_body_e, body_defer) => {
                  incomplete |= body_defer;
                  let new_exp = exp.append(self, &mut |_| LTerm::Match(
                      adj_body_e.loc(),
                      vec![(
                        LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                        new_rest_e.loc()
                      )]
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
                }
                //ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              }
            }
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixbody_e = exp.lookup(fixbody);
        let redo_fixbody_e = fixbody_e.clone();
        match self._resolve_adj_exp(fixbody_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) => {
            self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
          }
          ResolveAdj::Bridge(new_fixbody_e, fixbody_defer) => {
            match self._lookup_adj_var(fixname) {
              None => {
                let new_exp = exp.append(self, &mut |_| LTerm::Fix(
                    fixname.clone(),
                    new_fixbody_e.loc()
                ));
                self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, fixbody_defer))
              }
              Some(adj_fixname) => match self._force_adj_pair_exp(redo_fixbody_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(..) |
                ResolveAdj::Dual(..) => unreachable!(),
                ResolveAdj::Pair(adj_fixbody_e, redo_fixbody_defer) => {
                  let adj_fix_e = exp.append(self, &mut |_| LTerm::SFix(
                      vec![fixname.clone(), adj_fixname.clone()],
                      adj_fixbody_e.loc()
                  ));
                  let tmp_new_name = self.fresh_anon_var();
                  let tmp_adj_name = self.lookup_or_fresh_adj_var(&tmp_new_name);
                  let tmp_new_name_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_new_name.clone()));
                  let new_exp = exp.append(self, &mut |_| LTerm::Match(
                      adj_fix_e.loc(),
                      vec![(
                        LPat::STuple(vec![tmp_new_name.clone().into(), tmp_adj_name.clone().into()]).into(),
                        tmp_new_name_e.loc()
                      )]
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, redo_fixbody_defer))
                }
                //ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              }
            }
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        let mut incomplete = false;
        let mut any_bridge = false;
        //let mut pats = Vec::with_capacity(pat_arms.len());
        //let mut arms = Vec::with_capacity(pat_arms.len());
        let mut pat_arms_ = Vec::with_capacity(pat_arms.len());
        for &(ref pat, ref arm) in pat_arms.iter() {
          match self._resolve_adj_exp(exp.lookup(arm), env, tenv, t_work, work) {
            ResolveAdj::Primal(arm_e) => {
              // TODO
              //unimplemented!();
              //pats.push(pat.clone());
              pat_arms_.push((pat.clone(), arm_e.loc()));
            }
            ResolveAdj::Bridge(new_arm_e, arm_defer) => {
              // TODO
              incomplete |= arm_defer;
              any_bridge = true;
              //unimplemented!();
              let (pat_vars, pat_vars_set) = pat.vars_set();
              for pv in pat_vars.iter() {
                match self._lookup_adj_var(pv) {
                  None => {}
                  Some(adj_pv) => if !pat_vars_set.contains(&adj_pv) {
                    panic!("unimplemented case: non-adj-closed pattern");
                  }
                }
              }
              //pats.push(pat.clone());
              pat_arms_.push((pat.clone(), new_arm_e.loc()));
            }
            ResolveAdj::Dual(..) |
            ResolveAdj::Pair(..) => unreachable!(),
            ResolveAdj::Error => return ResolveAdj::Error,
          }
        }
        let query_e = match self._resolve_adj_exp(exp.lookup(query), env, tenv, t_work, work) {
          ResolveAdj::Primal(query_e) => {
            query_e
          }
          ResolveAdj::Bridge(new_query_e, query_defer) => {
            incomplete |= query_defer;
            any_bridge = true;
            new_query_e
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          ResolveAdj::Error => return ResolveAdj::Error,
        };
        if any_bridge {
          // TODO
          //unimplemented!();
          let new_exp = exp.append(self, &mut |_| LTerm::Match(
              query_e.loc(),
              pat_arms_.clone()
          ));
          self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
        } else {
          assert!(!incomplete);
          self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
        }
      }
      &LTerm::STuple(ref elems) => {
        let mut incomplete = false;
        let mut any_bridge = false;
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          match self._resolve_adj_exp(exp.lookup(elem), env, tenv, t_work, work) {
            ResolveAdj::Primal(elem_e) => {
              elems_.push(elem_e.loc());
            }
            ResolveAdj::Bridge(new_elem_e, elem_defer) => {
              incomplete |= elem_defer;
              any_bridge = true;
              elems_.push(new_elem_e.loc());
            }
            ResolveAdj::Dual(..) |
            ResolveAdj::Pair(..) => unreachable!(),
            ResolveAdj::Error => return ResolveAdj::Error,
          }
        }
        if any_bridge {
          let new_exp = exp.append(self, &mut |_| LTerm::STuple(
              elems_.clone()
          ));
          self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, incomplete))
        } else {
          assert!(!incomplete);
          self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
        }
      }
      &LTerm::UnitLit |
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) |
      &LTerm::Lookup(_) => {
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::ProjectVar(_, _) => {
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      &LTerm::ProjectIdent(ref target, ref ident) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Env(ref _idxs, ref keys, ref ctx) => {
              match ctx._lookup_ident(ident) {
                Some(key) => {
                  match keys.get(&key) {
                    Some(_) => {}
                    None => unreachable!(),
                  }
                  let target_e = exp.lookup(target);
                  match self._resolve_adj_exp(target_e, env, tenv, t_work, work) {
                    ResolveAdj::Primal(target_e) => {
                      /*let lookup_e = exp.append(self, &mut |_| LTerm::Lookup(key.clone()));
                      let new_exp = exp.append(self, &mut |_| LTerm::Import(
                          LEnvMask::Var(key.clone()),
                          target_e.loc(),
                          lookup_e.loc()
                      ));*/
                      let new_exp = exp.append(self, &mut |_| LTerm::ProjectVar(
                          target_e.loc(),
                          key.clone()
                      ));
                      self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, false))
                    }
                    ResolveAdj::Bridge(new_target_e, target_defer) => {
                      /*let lookup_e = exp.append(self, &mut |_| LTerm::Lookup(key.clone()));
                      let new_exp = exp.append(self, &mut |_| LTerm::Import(
                          LEnvMask::Var(key.clone()),
                          new_target_e.loc(),
                          lookup_e.loc()
                      ));*/
                      let new_exp = exp.append(self, &mut |_| LTerm::ProjectVar(
                          new_target_e.loc(),
                          key.clone()
                      ));
                      self._register_adj(&exp, work, ResolveAdj::Bridge(new_exp, target_defer))
                    }
                    ResolveAdj::Dual(..) |
                    ResolveAdj::Pair(..) => unreachable!(),
                    //ResolveAdj::Defer => ResolveAdj::Defer,
                    ResolveAdj::Error => ResolveAdj::Error,
                  }
                }
                None => {
                  work.errored.push_back((exp.label(), AdjError::EnvMissingIdent(ident.clone())));
                  ResolveAdj::Error
                }
              }
            }
            _ => {
              work.errored.push_back((exp.label(), AdjError::NonEnvType));
              ResolveAdj::Error
            }
          }
        } else {
          self._register_adj(&exp, work, ResolveAdj::Bridge(exp.clone(), true))
        }
      }
      &LTerm::MX(_) => {
        // TODO
        self._register_adj(&exp, work, ResolveAdj::Primal(exp.clone()))
      }
      // TODO
      //_ => unimplemented!(),
      t => panic!("_resolve_adj_exp: unimplemented term: {:?}", t),
    }
  }

  fn _force_adj_dual_exp(&mut self, exp: LExprCell, env: &mut Env, tenv: &mut TyEnv, t_work: &mut TyWork, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    /*match self.reg_adj.get(exp.borrow()) {
      None |
      Some(&RegisterAdj::Primal) |
      Some(&RegisterAdj::Bridge(_, _)) => {}
      Some(&RegisterAdj::Dual(ref adj_e)) => {
        let adj_exp = exp.lookup_exp(adj_e);
        return ResolveAdj::Dual(exp, adj_exp);
      }
      Some(_) => unreachable!(),
    }*/
    match &exp.term() {
      // TODO: cases.
      &LTerm::FlpLit(_) => {
        let tmp_sink = self.fresh_anon_var();
        tenv.annotate(&tmp_sink, Tyexp::Flp.into());
        let target_e = exp.append(self, &mut |_| LTerm::EnvVars(vec![]));
        let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
            vec![tmp_sink.clone()],
            target_e.loc()
        ));
        self._register_adj(&exp, work, ResolveAdj::Dual(exp.clone(), new_exp))
      }
      &LTerm::Lookup(ref var) => {
        if let Some((_, _, ty)) = tenv.mgu_var(&exp, var) {
          match &*ty {
            &LTy::Flp => {
              let tmp_sink = self.fresh_anon_var();
              tenv.annotate(&tmp_sink, tenv.lookup_var(&exp, var).into());
              let adj_var = self.lookup_or_fresh_adj_var(var);
              /*
              let mut adj_ctx = LFreeAdjCtxRef::default();
              let adj_var = adj_ctx.lookup_or_bind_fresh_mut(var, || self.fresh_anon_var());
              */
              let adj_var_e = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
              let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
              let adj_app_e = exp.append(self, &mut |_| LTerm::Apply(
                  adj_var_e.loc(),
                  vec![tmp_sink_e.loc()]
              ));
              let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
              let binder = self.lookup_var(var);
              /*let ident = env.lookup_var(&exp, var);*/
              let cons_e = exp.append(self, &mut |_| LTerm::ACons(
                  var.clone(),
                  binder.clone(),
                  tmp_sink_e.loc(),
                  adj_app_e.loc()
              ));
              let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
                  vec![tmp_sink.clone()],
                  cons_e.loc()
              ));
              self._register_adj(&exp, work, ResolveAdj::Dual(exp.clone(), new_exp))
            }
            &LTy::Fun(..) => {
              // FIXME: scalar/smooth.
              let adj_var = self.lookup_or_fresh_adj_var(var);
              let new_exp = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
              self._register_adj(&exp, work, ResolveAdj::Dual(exp.clone(), new_exp))
            }
            _ => unimplemented!(),
          }
        } else {
          // TODO
          //work.deferred.push_back(exp.label());
          //ResolveAdj::Defer
          unimplemented!();
        }
      }
      _ => unimplemented!(),
    }
  }

  fn _force_adj_pair_exp(&mut self, exp: LExprCell, env: &mut Env, tenv: &mut TyEnv, t_work: &mut TyWork, work: &mut AdjWork) -> ResolveAdj<LExprCell> {
    /*match self.reg_adj.get(exp.borrow()) {
      None |
      Some(&RegisterAdj::Primal) |
      Some(&RegisterAdj::Bridge(..)) |
      Some(&RegisterAdj::Pair(_, true)) => {}
      Some(&RegisterAdj::Pair(ref adj_e, false)) => {
        return ResolveAdj::Pair(exp.lookup_exp(adj_e), false);
      }
      Some(_) => unreachable!(),
    }*/
    match &exp.term() {
      // TODO: cases.
      &LTerm::Apply(ref head, ref args) => {
        let mut incomplete = false;
        let head_e = exp.lookup(head);
        match self._force_adj_dual_exp(head_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          ResolveAdj::Dual(_, adj_head_e) => {
            let tmp_new = self.fresh_anon_var();
            let tmp_adj = self.lookup_or_fresh_adj_var(&tmp_new);
            let tmp_sink = self.fresh_anon_var();
            let exp_ty = tenv.lookup_exp(&exp);
            tenv.annotate(&tmp_sink, exp_ty.into());
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
            // TODO: inspect the function type.
            let mut adj_app_app_fixup_args = Vec::with_capacity(args.len());
            for (idx, arg) in args.iter().enumerate() {
              let arg_e = exp.lookup(arg);
              match &arg_e.term() {
                &LTerm::BitLit(_) |
                &LTerm::IntLit(_) |
                &LTerm::FlpLit(_) => {}
                &LTerm::Lookup(ref arg_var) => {
                  match tenv.mgu_var(&exp, arg_var) {
                    None => {
                      incomplete = true;
                    }
                    Some((_, _, ty)) => {
                      match &*ty {
                        // TODO: fixup any smooth type.
                        &LTy::Flp => {
                          let arg_binder = self.lookup_var(arg_var);
                          let arg_adj = self.lookup_or_fresh_adj_var(arg_var);
                          adj_app_app_fixup_args.push((idx, arg_var.clone(), arg_binder, arg_adj));
                        }
                        _ => {}
                      }
                    }
                  }
                }
                _ => unimplemented!(),
              }
            }
            let adj_app_app_fixup_e = exp.append(self, &mut |_| LTerm::AApply(
                adj_app_app_e.loc(),
                adj_app_app_fixup_args.clone()
            ));
            let target_e = adj_app_app_fixup_e;
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
            self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
          }
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut incomplete = false;
        let body_e = exp.lookup(body);
        match self._force_adj_pair_exp(body_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(..) |
          ResolveAdj::Dual(..) => unreachable!(),
          ResolveAdj::Pair(adj_body_e, body_defer) => {
            incomplete |= body_defer;
            let tmp_new = self.fresh_anon_var();
            let tmp_adj = self.lookup_or_fresh_adj_var(&tmp_new);
            let tmp_sink = self.fresh_anon_var();
            let body_ty = tenv.lookup_exp(body);
            tenv.annotate(&tmp_sink, body_ty.into());
            let mut fixup_params = Vec::with_capacity(params.len());
            for (idx, param) in params.iter().enumerate() {
              match self._lookup_adj_var(param) {
                None => {}
                Some(_) => {
                  match tenv.mgu_var(body, param) {
                    None => {
                      incomplete = true;
                    }
                    Some((_, _, ty)) => match &*ty {
                      // TODO: allowed smooth types.
                      &LTy::Flp => {}
                      _ => {
                        work.errored.push_back((exp.label(), AdjError::NonsmoothParam(param.clone())));
                        return ResolveAdj::Error;
                      }
                    }
                  }
                  fixup_params.push((idx, param.clone()));
                }
              }
            }
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj.clone()));
            let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
            let adj_body_app_e = exp.append(self, &mut |_| LTerm::Apply(
                tmp_adj_e.loc(),
                vec![tmp_sink_e.loc()]
            ));
            let adj_body_app_fixup_e = exp.append(self, &mut |_| LTerm::AReturn(
                //LEnvMask::All,
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
            let mut adj_body_fixup_e = adj_body_e;
            for param in params.iter().rev() {
              match self._lookup_adj_var(param) {
                None => {}
                Some(adj_param) => {
                  let tmp_sink = self.fresh_anon_var();
                  tenv.annotate(&tmp_sink, tenv.lookup_var(body, param).into());
                  let param_target_e = exp.append(self, &mut |_| LTerm::EnvVars(vec![]));
                  let param_adj_e = exp.append(self, &mut |_| LTerm::Lambda(
                      vec![tmp_sink.clone()],
                      param_target_e.loc()
                  ));
                  adj_body_fixup_e = exp.append(self, &mut |_| LTerm::Let(
                      adj_param.clone(),
                      param_adj_e.loc(),
                      adj_body_fixup_e.loc()
                  ));
                }
              }
            }
            adj_body_fixup_e = exp.append(self, &mut |_| LTerm::Match(
                adj_body_fixup_e.loc(),
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
            let tmp_adj_name = self.lookup_or_fresh_adj_var(&tmp_new_name);
            let tmp_adj_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_adj_name.clone()));
            let mut new_params = Vec::with_capacity(params.len());
            for param in params.iter() {
              let new_param = match self.lookup_var(param) {
                LVarBinder::Ident(ident) => {
                  self.fresh_ident_var(ident)
                }
                _ => self.fresh_anon_var(),
              };
              let param_ty = tenv.lookup_var(body, param);
              tenv.annotate(&new_param, param_ty.into());
              new_params.push(new_param);
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
            let result_adj_name = self.lookup_or_fresh_adj_var(&result_pri_name);
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
            self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
          }
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::FixLambda(ref fixname, ref params, ref body) => {
        let body_e = exp.lookup(body);
        match self._force_adj_pair_exp(body_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(..) |
          ResolveAdj::Dual(..) => unreachable!(),
          ResolveAdj::Pair(adj_body_e, body_defer) => {
            // TODO
            unimplemented!();
          }
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        // TODO
        let mut incomplete = false;
        let body_e = exp.lookup(body);
        let rest_e = exp.lookup(rest);
        match self._force_adj_pair_exp(rest_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(..) |
          ResolveAdj::Dual(..) => unreachable!(),
          ResolveAdj::Pair(adj_rest_e, rest_defer) => {
            incomplete |= rest_defer;
            match self._lookup_adj_var(name) {
              None => match self._resolve_adj_exp(body_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(body_e) => {
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      body_e.loc(),
                      adj_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
                }
                ResolveAdj::Bridge(new_body_e, body_defer) => {
                  incomplete |= body_defer;
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      name.clone(),
                      new_body_e.loc(),
                      adj_rest_e.loc()
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
                }
                ResolveAdj::Dual(..) |
                ResolveAdj::Pair(..) => unreachable!(),
                //ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              },
              Some(adj_name) => match self._force_adj_pair_exp(body_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(..) |
                ResolveAdj::Dual(..) => unreachable!(),
                ResolveAdj::Pair(adj_body_e, body_defer) => {
                  incomplete |= body_defer;
                  let new_exp = exp.append(self, &mut |_| LTerm::Match(
                      adj_body_e.loc(),
                      vec![(
                        LPat::STuple(vec![name.clone().into(), adj_name.clone().into()]).into(),
                        adj_rest_e.loc()
                      )]
                  ));
                  self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
                }
                //ResolveAdj::Defer => ResolveAdj::Defer,
                ResolveAdj::Error => ResolveAdj::Error,
              }
            }
          }
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixbody_e = exp.lookup(fixbody);
        match self._force_adj_pair_exp(fixbody_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(_) |
          ResolveAdj::Bridge(..) |
          ResolveAdj::Dual(..) => unreachable!(),
          ResolveAdj::Pair(adj_fixbody_e, fixbody_defer) => {
            let adj_fixname = self.lookup_or_fresh_adj_var(fixname);
            let new_exp = exp.append(self, &mut |_| LTerm::SFix(
                vec![fixname.clone(), adj_fixname.clone()],
                adj_fixbody_e.loc()
            ));
            self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, fixbody_defer))
          }
          //ResolveAdj::Defer => ResolveAdj::Defer,
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        // TODO
        let mut incomplete = false;
        let query_e = exp.lookup(query);
        match self._resolve_adj_exp(query_e, env, tenv, t_work, work) {
          ResolveAdj::Primal(query_e) => {
            let mut adj_pat_arms = Vec::with_capacity(pat_arms.len());
            for &(ref pat, ref arm) in pat_arms.iter() {
              let arm_e = exp.lookup(arm);
              match self._force_adj_pair_exp(arm_e, env, tenv, t_work, work) {
                ResolveAdj::Primal(_) |
                ResolveAdj::Bridge(_, _) |
                ResolveAdj::Dual(_, _) => unreachable!(),
                ResolveAdj::Pair(adj_arm_e, arm_defer) => {
                  incomplete |= arm_defer;
                  adj_pat_arms.push((pat.clone(), adj_arm_e.loc()));
                }
                ResolveAdj::Error => return ResolveAdj::Error,
              }
            }
            if pat_arms.len() == 1 {
              let new_exp = exp.append(self, &mut |_| LTerm::Match(
                  query_e.loc(),
                  adj_pat_arms.clone()
              ));
              self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
            } else {
              /*// FIXME: this is more for debugging.
              let mut any_diff = false;
              let mut union_freectx = LFreectxRef::default();
              for &(_, ref adj_arm) in adj_pat_arms.iter() {
                let arm_freectx = self._freectx_once_exp(exp.lookup(adj_arm));
                union_freectx = union_freectx.union(arm_freectx);
              }
              for &(_, ref adj_arm) in adj_pat_arms.iter() {
                let arm_freectx = self._freectx_once_exp(exp.lookup(adj_arm));
                let diff_freectx = union_freectx.clone().diff(arm_freectx);
                if !diff_freectx.freevars.is_empty() {
                  any_diff = true;
                  break;
                }
              }*/
              /*if any_diff {*/
                // FIXME
                println!("WARNING: _force_adj_pair_exp: possible mismatch");
                //incomplete = true;
                let new_exp = exp.append(self, &mut |_| LTerm::Match(
                //let new_exp = exp.append(self, &mut |_| LTerm::Mismatch(
                    query_e.loc(),
                    adj_pat_arms.clone()
                ));
                self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
              /*} else {
                //println!("DEBUG: _force_adj_pair_exp: no mismatch, OK!");
                let new_exp = exp.append(self, &mut |_| LTerm::Match(
                    query_e.loc(),
                    adj_pat_arms.clone()
                ));
                self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, incomplete))
              }*/
            }
          }
          ResolveAdj::Bridge(new_query_e, query_defer) => {
            // TODO
            unimplemented!();
          }
          ResolveAdj::Dual(..) |
          ResolveAdj::Pair(..) => unreachable!(),
          ResolveAdj::Error => ResolveAdj::Error,
        }
      }
      &LTerm::FlpLit(_) => {
        let tmp_sink = self.fresh_anon_var();
        tenv.annotate(&tmp_sink, Tyexp::Flp.into());
        let target_e = exp.append(self, &mut |_| LTerm::EnvVars(vec![]));
        let adj_e = exp.append(self, &mut |_| LTerm::Lambda(
            vec![tmp_sink.clone()],
            target_e.loc()
        ));
        let new_exp = exp.append(self, &mut |_| LTerm::STuple(
            vec![exp.loc(), adj_e.loc()]
        ));
        self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, false))
      }
      &LTerm::Lookup(ref var) => {
        if let Some((_, _, ty)) = tenv.mgu_var(&exp, var) {
          match &*ty {
            &LTy::Flp => {
              let tmp_sink = self.fresh_anon_var();
              tenv.annotate(&tmp_sink, tenv.lookup_var(&exp, var).into());
              let adj_var = self.lookup_or_fresh_adj_var(var);
              /*
              let mut adj_ctx = LFreeAdjCtxRef::default();
              let adj_var = adj_ctx.lookup_or_bind_fresh_mut(var, || self.fresh_anon_var());
              */
              let adj_var_e = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
              let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
              let adj_app_e = exp.append(self, &mut |_| LTerm::Apply(
                  adj_var_e.loc(),
                  vec![tmp_sink_e.loc()]
              ));
              let tmp_sink_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_sink.clone()));
              let binder = self.lookup_var(var);
              let cons_e = exp.append(self, &mut |_| LTerm::ACons(
                  var.clone(),
                  binder.clone(),
                  tmp_sink_e.loc(),
                  adj_app_e.loc()
              ));
              let adj_e = exp.append(self, &mut |_| LTerm::Lambda(
                  vec![tmp_sink.clone()],
                  cons_e.loc()
              ));
              let new_exp = exp.append(self, &mut |_| LTerm::STuple(
                  vec![exp.loc(), adj_e.loc()]
              ));
              self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, false))
            }
            &LTy::Fun(..) => {
              // FIXME: scalar/smooth.
              let adj_var = self.lookup_or_fresh_adj_var(var);
              /*
              let mut adj_ctx = LFreeAdjCtxRef::default();
              let adj_var = adj_ctx.lookup_or_bind_fresh_mut(var, || self.fresh_anon_var());
              */
              let adj_e = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
              let new_exp = exp.append(self, &mut |_| LTerm::STuple(
                  vec![exp.loc(), adj_e.loc()]
              ));
              self._register_adj(&exp, work, ResolveAdj::Pair(new_exp, false))
            }
            _ => unimplemented!(),
          }
        } else {
          // TODO
          //work.deferred.push_back(exp.label());
          //ResolveAdj::Defer
          unimplemented!();
        }
      }
      _ => unimplemented!(),
    }
  }
}

impl LBuilder {
  fn _resolve_post_adj(&mut self, tree: LTreeCell, env: &mut Env, tenv: &mut TyEnv) -> LTreeCell {
    // TODO
    let new_root = self._resolve_post_adj_exp(tree.root(), env, tenv);
    new_root.unsafe_set_self_root();
    LTreeCell{
      view: new_root.view.into(),
      data: new_root.tree.data.clone(),
    }
  }

  fn _resolve_post_adj_exp(&mut self, exp: LExprCell, env: &mut Env, tenv: &mut TyEnv) -> LExprCell {
    match &exp.term() {
      &LTerm::Top => {
        exp
      }
      &LTerm::EnvIdxs(ref keys) => {
        let mut keys_ = Vec::with_capacity(keys.len());
        for &(ref v, ref value) in keys.iter() {
          let value = self._resolve_post_adj_exp(exp.lookup(value), env, tenv);
          keys_.push((v.clone(), value.loc()));
        }
        let new_exp = exp.append(self, &mut |_| LTerm::EnvIdxsLazy(
            keys_.clone()
        ));
        new_exp
      }
      &LTerm::EnvVars(ref keys) => {
        let mut keys_ = Vec::with_capacity(keys.len());
        for &(ref v, ref value) in keys.iter() {
          let value = self._resolve_post_adj_exp(exp.lookup(value), env, tenv);
          keys_.push((v.clone(), value.loc()));
        }
        let new_exp = exp.append(self, &mut |_| LTerm::EnvVarsLazy(
            keys_.clone()
        ));
        new_exp
      }
      &LTerm::AApply(ref target, ref args) => {
        if let Some((_, _, tg_ty)) = tenv.mgu_exp(target) {
          match &*tg_ty {
            &LTy::Env(ref tg_idxs, ref tg_vars, ref _tg_binders) => {
              // FIXME
              // TODO: bind the immediately returned target env, since we will
              // be dereferencing it quite a bit.
              let imm_target_e = self._resolve_post_adj_exp(exp.lookup(target), env, tenv);
              // FIXME: init `rollup_vars` with keys from `tg_vars`.
              //let mut rollup_vars = IHTreapSet::default();
              let mut rollup_vars = tg_vars.keys();
              let mut target_e = imm_target_e;
              for &(idx, ref var, _, ref adj_var) in args.iter() {
                if let Some((_, _, adj_ty)) = tenv.mgu_var(&exp, adj_var) {
                  match &*adj_ty {
                    &LTy::Fun(_, ref adj_ret_ty) => match &**adj_ret_ty {
                      &LTy::Env(_, ref arg_tg_vars, _) => {
                        // TODO
                        let adj_var_e = exp.append(self, &mut |_| LTerm::Lookup(adj_var.clone()));
                        /*
                        let arg_target_e = exp.append(self, &mut |_| LTerm::Apply(
                            adj_var_e.loc(),
                            vec![_]
                        ));
                        target_e = exp.append(self, &mut |_| LTerm::ESymmVars(
                            target_e.loc(),
                            arg_target_e.loc()
                        ));
                        */
                        let shared_vars = arg_tg_vars.set_intersection(&rollup_vars);
                        /*for v in shared_vars.iter() {
                          target_e = exp.append(self, &mut |_| LTerm::EConsVarLazy(
                              v.clone(),
                              _,
                              target_e.loc()
                          ));
                        }*/
                        rollup_vars.union_mut(&arg_tg_vars.keys());
                      }
                      _ => unreachable!(),
                    },
                    _ => unreachable!(),
                  }
                } else {
                  unreachable!();
                }
                if rollup_vars.contains(var) {
                  // TODO
                  /*target_e = exp.append(self, &mut |_| LTerm::EPopConsIdxLazy(
                      idx,
                      var.clone(),
                      _,
                      target_e.loc()
                  ));*/
                } else {
                  target_e = exp.append(self, &mut |_| LTerm::EPopIdx(
                      idx,
                      var.clone(),
                      target_e.loc()
                  ));
                  rollup_vars.insert_mut(var.clone());
                }
              }
              target_e
            }
            _ => unreachable!(),
          }
        } else {
          unreachable!();
        }
      }
      &LTerm::AReturn(ref params, ref target) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Env(ref _idx_keys, ref _var_keys, ref _binders) => {
              let target_e = self._resolve_post_adj_exp(exp.lookup(target), env, tenv);
              // TODO: check idxs and vars.
              let mut vars = Vec::with_capacity(params.len());
              for &(idx, ref var) in params.iter() {
                vars.push((var.clone(), idx));
              }
              let new_exp = exp.append(self, &mut |_| LTerm::EPopVars(
                  vars.clone(),
                  target_e.loc()
              ));
              new_exp
            }
            _ => unreachable!(),
          }
        } else {
          unreachable!();
        }
      }
      &LTerm::ACons(ref var, ref binder, ref value, ref target) => {
        if let Some((_, _, ty)) = tenv.mgu_exp(target) {
          match &*ty {
            &LTy::Env(ref _idx_keys, ref var_keys, ref binders) => {
              let value_e = self._resolve_post_adj_exp(exp.lookup(value), env, tenv);
              let target_e = self._resolve_post_adj_exp(exp.lookup(target), env, tenv);
              match var_keys.get(var) {
                None => {
                  let new_exp = exp.append(self, &mut |_| LTerm::EConsVarLazy(
                      var.clone(),
                      value_e.loc(),
                      target_e.loc()
                  ));
                  new_exp
                }
                Some(_) => {
                  // FIXME
                  // TODO: check binder.
                  let ctx = env.ctx(&exp);
                  let add_id = self.lookup_name("add");
                  let add_var = ctx.lookup_ident(add_id);
                  let tmp_var = self.fresh_anon_var();
                  let tmp_var_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_var.clone()));
                  let var_e = exp.append(self, &mut |_| LTerm::Lookup(var.clone()));
                  let old_value_e = exp.append(self, &mut |_| LTerm::EImportVar(
                      var.clone(),
                      tmp_var_e.loc(),
                      var_e.loc()
                  ));
                  let add_e = exp.append(self, &mut |_| LTerm::Lookup(add_var.clone()));
                  let new_value_e = exp.append(self, &mut |_| LTerm::Apply(
                      add_e.loc(),
                      vec![old_value_e.loc(), value_e.loc()],
                  ));
                  let tmp_var_e = exp.append(self, &mut |_| LTerm::Lookup(tmp_var.clone()));
                  let cons_e = exp.append(self, &mut |_| LTerm::EConsVarLazy(
                      var.clone(),
                      new_value_e.loc(),
                      tmp_var_e.loc()
                  ));
                  let new_exp = exp.append(self, &mut |_| LTerm::Let(
                      tmp_var.clone(),
                      target_e.loc(),
                      cons_e.loc()
                  ));
                  new_exp
                }
              }
            }
            _ => unreachable!(),
          }
        } else {
          unreachable!();
        }
      }
      &LTerm::Apply(ref head, ref args) => {
        let head = self._resolve_post_adj_exp(exp.lookup(head), env, tenv);
        let mut args_ = Vec::with_capacity(args.len());
        for arg in args.iter() {
          args_.push(self._resolve_post_adj_exp(exp.lookup(arg), env, tenv).loc());
        }
        let new_exp = exp.append(self, &mut |_| LTerm::Apply(
            head.loc(),
            args_.clone()
        ));
        new_exp
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._resolve_post_adj_exp(exp.lookup(body), env, tenv);
        let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
            params.clone(),
            body.loc()
        ));
        new_exp
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = self._resolve_post_adj_exp(exp.lookup(body), env, tenv);
        let rest = self._resolve_post_adj_exp(exp.lookup(rest), env, tenv);
        let new_exp = exp.append(self, &mut |_| LTerm::Let(
            name.clone(),
            body.loc(),
            rest.loc()
        ));
        new_exp
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixbody = self._resolve_post_adj_exp(exp.lookup(fixbody), env, tenv);
        let new_exp = exp.append(self, &mut |_| LTerm::Fix(
            fixname.clone(),
            fixbody.loc()
        ));
        new_exp
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        let query = self._resolve_post_adj_exp(exp.lookup(query), env, tenv);
        let mut pat_arms_ = Vec::with_capacity(pat_arms.len());
        for &(ref pat, ref arm) in pat_arms.iter() {
          let arm = self._resolve_post_adj_exp(exp.lookup(arm), env, tenv);
          pat_arms_.push((pat.clone(), arm.loc()));
        }
        let new_exp = exp.append(self, &mut |_| LTerm::Match(
            query.loc(),
            pat_arms_.clone()
        ));
        new_exp
      }
      &LTerm::STuple(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          let elem = self._resolve_post_adj_exp(exp.lookup(elem), env, tenv);
          elems_.push(elem.loc());
        }
        let new_exp = exp.append(self, &mut |_| LTerm::STuple(
            elems_.clone()
        ));
        new_exp
      }
      &LTerm::BitLit(_) |
      &LTerm::IntLit(_) |
      &LTerm::FlpLit(_) |
      &LTerm::Lookup(_) => {
        exp
      }
      &LTerm::ProjectVar(ref target, ref var) => {
        let target_e = self._resolve_post_adj_exp(exp.lookup(target), env, tenv);
        let var_e = exp.append(self, &mut |_| LTerm::Lookup(var.clone()));
        /*let mut sel_vars = IHTreapSet::default();
        sel_vars.insert_mut(var.clone());
        let new_exp = exp.append(self, &mut |_| LTerm::EImportVars(
            sel_vars.clone(),*/
        let new_exp = exp.append(self, &mut |_| LTerm::EImportVar(
            var.clone(),
            target_e.loc(),
            var_e.loc()
        ));
        new_exp
      }
      &LTerm::MX(_) => {
        exp
      }
      //_ => unimplemented!(),
      t => panic!("unimplemented: {:?}", t),
    }
  }
}

/*#[derive(Clone, Debug)]
enum Key {
  Idx(usize),
  Var(LVar),
}

type TyredexRef = Rc<RefCell<Tyredex>>;

#[derive(Clone)]
enum Tyredex {
  Var(LTyvar),
  Fun(Option<usize>, Vec<TyredexRef>, TyredexRef),
  Env(Option<Key>, IHTreapSet<usize>, IHTreapSet<LVar>, IHTreapMap<usize, LTyvar>, IHTreapMap<LVar, LTyvar>, IHTreapMap<LIdent, LVar>),
  STup(Option<usize>, Vec<LTyvar>),
  HTup,
  Bit,
  Int,
  Flp,
  VFlp,
  Unit,
}

#[derive(Clone)]
enum Tyexp_ {
  // TODO
  Var(LTyvar),
  Fun(Vec<LTyvar>, LTyvar),
  //Env(RBTreeMap<usize, LTyvar>, RBTreeMap<LVar, LTyvar>, RBTreeMap<LIdent, LVar>),
  Env(IHTreapSet<usize>, IHTreapSet<LVar>, IHTreapMap<usize, LTyvar>, IHTreapMap<LVar, LTyvar>, IHTreapMap<LIdent, LVar>),
  STup(Vec<LTyvar>),
  HTup,
  Bit,
  Int,
  Flp,
  VFlp,
  Unit,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Tydom {
  // TODO
  Var,
  Fun,
  Env,
  STup,
  HTup,
  Bit,
  Int,
  Flp,
  VFlp,
  Unit,
}*/

//#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[derive(Clone, Debug)]
enum Tyexp {
  // TODO
  Var(LTyvar),
  Fun(Vec<TyexpRef>, TyexpRef),
  //Env(RBTreeMap<usize, LTyvar>, RBTreeMap<LVar, LTyvar>, RBTreeMap<LIdent, LVar>),
  //Env(RBTreeMap<usize, TyexpRef>, RBTreeMap<LVar, TyexpRef>, RBTreeMap<LIdent, LVar>),
  //Env(RBTreeSet<usize>, RBTreeMap<usize, TyexpRef>, RBTreeSet<LVar>, RBTreeMap<LVar, TyexpRef>, RBTreeMap<LIdent, LVar>),
  //Env(IHTreapMap<usize, TyexpRef>, IHTreapMap<LVar, TyexpRef>, IHTreapMap<LIdent, LVar>),
  Env(IHTreapMap<usize, TyexpRef>, IHTreapMap<LVar, TyexpRef>, LCtxRef),
  STup(Vec<TyexpRef>),
  HTup,
  Bit,
  Int,
  Flp,
  VFlp,
  Unit,
}

//#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[derive(Clone, Debug)]
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

//#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[derive(Clone, Debug)]
pub enum LTy {
  Fun(Vec<LTyRef>, LTyRef),
  //Env(RBTreeMap<usize, LTyRef>, RBTreeMap<LVar, LTyRef>, RBTreeMap<LIdent, LVar>),
  //Env(DebugRBTreeMap<usize, LTyRef>, DebugRBTreeMap<LVar, LTyRef>, DebugRBTreeMap<LIdent, LVar>),
  //Env(DebugRBTreeSet<usize>, DebugRBTreeMap<usize, LTyRef>, DebugRBTreeSet<LVar>, DebugRBTreeMap<LVar, LTyRef>, DebugRBTreeMap<LIdent, LVar>),
  Env(IHTreapMap<usize, LTyRef>, IHTreapMap<LVar, LTyRef>, LCtxRef),
  STup(Vec<LTyRef>),
  HTup,
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
  //Cnj(Queue<TyConRef>),
  Eq_(TyexpRef, TyexpRef),
  //IsAApply(TyexpRef, Vec<(usize, LVar, LVarBinder, LVar)>, TyexpRef),
  IsAApply(TyexpRef, TyexpRef, Vec<(usize, LVar, LVarBinder, LVar, LTyvar)>),
  IsAReturn(TyexpRef, Vec<(usize, LVar)>, TyexpRef),
  IsACons(TyexpRef, TyexpRef, LVar, LVarBinder, TyexpRef, TyexpRef),
  IsAConcat(TyexpRef, TyexpRef, TyexpRef),
  Bot,
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
enum TyUnsat {
  AdjArity,
  EnvArity,
  EnvBinder,
  EnvKey,
  ExpectedEnv,
  ExpectedFun,
  FunArity,
  STupArity,
  Unknown,
}

#[derive(Default, Debug)]
struct TyWork {
  cons:     VecDeque<TyConRef>,
  unsat:    VecDeque<(TyConRef, TyUnsat)>,
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

#[derive(Clone, Default, Debug)]
pub struct LTyctxRef {
  //idx:  IHTreapMap<usize, LTyvar>,
  //idxi: IHTreapMap<LTyvar, usize>,
  var:  IHTreapMap<LVar, LTyvar>,
  vari: IHTreapMap<LTyvar, LVar>,
}

impl LTyctxRef {
  pub fn lookup_var(&self, var: &LVar) -> LTyvar {
    match self.var.get(var) {
      None => panic!(),
      Some(v) => v.clone(),
    }
  }

  fn bind_var(&self, var: &LVar, tenv: &mut TyEnv) -> LTyctxRef {
    let v = tenv.fresh_tvar();
    match tenv.anno.get(var) {
      None => {}
      Some(ty) => {
        tenv.texp.insert_mut(v.clone(), ty.clone());
      }
    }
    LTyctxRef{
      var:  self.var.insert(var.clone(), v.clone()),
      vari: self.vari.insert(v.clone(), var.clone()),
    }
  }

  fn bind_var_mut(&mut self, var: &LVar, tenv: &mut TyEnv) -> LTyvar {
    let v = tenv.fresh_tvar();
    match tenv.anno.get(var) {
      None => {}
      Some(ty) => {
        tenv.texp.insert_mut(v.clone(), ty.clone());
      }
    }
    self.var.insert_mut(var.clone(), v.clone());
    self.vari.insert_mut(v.clone(), var.clone());
    v
  }
}

#[derive(Debug)]
enum TyReduce {
  Exp(TyexpRef),
  Var(LTyvar),
}

#[derive(Clone, Default, Debug)]
struct TyEnv {
  // TODO
  vctr: u64,
  anno: IHTreapMap<LVar, TyexpRef>,
  tctx: IHTreapMap<LLabel, LTyctxRef>,
  exp:  IHTreapMap<LLabel, LTyvar>,
  expi: IHTreapMap<LTyvar, LLabel>,
  db:   IHTreapMap<LTyvar, LTyvar>,
  texp: IHTreapMap<LTyvar, TyexpRef>,
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

  fn unsafe_set_tctx<L: Borrow<LLabel>>(&mut self, loc: L, tctx: LTyctxRef) {
    let label = loc.borrow();
    self.tctx.insert_mut(label.clone(), tctx);
  }

  fn lookup_var<L: Borrow<LLabel>>(&self, loc: L, var: &LVar) -> LTyvar {
    let label = loc.borrow();
    match self.tctx.get(label) {
      None => panic!(),
      Some(tctx) => tctx.lookup_var(var),
    }
  }

  fn _lookup_exp<L: Borrow<LLabel>>(&mut self, loc: L) -> Option<LTyvar> {
    let label = loc.borrow();
    match self.exp.get(label) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  fn lookup_exp<L: Borrow<LLabel>>(&mut self, loc: L) -> LTyvar {
    let label = loc.borrow();
    match self.exp.get(label) {
      None => panic!(),
      Some(v) => v.clone(),
    }
  }

  fn lookup_exp_or_fresh<L: Borrow<LLabel>>(&mut self, loc: L) -> LTyvar {
    let label = loc.borrow();
    match self.exp.get(label) {
      None => {
        let v = self.fresh_tvar();
        self.exp.insert_mut(label.clone(), v.clone());
        self.expi.insert_mut(v.clone(), label.clone());
        v
      }
      Some(v) => v.clone(),
    }
  }

  fn annotate(&mut self, var: &LVar, ty: TyexpRef) {
    match self.anno.get(var) {
      None => {
        self.anno.insert_mut(var.clone(), ty);
      }
      Some(_) => panic!(),
    }
  }

  fn head(&mut self, query: LTyvar) -> LTyvar {
    if !self.db.contains_key(&query) {
      self.db.insert_mut(query.clone(), query.clone());
      return query;
    }
    let mut cursor = query;
    let mut next = self.db.get(&cursor).unwrap().clone();
    while cursor != next {
      let next2 = match self.db.get(&next) {
        None => next.clone(),
        Some(next2) => next2.clone(),
      };
      self.db.insert_mut(next.clone(), next2.clone());
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
    self.db.insert_mut(lw.clone(), rw.clone());
    match self.texp.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.texp.remove_mut(&lw);
        self.texp.insert_mut(rw.clone(), t);
      }
    }
  }

  fn unify_texp(&mut self, v: LTyvar, query: TyexpRef) {
    let w = self.head(v);
    self.texp.insert_mut(w, query);
  }

  fn reduce_tvar(&mut self, v: LTyvar) -> TyReduce {
    let w = self.head(v);
    match self.texp.get(&w) {
      None => TyReduce::Var(w),
      Some(query) => {
        let query = query.clone();
        let query = self.reduce_texp(query);
        self.texp.insert_mut(w, query.clone());
        TyReduce::Exp(query)
      }
    }
  }

  fn reduce_texp(&mut self, query: TyexpRef) -> TyexpRef {
    match &*query {
      // TODO: cases.
      &Tyexp::Var(ref v) => {
        match self.reduce_tvar(v.clone()) {
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
      &Tyexp::Env(ref idxs, ref vars, ref ctx) => {
        let mut idxs_ = IHTreapMap::default();
        let mut vars_ = IHTreapMap::default();
        for (&idx, t) in idxs.iter() {
          idxs_.insert_mut(idx, self.reduce_texp(t.clone()));
        }
        for (var, t) in vars.iter() {
          vars_.insert_mut(var.clone(), self.reduce_texp(t.clone()));
        }
        Tyexp::Env(idxs_, vars_, ctx.clone()).into()
      }
      &Tyexp::STup(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          elems_.push(self.reduce_texp(elem.clone()));
        }
        Tyexp::STup(elems_).into()
      }
      &Tyexp::HTup |
      &Tyexp::Bit |
      &Tyexp::Int |
      &Tyexp::Flp |
      &Tyexp::Unit => query,
      _ => unimplemented!(),
    }
  }

  fn mgu_var<L: Borrow<LLabel>>(&mut self, loc: L, var: &LVar) -> Option<(LTyvar, LTyvar, LTyRef)> {
    let v = self.lookup_var(loc, var);
    match self.mgu_tvar(v.clone()) {
      None => None,
      Some((w, e)) => Some((v, w, e)),
    }
  }

  fn mgu_exp<L: Borrow<LLabel>>(&mut self, loc: L) -> Option<(LTyvar, LTyvar, LTyRef)> {
    match self._lookup_exp(loc) {
      None => panic!(),
      Some(v) => match self.mgu_tvar(v.clone()) {
        None => None,
        Some((w, e)) => Some((v, w, e)),
      }
    }
  }

  fn mgu_tvar(&mut self, v: LTyvar) -> Option<(LTyvar, LTyRef)> {
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
      &Tyexp::Env(ref idxs, ref vars, ref ctx) => {
        let mut idxs_ = IHTreapMap::default();
        let mut vars_ = IHTreapMap::default();
        for (&idx, t) in idxs.iter() {
          idxs_.insert_mut(idx, self._mgu_reduced(t.clone())?);
        }
        for (var, t) in vars.iter() {
          vars_.insert_mut(var.clone(), self._mgu_reduced(t.clone())?);
        }
        Ok(LTy::Env(idxs_.into(), vars_.into(), ctx.clone().into()).into())
      }
      &Tyexp::STup(ref elems) => {
        let mut elems_ = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          elems_.push(self._mgu_reduced(elem.clone())?);
        }
        Ok(LTy::STup(elems_).into())
      }
      &Tyexp::Bit => Ok(LTy::Bit.into()),
      &Tyexp::Int => Ok(LTy::Int.into()),
      &Tyexp::Flp => Ok(LTy::Flp.into()),
      &Tyexp::Unit => Ok(LTy::Unit.into()),
      _ => Err(()),
    }
  }
}

/*#[derive(Clone, Default)]
struct IncTyInfMachine {
}*/

impl LBuilder {
  fn _gen_pat(&mut self, pat: LPatRef, tctx: &mut LTyctxRef, tenv: &mut TyEnv, work: &mut TyWork) -> TyexpRef {
    // TODO
    match &*pat {
      &LPat::STuple(ref elems) => {
        let mut elem_tys = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          elem_tys.push(self._gen_pat(elem.clone(), tctx, tenv, work));
        }
        Tyexp::STup(elem_tys).into()
      }
      &LPat::BitLit(_) => {
        Tyexp::Bit.into()
      }
      &LPat::IntLit(_) => {
        Tyexp::Int.into()
      }
      &LPat::Var(ref var) => {
        tctx.bind_var_mut(var, tenv).into()
      }
      _ => unimplemented!(),
    }
  }

  fn _gen_exp(&mut self, exp: LExprCell, tctx: LTyctxRef, tenv: &mut TyEnv, work: &mut TyWork) {
    /*let ety = match tenv._lookup_exp(&exp) {
      None => tenv.lookup_exp_or_fresh(&exp),
      Some(_) => return,
    };*/
    tenv.unsafe_set_tctx(&exp, tctx.clone());
    let ety = tenv.lookup_exp_or_fresh(&exp);
    match &exp.term() {
      &LTerm::Top => {
        let con = TyCon::Eq_(ety.into(), Tyexp::Unit.into()).into();
        work.cons.push_front(con);
      }
      &LTerm::Break(ref inner) => {
        self._gen_exp(exp.lookup(inner), tctx, tenv, work);
        let con = TyCon::Eq_(ety.into(), tenv.lookup_exp(inner).into()).into();
        work.cons.push_front(con);
      }
      &LTerm::Return(ref inner) => {
        self._gen_exp(exp.lookup(inner), tctx, tenv, work);
        let con = TyCon::Eq_(ety.into(), tenv.lookup_exp(inner).into()).into();
        work.cons.push_front(con);
      }
      &LTerm::Apply(ref head, ref args) => {
        self._gen_exp(exp.lookup(head), tctx.clone(), tenv, work);
        let mut arg_tys = Vec::with_capacity(args.len());
        for a in args.iter() {
          self._gen_exp(exp.lookup(a), tctx.clone(), tenv, work);
          arg_tys.push(tenv.lookup_exp(a).into());
        }
        let app_con = TyCon::Eq_(tenv.lookup_exp(head).into(), Tyexp::Fun(arg_tys, ety.into()).into()).into();
        work.cons.push_front(app_con);
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut param_tys = Vec::with_capacity(params.len());
        let mut body_tctx = tctx;
        for p in params.iter() {
          let p_v = body_tctx.bind_var_mut(p, tenv);
          param_tys.push(p_v.into());
        }
        self._gen_exp(exp.lookup(body), body_tctx, tenv, work);
        let lam_con = TyCon::Eq_(ety.into(), Tyexp::Fun(param_tys, tenv.lookup_exp(body).into()).into()).into();
        work.cons.push_front(lam_con);
      }
      &LTerm::Export => {
        // TODO
        /*let ctx = exp.ctx();
        let idxs: RBTreeMap<usize, LTyvar> = Default::default();
        let mut keys: RBTreeMap<LVar, LTyvar> = Default::default();
        let mut idents: RBTreeMap<LIdent, LVar> = Default::default();
        for (binder, var) in ctx.bind_to_var.iter() {
          keys.insert_mut(var.clone(), tenv.lookup_var(var));
          match binder {
            &LVarBinder::Ident(ref ident) => {
              idents.insert_mut(ident.clone(), var.clone());
            }
            &LVarBinder::Anon => {}
          }
        }
        let con = TyConRef::new(TyCon::Eq_(ety.into(), Tyexp::Env(idxs, keys, idents).into()));
        work.cons.push_front(con);*/
        unimplemented!();
      }
      &LTerm::Import(ref _free, ref _env, ref _body) => {
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }
      &LTerm::EnvVars(ref kvs) => {
        // TODO
        if kvs.is_empty() {
          let idxs = Default::default();
          let keys = Default::default();
          let idents = Default::default();
          let con = TyCon::Eq_(ety.into(), Tyexp::Env(idxs, keys, idents).into()).into();
          work.cons.push_front(con);
        } else {
          unimplemented!();
        }
      }
      &LTerm::AApply(ref target, ref args) => {
        println!("TRACE: _gen_exp: generating IsAApply constraint");
        self._gen_exp(exp.lookup(target), tctx, tenv, work);
        let args_ = args.iter().map(|&(idx, ref key, ref key_ident, ref key_adj)| {
          let key_adj_ty = tenv.lookup_var(&exp, key_adj);
          (idx, key.clone(), key_ident.clone(), key_adj.clone(), key_adj_ty)
        }).collect();
        let con = TyCon::IsAApply(ety.into(), tenv.lookup_exp(target).into(), args_).into();
        work.cons.push_front(con);
      }
      &LTerm::AReturn(/*ref mask,*/ ref params, ref target) => {
        // TODO
        println!("TRACE: _gen_exp: generating IsAReturn constraint");
        self._gen_exp(exp.lookup(target), tctx, tenv, work);
        let con = TyCon::IsAReturn(ety.into(), params.clone(), tenv.lookup_exp(target).into()).into();
        work.cons.push_front(con);
      }
      &LTerm::ACons(/*ref mask,*/ ref key, ref ident, ref value, ref target) => {
        println!("TRACE: _gen_exp: generating IsACons constraint");
        let key_v = tctx.lookup_var(key);
        self._gen_exp(exp.lookup(value), tctx.clone(), tenv, work);
        self._gen_exp(exp.lookup(target), tctx.clone(), tenv, work);
        let key_con = TyCon::Eq_(key_v.clone().into(), tenv.lookup_exp(value).into()).into();
        let con = TyCon::IsACons(ety.into(), key_v.into(), key.clone(), ident.clone(), tenv.lookup_exp(value).into(), tenv.lookup_exp(target).into()).into();
        work.cons.push_front(con);
        work.cons.push_front(key_con);
      }
      &LTerm::AConcat(ref lhs, ref rhs) => {
        // TODO
      }
      &LTerm::PtlD(ref target) => {
        self._gen_exp(exp.lookup(target), tctx, tenv, work);
        work.a_defer.push_front(exp.label());
      }
      &LTerm::AdjD(ref _target) => {
        unimplemented!();
      }
      &LTerm::TngD(ref _target) => {
        unimplemented!();
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let mut rest_tctx = tctx.clone();
        let name_v = rest_tctx.bind_var_mut(name, tenv);
        self._gen_exp(exp.lookup(body), tctx, tenv, work);
        self._gen_exp(exp.lookup(rest), rest_tctx, tenv, work);
        let let_con1 = TyCon::Eq_(name_v.into(), tenv.lookup_exp(body).into()).into();
        let let_con2 = TyCon::Eq_(ety.into(), tenv.lookup_exp(rest).into()).into();
        work.cons.push_front(let_con2);
        work.cons.push_front(let_con1);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let mut fixbody_tctx = tctx;
        let fixname_v = fixbody_tctx.bind_var_mut(fixname, tenv);
        self._gen_exp(exp.lookup(fixbody), fixbody_tctx, tenv, work);
        let fixname_con = TyCon::Eq_(fixname_v.into(), tenv.lookup_exp(fixbody).into()).into();
        let fix_con = TyCon::Eq_(ety.into(), tenv.lookup_exp(fixbody).into()).into();
        work.cons.push_front(fix_con);
        work.cons.push_front(fixname_con);
      }
      &LTerm::SFix(ref fixnames, ref fixbody) => {
        let mut fixname_tys = Vec::with_capacity(fixnames.len());
        let mut fixbody_tctx = tctx;
        for fixname in fixnames.iter() {
          let fixname_v = fixbody_tctx.bind_var_mut(fixname, tenv);
          fixname_tys.push(fixname_v.into());
        }
        self._gen_exp(exp.lookup(fixbody), fixbody_tctx, tenv, work);
        let fixnames_con = TyCon::Eq_(tenv.lookup_exp(fixbody).into(), Tyexp::STup(fixname_tys).into()).into();
        let fix_con = TyCon::Eq_(ety.into(), tenv.lookup_exp(fixbody).into()).into();
        work.cons.push_front(fix_con);
        work.cons.push_front(fixnames_con);
      }
      &LTerm::Match(ref query, ref pat_arms) => {
        self._gen_exp(exp.lookup(query), tctx.clone(), tenv, work);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut pat_arm_tctx = tctx.clone();
          let pat_ty = self._gen_pat(pat.clone(), &mut pat_arm_tctx, tenv, work);
          self._gen_exp(exp.lookup(arm), pat_arm_tctx, tenv, work);
          let pat_con = TyCon::Eq_(tenv.lookup_exp(query).into(), pat_ty).into();
          let arm_con = TyCon::Eq_(ety.clone().into(), tenv.lookup_exp(arm).into()).into();
          work.cons.push_front(arm_con);
          work.cons.push_front(pat_con);
        }
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        self._gen_exp(exp.lookup(query), tctx.clone(), tenv, work);
        for &(ref pat, ref arm) in pat_arms.iter() {
          let mut pat_arm_tctx = tctx.clone();
          let pat_ty = self._gen_pat(pat.clone(), &mut pat_arm_tctx, tenv, work);
          self._gen_exp(exp.lookup(arm), pat_arm_tctx, tenv, work);
          let pat_con = TyCon::Eq_(tenv.lookup_exp(query).into(), pat_ty).into();
          work.cons.push_front(pat_con);
        }
      }
      &LTerm::STuple(ref elems) => {
        let mut elem_tys = Vec::with_capacity(elems.len());
        for elem in elems.iter() {
          self._gen_exp(exp.lookup(elem), tctx.clone(), tenv, work);
          elem_tys.push(tenv.lookup_exp(elem).into());
        }
        let con = TyCon::Eq_(ety.into(), Tyexp::STup(elem_tys).into()).into();
        work.cons.push_front(con);
      }
      &LTerm::BitLit(_) => {
        let con = TyCon::Eq_(ety.into(), Tyexp::Bit.into()).into();
        work.cons.push_front(con);
      }
      &LTerm::IntLit(_) => {
        let con = TyCon::Eq_(ety.into(), Tyexp::Int.into()).into();
        work.cons.push_front(con);
      }
      &LTerm::FlpLit(_) => {
        let con = TyCon::Eq_(ety.into(), Tyexp::Flp.into()).into();
        work.cons.push_front(con);
      }
      &LTerm::Lookup(ref name) => {
        let name_v = tctx.lookup_var(name);
        let con = TyCon::Eq_(ety.into(), name_v.into()).into();
        work.cons.push_front(con);
      }
      // FIXME: embed the key type into the term.
      &LTerm::ProjectVar(ref target, ref key) => {
        let key_v = tctx.lookup_var(key);
        self._gen_exp(exp.lookup(target), tctx, tenv, work);
        let con = TyCon::Eq_(ety.into(), key_v.into()).into();
        work.cons.push_front(con);
      }
      &LTerm::ProjectIdent(ref target, _) => {
        self._gen_exp(exp.lookup(target), tctx, tenv, work);
        work.a_defer.push_front(exp.label());
      }
      &LTerm::MX(_) => {
        // TODO
      }
      //_ => unimplemented!(),
      t => {
        panic!("TRACE: _gen_exp: unhandled term: {:?}", t);
      }
    }
  }

  fn gen(&mut self, tree: &LTreeCell, tenv: &mut TyEnv, work: &mut TyWork) {
    //work._reset();
    let tctx = LTyctxRef::default();
    self._gen_exp(tree.root(), tctx, tenv, work);
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

  /*fn gen_inc_adj(&mut self, tree: &LTreeCell, a_work: &mut AdjWork, tenv: &mut TyEnv, work: &mut TyWork) {
    // TODO
    //work._reset();
    let root = tree.root();
    for e in a_work.appended.drain(..) {
      self._gen_exp(root.lookup_exp(&e), tenv, work);
    }
  }*/

  fn _solve_eq_tvar(&mut self, lv: LTyvar, rv: LTyvar, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    let lquery = tenv.reduce_tvar(lv.clone());
    let rquery = tenv.reduce_tvar(rv.clone());
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

  fn _solve_eq_texp(&mut self, v: LTyvar, query: TyexpRef, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    let lquery = tenv.reduce_tvar(v.clone());
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
}

impl LBuilder {
  fn _solve(&mut self, con: TyConRef, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    // TODO
  }

  fn solve(&mut self, root: LExprCell, tenv: &mut TyEnv, work: &mut TyWork) {
    let con = match work.cons.pop_front() {
      None => {
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
            self._solve_eq_tvar(lv.clone(), rv.clone(), root, tenv, work)
          }
          (&Tyexp::Var(ref lv), _) => {
            self._solve_eq_texp(lv.clone(), rquery.clone(), root, tenv, work)
          }
          (_, &Tyexp::Var(ref rv)) => {
            self._solve_eq_texp(rv.clone(), lquery.clone(), root, tenv, work)
          }
          (&Tyexp::Fun(ref l_dom, ref l_ret), &Tyexp::Fun(ref r_dom, ref r_ret)) => {
            if l_dom.len() != r_dom.len() {
              println!("WARNING: solve: Eq_: fun arity mismatch");
              work.unsat.push_back((con.clone(), TyUnsat::FunArity));
              work.cons.push_back(TyCon::Bot.into());
              return self.solve(root, tenv, work);
            }
            for (lty, rty) in l_dom.iter().zip(r_dom.iter()) {
              work.cons.push_back(TyConRef::new(TyCon::Eq_(lty.clone(), rty.clone())));
            }
            work.cons.push_back(TyConRef::new(TyCon::Eq_(l_ret.clone(), r_ret.clone())));
            self.solve(root, tenv, work)
          }
          (&Tyexp::Env(ref l_idxs, ref l_vars, ref l_ctx), &Tyexp::Env(ref r_idxs, ref r_vars, ref r_ctx)) => {
            if l_idxs.len() != r_idxs.len() || l_vars.len() != r_vars.len() {
              println!("WARNING: solve: Eq_: env arity mismatch");
              work.unsat.push_back((con.clone(), TyUnsat::EnvArity));
              work.cons.push_back(TyCon::Bot.into());
              return self.solve(root, tenv, work);
            }
            for ((l_idx, l_ty), (r_idx, r_ty)) in l_idxs.iter().zip(r_idxs.iter()) {
              if l_idx != r_idx {
                println!("WARNING: solve: Eq_: env index key mismatch");
                work.unsat.push_back((con.clone(), TyUnsat::EnvKey));
                work.cons.push_back(TyCon::Bot.into());
                return self.solve(root, tenv, work);
              }
              work.cons.push_back(TyConRef::new(TyCon::Eq_(l_ty.clone(), r_ty.clone())));
            }
            for ((l_var, l_ty), (r_var, r_ty)) in l_vars.iter().zip(r_vars.iter()) {
              if l_var != r_var {
                println!("WARNING: solve: Eq_: env var key mismatch");
                work.unsat.push_back((con.clone(), TyUnsat::EnvKey));
                work.cons.push_back(TyCon::Bot.into());
                return self.solve(root, tenv, work);
              }
              work.cons.push_back(TyConRef::new(TyCon::Eq_(l_ty.clone(), r_ty.clone())));
              /*work.cons.push_back(TyConRef::new(TyCon::Eq_(tenv.lookup_var(l_var).into(), l_ty.clone())));
              work.cons.push_back(TyConRef::new(TyCon::Eq_(tenv.lookup_var(l_var).into(), r_ty.clone())));*/
            }
            for ((l_id, l_var), (r_id, r_var)) in l_ctx.id_to_var.iter().zip(r_ctx.id_to_var.iter()) {
              if l_id != r_id || l_var != r_var {
                println!("WARNING: solve: Eq_: env var binding mismatch");
                work.unsat.push_back((con.clone(), TyUnsat::EnvBinder));
                work.cons.push_back(TyCon::Bot.into());
                return self.solve(root, tenv, work);
              }
            }
            self.solve(root, tenv, work)
          }
          (&Tyexp::STup(ref l_elems), &Tyexp::STup(ref r_elems)) => {
            if l_elems.len() != r_elems.len() {
              println!("WARNING: solve: Eq_: stup arity mismatch");
              work.unsat.push_back((con.clone(), TyUnsat::STupArity));
              work.cons.push_back(TyCon::Bot.into());
              return self.solve(root, tenv, work);
            }
            for (le, re) in l_elems.iter().zip(r_elems.iter()) {
              work.cons.push_back(TyConRef::new(TyCon::Eq_(le.clone(), re.clone())));
            }
            self.solve(root, tenv, work)
          }
          (&Tyexp::HTup, &Tyexp::HTup) |
          (&Tyexp::Bit, &Tyexp::Bit) |
          (&Tyexp::Int, &Tyexp::Int) |
          (&Tyexp::Flp, &Tyexp::Flp) |
          (&Tyexp::Unit, &Tyexp::Unit) => {
            self.solve(root, tenv, work)
          }
          (lhs, rhs) => {
            println!("WARNING: solve: Eq_: type mismatch or unimpl: {:?} vs {:?}", lhs, rhs);
            work.unsat.push_back((con, TyUnsat::Unknown));
            work.cons.push_back(TyCon::Bot.into());
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::IsAApply(ref query, ref target, ref args) => {
        match &*tenv.reduce_texp(target.clone()) {
          &Tyexp::Var(_) => {
            work.cons.push_back(con);
            self.solve(root, tenv, work)
          }
          &Tyexp::Env(ref tg_idxs, ref tg_keys, ref tg_ctx) => {
            println!("TRACE: solve: IsAApply: instantiating a new env tyexp");
            let mut adj_doms = Vec::with_capacity(args.len());
            let mut adj_rets = Vec::with_capacity(args.len());
            for &(idx, _, _, ref key_adj, ref key_adj_ty) in args.iter() {
              match tg_idxs.get(&idx) {
                None => {}
                Some(_) => {
                  /*let key_adj_ty = tenv.lookup_var(key_adj);*/
                  match &*tenv.reduce_texp(key_adj_ty.clone().into()) {
                    &Tyexp::Var(_) => {
                      work.cons.push_back(con);
                      return self.solve(root, tenv, work);
                    }
                    &Tyexp::Fun(ref v_dom, ref v_ret) => {
                      match &**v_ret {
                        &Tyexp::Var(_) => {
                          work.cons.push_back(con);
                          return self.solve(root, tenv, work);
                        }
                        &Tyexp::Env(..) => {
                          adj_doms.push(v_dom.clone());
                          adj_rets.push(v_ret.clone());
                        }
                        _ => {
                          println!("WARNING: solve: IsAApply: non-env adj ret type");
                          work.unsat.push_back((con, TyUnsat::ExpectedEnv));
                          work.cons.push_back(TyCon::Bot.into());
                          return self.solve(root, tenv, work);
                        }
                      }
                    }
                    _ => {
                      println!("WARNING: solve: IsAApply: non-fun adj type");
                      work.unsat.push_back((con, TyUnsat::ExpectedFun));
                      work.cons.push_back(TyCon::Bot.into());
                      return self.solve(root, tenv, work);
                    }
                  }
                }
              }
            }
            // TODO: fixup idents.
            let mut app_idxs = tg_idxs.clone();
            let mut app_keys = tg_keys.clone();
            let mut app_ctx = tg_ctx.clone();
            for (adj_idx, &(idx, _, ref ident, _, _)) in args.iter().enumerate().rev() {
              match app_idxs.get(&idx) {
                //None => unreachable!(),
                None => {}
                Some(val_ty) => {
                  let val_ty = val_ty.clone();
                  if adj_doms[adj_idx].len() != 1 {
                    println!("WARNING: solve: IsAApply: non-unity adj arity");
                    work.unsat.push_back((con, TyUnsat::AdjArity));
                    work.cons.push_back(TyCon::Bot.into());
                    return self.solve(root, tenv, work);
                  }
                  let adj_dom_con = TyConRef::new(TyCon::Eq_(val_ty.clone(), adj_doms[adj_idx][0].clone()));
                  work.cons.push_back(adj_dom_con);
                  match &*adj_rets[adj_idx] {
                    &Tyexp::Env(_, ref adj_keys, _) => {
                      for (adj_key, adj_val_ty) in adj_keys.iter() {
                        let adj_val_ty = adj_val_ty.clone();
                        match app_keys.get(adj_key) {
                          None => {
                            app_keys.insert_mut(adj_key.clone(), adj_val_ty);
                          }
                          Some(val_ty2) => {
                            let val_ty2 = val_ty2.clone();
                            let val_con = TyConRef::new(TyCon::Eq_(adj_val_ty, val_ty2));
                            work.cons.push_back(val_con);
                          }
                        }
                      }
                    }
                    _ => unreachable!(),
                  }
                }
              }
            }
            for &(idx, ref key, ref ident, _, _) in args.iter() {
              match app_idxs.get(&idx) {
                None => {}
                Some(val_ty) => {
                  let val_ty = val_ty.clone();
                  app_idxs.remove_mut(&idx);
                  match app_keys.get(key) {
                    None => {
                      app_keys.insert_mut(key.clone(), val_ty);
                    }
                    Some(val_ty2) => {
                      let val_ty2 = val_ty2.clone();
                      let val_con = TyConRef::new(TyCon::Eq_(val_ty, val_ty2));
                      work.cons.push_back(val_con);
                    }
                  }
                  if let &LVarBinder::Ident(ref ident) = ident {
                    app_ctx.bind_ident_mut(ident.clone(), key.clone());
                  }
                }
              }
            }
            let new_con = TyConRef::new(TyCon::Eq_(query.clone(), Tyexp::Env(app_idxs, app_keys, app_ctx).into()));
            work.cons.push_back(new_con);
            self.solve(root, tenv, work)
          }
          _ => {
            println!("WARNING: solve: IsAApply: unsat!");
            work.unsat.push_back((con, TyUnsat::ExpectedEnv));
            work.cons.push_back(TyCon::Bot.into());
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::IsAReturn(ref query, ref params, ref target) => {
        match &*tenv.reduce_texp(target.clone()) {
          &Tyexp::Var(_) => {
            work.cons.push_back(con);
            self.solve(root, tenv, work)
          }
          &Tyexp::Env(ref tg_idxs, ref tg_vars, ref tg_ctx) => {
            println!("TRACE: solve: IsAReturn: instantiating a new env tyexp");
            if !tg_idxs.is_empty() {
              println!("WARNING: solve: IsAReturn: nonempty target index set");
              work.unsat.push_back((con.clone(), TyUnsat::EnvArity));
              work.cons.push_back(TyCon::Bot.into());
              return self.solve(root, tenv, work);
            }
            // TODO: fixup idents.
            let mut ret_idxs = IHTreapMap::default();
            let mut ret_vars = tg_vars.clone();
            let mut ret_ctx = tg_ctx.clone();
            for &(idx, ref var) in params.iter() {
              match ret_vars.get(var) {
                None => {}
                Some(val_ty) => {
                  let val_ty = val_ty.clone();
                  match self.lookup_var(var) {
                    LVarBinder::Ident(var_ident) => {
                      match ret_ctx._lookup_ident(&var_ident) {
                        None => {}
                        Some(ref var2) => {
                          if var == var2 {
                            ret_ctx.unbind_ident_mut(&var_ident);
                          }
                        }
                      }
                    }
                    _ => {}
                  }
                  ret_vars.remove_mut(var);
                  ret_idxs.insert_mut(idx, val_ty);
                }
              }
            }
            let new_con = TyConRef::new(TyCon::Eq_(query.clone(), Tyexp::Env(ret_idxs, ret_vars, ret_ctx).into()));
            work.cons.push_back(new_con);
            self.solve(root, tenv, work)
          }
          _ => {
            println!("WARNING: solve: IsAReturn: unsat!");
            work.unsat.push_back((con, TyUnsat::ExpectedEnv));
            work.cons.push_back(TyCon::Bot.into());
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::IsACons(/*ref mask,*/ ref query, ref key, ref key_var, ref key_ident, ref value, ref target) => {
        match &*tenv.reduce_texp(target.clone()) {
          &Tyexp::Var(_) => {
            work.cons.push_back(con);
            self.solve(root, tenv, work)
          }
          &Tyexp::Env(ref tg_idxs, ref tg_keys, ref tg_ctx) => {
            println!("TRACE: solve: IsACons: instantiating a new env tyexp");
            // TODO
            let cons_keys = tg_keys.insert(key_var.clone(), value.clone().into());
            let cons_ctx = match key_ident {
              LVarBinder::Ident(key_ident) => tg_ctx.bind_ident(key_ident.clone(), key_var.clone()),
              LVarBinder::Anon => tg_ctx.clone(),
            };
            let new_con = TyConRef::new(TyCon::Eq_(query.clone(), Tyexp::Env(tg_idxs.clone(), cons_keys, cons_ctx).into()));
            work.cons.push_back(new_con);
            self.solve(root, tenv, work)
          }
          _ => {
            println!("WARNING: solve: IsACons: unsat!");
            work.unsat.push_back((con, TyUnsat::ExpectedEnv));
            work.cons.push_back(TyCon::Bot.into());
            self.solve(root, tenv, work)
          }
        }
      }
      &TyCon::IsAConcat(ref query, ref lhs, ref rhs) => {
        // TODO
        unimplemented!();
      }
      &TyCon::Bot => {
        return;
      }
      _ => unimplemented!(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct LCtxRef {
  // TODO
  //version:      usize,
  //tree_version: usize,
  id_to_var:    IHTreapMap<LIdent, LVar>,
  //var_to_depth: IHTreapMap<LVar, usize>,
  //var_stack:    Stack<LVar>,
}

impl Default for LCtxRef {
  fn default() -> LCtxRef {
    LCtxRef::empty()
  }
}

impl LCtxRef {
  pub fn empty_top_level() -> LCtxRef {
    LCtxRef::empty()
  }

  pub fn empty() -> LCtxRef {
    LCtxRef{
      //version:      0,
      id_to_var:    Default::default(),
      //var_to_depth: Default::default(),
      //var_stack:    Stack::default(),
    }
  }

  pub fn _lookup_ident<Id: Borrow<LIdent>>(&self, ident: Id) -> Option<LVar> {
    match self.id_to_var.get(ident.borrow()) {
      None => None,
      Some(v) => Some(v.clone()),
    }
  }

  pub fn lookup_ident<Id: Borrow<LIdent>>(&self, ident: Id) -> LVar {
    match self.id_to_var.get(ident.borrow()) {
      None => panic!(),
      Some(v) => v.clone(),
    }
  }

  pub fn bind_ident<Id: Into<LIdent>>(&self, ident: Id, var: LVar) -> LCtxRef {
    LCtxRef{
      id_to_var:    self.id_to_var.insert(ident.into(), var),
    }
  }

  pub fn bind_ident_mut<Id: Into<LIdent>>(&mut self, ident: Id, var: LVar) {
    self.id_to_var.insert_mut(ident.into(), var);
    //self.var_to_depth.insert_mut(var.clone(), self.var_stack.size());
    //self.var_stack.push_mut(var);
  }

  pub fn unbind_ident_mut<Id: Borrow<LIdent>>(&mut self, ident: Id) {
    self.id_to_var.remove_mut(ident.borrow());
  }
}

#[derive(Clone, Default, Debug)]
pub struct LFreectxRef {
  freevars: IHTreapSet<LVar>,
}

impl LFreectxRef {
  fn union(self, other: LFreectxRef) -> LFreectxRef {
    LFreectxRef{
      freevars: self.freevars.union(&other.freevars),
    }
  }

  fn diff(self, other: LFreectxRef) -> LFreectxRef {
    LFreectxRef{
      freevars: self.freevars.difference(&other.freevars),
    }
  }
}

#[derive(Clone, Default, Debug)]
pub struct LFreeAdjCtxRef {
  adj_var:  IHTreapMap<LVar, LVar>,
}

#[derive(Clone, Default, Debug)]
struct Env {
  top_ctx:  Option<LCtxRef>,
  ctx:      IHTreapMap<LLabel, LCtxRef>,
  free_ctx: IHTreapMap<LLabel, LFreectxRef>,
  //free_adj: IHTreapMap<LLabel, LFreeAdjCtxRef>,
}

impl Env {
  fn unsafe_set_ctx<L: Borrow<LLabel>>(&mut self, loc: L, new_ctx: LCtxRef) {
    let label = loc.borrow();
    self.ctx.insert_mut(label.clone(), new_ctx);
  }

  fn unsafe_set_freectx<L: Borrow<LLabel>>(&mut self, loc: L, new_ctx: LFreectxRef) {
    let label = loc.borrow();
    self.free_ctx.insert_mut(label.clone(), new_ctx);
  }

  pub fn _ctx<L: Borrow<LLabel>>(&self, loc: L) -> Option<LCtxRef> {
    match self.ctx.get(loc.borrow()) {
      None => None,
      Some(ctx) => Some(ctx.clone())
    }
  }

  pub fn ctx<L: Borrow<LLabel>>(&self, loc: L) -> LCtxRef {
    match self.ctx.get(loc.borrow()) {
      None => panic!("bug"),
      Some(ctx) => ctx.clone()
    }
  }

  pub fn _freectx<L: Borrow<LLabel>>(&self, loc: L) -> Option<LFreectxRef> {
    match self.free_ctx.get(loc.borrow()) {
      None => None,
      Some(ctx) => Some(ctx.clone())
    }
  }

  pub fn freectx<L: Borrow<LLabel>>(&self, loc: L) -> LFreectxRef {
    match self.free_ctx.get(loc.borrow()) {
      None => panic!("bug"),
      Some(ctx) => ctx.clone()
    }
  }
}

/*#[derive(Debug)]
pub enum LDelta {
  Append(LLoc),
  AppendM(LMLoc),
  Rewrite(LLoc),
}*/

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
  //history:  Vec<(usize, LDelta)>,
  mindex:   HashMap<LMLabel, usize>,
  index:    HashMap<LLabel, usize>,
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
    RefCell::borrow(&view.data).clone()
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
  pub fn empty(builder: &mut LBuilder) -> LTreeCell {
    let label = builder.fresh_label();
    let view = LTreeView{
      root:     LLoc::new(label.clone(), 0),
      epoch:    0,
      version:  0,
    };
    let mut tree = LTree::default();
    tree.exps.push(LExpr{
      version:  0,
      label,
      term:     LTerm::Bot
    });
    LTreeCell{
      view,
      data: Rc::new(RefCell::new(tree)),
    }
  }

  pub fn root(&self) -> LExprCell {
    let data = RefCell::borrow(&self.data);
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
    /*let mut exp = self.root();
    loop {
      match exp.term() {
        LTerm::Top => {
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
    Some(exp.ctx())*/
    None
  }

  fn final_tctx(&self, ctx: &LCtxRef, tenv: &mut TyEnv) -> Option<LTyctxRef> {
    // FIXME
    /*let tree = self.data.borrow();
    let mut tctx = LTyctxRef::default();
    for var in ctx.var_stack.iter() {
      let v = match tenv._lookup_var(var) {
        None => {
          //println!("DEBUG: resolve_ctx: no tvar");
          return None;
        }
        Some(v) => v,
      };
      match tenv.mgu_tvar(v.clone()) {
        None => {
          //println!("DEBUG: resolve_ctx: no mgu");
          return None;
        }
        Some((w, ty)) => {
          tctx.var_to_ty.insert_mut(var.clone(), (v, w, ty));
        }
      }
    }
    Some(tctx)*/
    None
  }
}

#[derive(Clone)]
pub struct LMExprCell {
  pub view:     LTreeViewCell,
  pub tree:     LTreeCell,
  pub pos:      usize,
  pub label:    LMLabel,
}

impl LMExprCell {
  pub fn loc(&self) -> LMLoc {
    LMLoc{
      label:    self.label.clone(),
      pos:      self.pos,
    }
  }

  pub fn term(&self) -> LMTerm {
    let tree = RefCell::borrow(&self.tree.data);
    let mexp = tree.mexps[self.pos].clone();
    assert_eq!(self.label, mexp.label);
    mexp.term
  }
}

#[derive(Clone)]
pub struct LExprCell {
  pub view:     LTreeViewCell,
  pub tree:     LTreeCell,
  pub pos:      usize,
  pub label:    LLabel,
}

impl<'a> Borrow<LLabel> for &'a LExprCell {
  fn borrow(&self) -> &LLabel {
    &self.label
  }
}

impl Borrow<LLabel> for LExprCell {
  fn borrow(&self) -> &LLabel {
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
    let tree = RefCell::borrow(&self.tree.data);
    let exp = tree.exps[self.pos].clone();
    assert_eq!(self.label, exp.label);
    exp.term
  }

  fn unsafe_set_self_root(&self) {
    let mut view = self.view.data.borrow_mut();
    view.root = LLoc::new(self.label.clone(), self.pos);
    view.epoch += 1;
  }

  pub fn jump<L: Borrow<LLoc>>(&self, loc: L) -> LExprCell {
    self.lookup(loc.borrow())
  }

  pub fn lookup(&self, loc: &LLoc) -> LExprCell {
    let tree = RefCell::borrow(&self.tree.data);
    assert_eq!(loc.label, tree.exps[loc.pos].label);
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      loc.pos,
      label:    loc.label.clone(),
    }
  }

  pub fn lookup_exp<L: Borrow<LLabel>>(&self, loc: L) -> LExprCell {
    let tree = RefCell::borrow(&self.tree.data);
    let label = loc.borrow();
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
      tree.exps.push(LExpr{
        version:  view.version,
        label:    new_label.clone(),
        term:     new_term,
      });
      /*tree.history.push((view.version, LDelta::Append(LLoc::new(new_label.clone(), new_pos))));
      // FIXME: adj resolution temporarily breaks this invariant.
      assert_eq!(view.version, tree.history.len());*/
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
    /*tree.history.push((view.version, LDelta::Rewrite(LLoc::new(self.label.clone(), self.pos))));
    assert_eq!(view.version, tree.history.len());*/
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

  pub fn mjump<L: Borrow<LMLoc>>(&self, loc: L) -> LMExprCell {
    self.mlookup(loc.borrow())
  }

  pub fn mlookup(&self, loc: &LMLoc) -> LMExprCell {
    let tree = RefCell::borrow(&self.tree.data);
    assert_eq!(loc.label, tree.mexps[loc.pos].label);
    LMExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      loc.pos,
      label:    loc.label.clone(),
    }
  }

  pub fn mappend(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LMTerm) -> LMExprCell {
    let new_label = builder.fresh_mlabel();
    self._mappend(new_label, builder, mk_term)
  }

  pub fn _mappend(&self, new_label: LMLabel, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LMTerm) -> LMExprCell {
    let new_term = (mk_term)(builder);
    let new_pos = {
      let mut view = self.view.data.borrow_mut();
      let mut tree = self.tree.data.borrow_mut();
      let root = view.root.clone();
      let new_pos = tree.mexps.len();
      view.version += 1;
      assert!(view.version != 0);
      tree.mexps.push(LMExpr{
        version:  view.version,
        label:    new_label.clone(),
        term:     new_term,
      });
      /*tree.history.push((view.version, LDelta::Append(LLoc::new(new_label.clone(), new_pos))));
      assert_eq!(view.version, tree.history.len());*/
      tree.mindex.insert(new_label.clone(), new_pos);
      new_pos
    };
    LMExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      new_pos,
      label:    new_label,
    }
  }
}

pub type LETerm = LTerm<usize, usize>;

pub type LCodeRef = Rc<LCode>;

pub struct LCode {
  pub mterms:   Vec<LMTerm>,
  pub terms:    Vec<LETerm>,
}

#[derive(Clone)]
pub struct LMTermRef {
  // FIXME
  pub code:     LCodeRef,
  pub pos:      usize,
  //pub label:    LLabel,
  //pub term:     LTerm,
}

#[derive(Clone)]
pub struct LTermRef {
  // FIXME
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
      &LPat::BitLit(x) => {
        match x {
          true  => write!(&mut buffer, "top")?,
          false => write!(&mut buffer, "bot")?,
        }
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LPat::IntLit(x) => {
        write!(&mut buffer, "{}n", x)?;
        writer.write_all(&buffer.into_inner())?;
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
      &LTerm::EnvVars(ref kvs) => {
        if kvs.is_empty() {
          write!(&mut buffer, "<env-vars>{{}}")?;
          writer.write_all(&buffer.into_inner())?;
          Ok(())
        } else if kvs.len() == 1 {
          let (k, v) = match kvs.iter().next() {
            None => unreachable!(),
            Some(&(ref k, ref v)) => (k, v),
          };
          write!(&mut buffer, "<env-vars>{{${} => ", k.0)?;
          let mut val_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          val_box._print_exp(builder, exp.lookup(v), &mut buffer)?;
          if val_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          write!(&mut buffer, "}}")?;
          writer.write_all(&buffer.into_inner())?;
          Ok(())
        } else {
          unimplemented!();
        }
      }
      &LTerm::EnvVarsLazy(ref kvs) => {
        if kvs.is_empty() {
          write!(&mut buffer, "<env-vars-L>{{}}")?;
          writer.write_all(&buffer.into_inner())?;
          Ok(())
        } else if kvs.len() == 1 {
          let (k, v) = match kvs.iter().next() {
            None => unreachable!(),
            Some(&(ref k, ref v)) => (k, v),
          };
          write!(&mut buffer, "<env-vars-L>{{${} => ", k.0)?;
          let mut val_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          val_box._print_exp(builder, exp.lookup(v), &mut buffer)?;
          if val_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          write!(&mut buffer, "}}")?;
          writer.write_all(&buffer.into_inner())?;
          Ok(())
        } else {
          unimplemented!();
        }
      }
      &LTerm::EImportVar(ref sel_var, ref target, ref rest) => {
        // TODO
        write!(&mut buffer, "<E-import-var>({:?}", sel_var)?;
        write!(&mut buffer, ")")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::EImportVars(ref sel_vars, ref target, ref rest) => {
        // TODO
        write!(&mut buffer, "<E-import-vars>({:?}", sel_vars)?;
        write!(&mut buffer, ")")?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::EConsVarLazy(ref var, ref value, ref target) => {
        // TODO
        write!(&mut buffer, "(${} => ", var.0)?;
        let mut value_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        value_box._print_exp(builder, exp.lookup(value), &mut buffer)?;
        if value_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, " <E-cons-var-L::> ")?;
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
      &LTerm::EPopVars(ref params, ref target) => {
        // TODO
        write!(&mut buffer, "<E-pop-vars>(")?;
        for (p_idx, &(ref key, idx)) in params.iter().enumerate() {
          write!(&mut buffer, "${} => %{}", key.0, idx)?;
          if p_idx != params.len() - 1 {
            write!(&mut buffer, ", ")?;
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
      &LTerm::AApply(ref target, ref args) => {
        write!(&mut buffer, "<A-app>(")?;
        for &(ref idx, ref key, ref ident, ref adj_key) in args.iter() {
          match ident {
            &LVarBinder::Ident(ref ident) => {
              let ident_s = builder.lookup_ident(ident);
              write!(&mut buffer, "%{} => (${}({}), ${})", idx, key.0, ident_s, adj_key.0)?;
            }
            _ => {
              write!(&mut buffer, "%{} => (${}, ${})", idx, key.0, adj_key.0)?;
            }
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
      &LTerm::AReturn(/*ref mask,*/ ref params, ref target) => {
        // TODO
        write!(&mut buffer, "<A-ret>(")?;
        for (p_idx, &(ref idx, ref key)) in params.iter().enumerate() {
          write!(&mut buffer, "${} => %{}", key.0, idx)?;
          if p_idx != params.len() - 1 {
            write!(&mut buffer, ", ")?;
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
      &LTerm::ACons(ref key, ref _ident, ref value, ref target) => {
        // TODO
        /*if ident.is_some() {
          let ident_s = builder.lookup_ident(ident.borrow().unwrap());
          write!(&mut buffer, "({{${}({}) => ", key.0, ident_s)?;
        } else {
          write!(&mut buffer, "({{${} => ", key.0)?;
        }*/
        write!(&mut buffer, "(${} => ", key.0)?;
        let mut value_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        value_box._print_exp(builder, exp.lookup(value), &mut buffer)?;
        if value_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, " <A::> ")?;
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
      &LTerm::AConcat(ref lhs, ref rhs) => {
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
        write!(&mut buffer, "(")?;
        let mut head_box = PrintBox{
          left_indent:  self.left_indent + buffer.position() as usize,
          line_nr:      1,
        };
        head_box._print_exp(builder, exp.lookup(head), &mut buffer)?;
        if head_box.line_nr > 1 {
          // TODO
          unimplemented!();
        }
        write!(&mut buffer, ")[")?;
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
          // TODO
          write!(&mut buffer, "match ")?;
          let mut query_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          query_box._print_exp(builder, exp.lookup(query), &mut buffer)?;
          if query_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          writer.write_all(&buffer.into_inner())?;
          self._newline(writer)?;
          for (idx, &(ref pat, ref arm)) in pat_arms.iter().enumerate() {
            let mut buffer = Cursor::new(vec![]);
            write!(&mut buffer, "  | ")?;
            let mut pat_box = PrintBox{
              left_indent:  self.left_indent + buffer.position() as usize,
              line_nr:      1,
            };
            pat_box._print_pat(builder, pat.clone(), &mut buffer)?;
            if pat_box.line_nr > 1 {
              // TODO
              unimplemented!();
            }
            write!(&mut buffer, " => ")?;
            let mut arm_box = PrintBox{
              left_indent:  self.left_indent + buffer.position() as usize,
              line_nr:      1,
            };
            arm_box._print_exp(builder, exp.lookup(arm), &mut buffer)?;
            // TODO
            if arm_box.line_nr > 1 {
              writer.write_all(&buffer.into_inner())?;
              self.line_nr += query_box.line_nr - 1;
              if idx != pat_arms.len() - 1 {
                self._newline(writer)?;
              }
            } else {
              writer.write_all(&buffer.into_inner())?;
              if idx != pat_arms.len() - 1 {
                self._newline(writer)?;
              }
            }
          }
          Ok(())
        }
      }
      &LTerm::Mismatch(ref query, ref pat_arms) => {
        // TODO
        if pat_arms.len() == 1 {
          unimplemented!();
        } else {
          // TODO
          write!(&mut buffer, "mismatch ")?;
          let mut query_box = PrintBox{
            left_indent:  self.left_indent + buffer.position() as usize,
            line_nr:      1,
          };
          query_box._print_exp(builder, exp.lookup(query), &mut buffer)?;
          if query_box.line_nr > 1 {
            // TODO
            unimplemented!();
          }
          writer.write_all(&buffer.into_inner())?;
          self._newline(writer)?;
          for (idx, &(ref pat, ref arm)) in pat_arms.iter().enumerate() {
            let mut buffer = Cursor::new(vec![]);
            write!(&mut buffer, "  | ")?;
            let mut pat_box = PrintBox{
              left_indent:  self.left_indent + buffer.position() as usize,
              line_nr:      1,
            };
            pat_box._print_pat(builder, pat.clone(), &mut buffer)?;
            if pat_box.line_nr > 1 {
              // TODO
              unimplemented!();
            }
            write!(&mut buffer, " => ")?;
            let mut arm_box = PrintBox{
              left_indent:  self.left_indent + buffer.position() as usize,
              line_nr:      1,
            };
            arm_box._print_exp(builder, exp.lookup(arm), &mut buffer)?;
            // TODO
            if arm_box.line_nr > 1 {
              writer.write_all(&buffer.into_inner())?;
              self.line_nr += query_box.line_nr - 1;
              if idx != pat_arms.len() - 1 {
                self._newline(writer)?;
              }
            } else {
              writer.write_all(&buffer.into_inner())?;
              if idx != pat_arms.len() - 1 {
                self._newline(writer)?;
              }
            }
          }
          Ok(())
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
      &LTerm::Index(idx) => {
        write!(&mut buffer, "%{}", idx)?;
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
      &LTerm::LookupIdent(ref ident) => {
        let ident_s = builder.lookup_ident(&ident);
        write!(&mut buffer, "#{}({})", ident.0, ident_s)?;
        writer.write_all(&buffer.into_inner())?;
        Ok(())
      }
      &LTerm::ProjectVar(ref target, ref key) => {
        //let ident_s = builder.lookup_ident(&ident);
        let mut target_box = PrintBox{
          left_indent:  self.left_indent,
          line_nr:      1,
        };
        target_box._print_exp(builder, exp.lookup(target), &mut buffer)?;
        if target_box.line_nr > 1 {
          unimplemented!();
        } else {
          write!(buffer, ".${}", key.0)?;
          writer.write_all(&buffer.into_inner())?;
        }
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
          write!(buffer, ".#{}({})", ident.0, ident_s)?;
          writer.write_all(&buffer.into_inner())?;
        }
        Ok(())
      }
      &LTerm::MX(_) => {
        // TODO
        write!(&mut buffer, "<MX>")?;
        writer.write_all(&buffer.into_inner())?;
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
