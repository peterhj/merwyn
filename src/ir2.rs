// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::mach::{MAddr, MBModule, MCModule};

use rpds::{HashTrieMap, RedBlackTreeMap};

use std::cell::{RefCell};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LLabel(u64);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LHash(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LVar(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LEnvKey {
  Var(LVar),
  Pos(usize),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LTyvar(u64);

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

  pub fn compile(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LModule {
    // TODO
    let ltree = self._lower(htree, ctx);
    //let ltree = self._lower_with_toplevel(htree, ctx);
    let ltree = self._normalize(ltree);
    //let ltree = self._rederive_ctxs(ltree);
    // FIXME: take the final ctxtree and convert it into an end ctx, if possible.
    let end_ctx = None;
    //let end_ctx = Some(ltree.ctxs[ltree.ctxs.len() - 1].clone());
    LModule{
      tree: ltree,
      end_ctx,
    }
  }
}

impl LBuilder {
  pub fn _lower_pat_rec(&mut self, htree: Rc<HExpr>, bindings: ()) -> () {
    // TODO
    unimplemented!();
  }

  //pub fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
  pub fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
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
    let op_ = LLoc::new2(op_label, pos + 1, pos);
    let mut curr_pos = pos + 2;
    let (arg_label, next_pos) = self._lower_rec(arg, ctx.clone(), stack, curr_pos);
    let arg_ = LLoc::new2(arg_label, curr_pos, pos);
    curr_pos = next_pos;
    let label = self.fresh_label();
    let e = LExpr{
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![arg_])
    };
    //stack.push_front((op_e, ctx.clone(), pos + 1));
    //stack.push_front((e, ctx, pos));
    stack.insert(pos + 1, (op_e, ctx.clone(), pos + 1));
    stack.insert(pos, (e, ctx, pos));
    (label, curr_pos)
  }

  //pub fn _lower_binop(&mut self, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
  pub fn _lower_binop(&mut self, op_name: &str, lhs: Rc<HExpr>, rhs: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
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
      label:    label.clone(),
      term:     LTerm::Apply(op_, vec![lhs_, rhs_])
    };
    //stack.push_front((op_e, ctx.clone(), pos + 1));
    //stack.push_front((e, ctx, pos));
    stack.insert(pos + 1, (op_e, ctx.clone(), pos + 1));
    stack.insert(pos, (e, ctx, pos));
    (label, curr_pos)
  }

  //pub fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut VecDeque<(LExpr, LCtxRef, usize)>, /*ltree: &mut LTree, ctxtree: &mut LCtxTree,*/ pos: usize) -> (LLabel, usize) {
  pub fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, /*ltree: &mut LTree, ctxtree: &mut LCtxTree,*/ pos: usize) -> (LLabel, usize) {
    match &*htree {
      &HExpr::End => {
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::End
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
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
          term:     LTerm::Lambda(param_vars, LLoc::new2(body_label, body_pos, pos))
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
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
          label:    label.clone(),
          term:     LTerm::Apply(head_, args_)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, curr_pos)
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        let body_ctx = ctx.clone();
        let mut rest_ctx = ctx.clone();
        let name = match &**lhs {
          &HExpr::Ident(ref name) => name,
          _ => unimplemented!(),
        };
        let n_hash = self.lookup_name(name);
        let n_var = self.fresh_var();
        rest_ctx.bind_mut(n_hash, n_var.clone());
        let body_pos = pos + 1;
        let (body_label, next_pos) = self._lower_rec(body.clone(), body_ctx, stack, body_pos);
        let body_ = LLoc::new2(body_label, body_pos, pos);
        let rest_pos = next_pos;
        let (rest_label, next_pos) = self._lower_rec(rest.clone(), rest_ctx, stack, rest_pos);
        let rest_ = LLoc::new2(rest_label, rest_pos, pos);
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::Let(n_var, body_, rest_)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
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
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::TeeLit => {
        let label = self.fresh_label();
        let e = LExpr{
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
          label:    label.clone(),
          term:     LTerm::FloLit(x)
        };
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
        (label, pos + 1)
      }
      &HExpr::Ident(ref name) => {
        let name_hash = self.lookup_name(name);
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
        //stack.push_front((e, ctx, pos));
        stack.insert(pos, (e, ctx, pos));
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
    let mut stack = BTreeMap::new();
    self._lower_rec(htree, ctx, &mut stack, 0);
    let mut ltree = LTree::default();
    for (&pos, &(ref e, ref ctx, pos2)) in stack.iter() {
      assert_eq!(pos, pos2);
      assert_eq!(pos, ltree.exps.len());
      assert_eq!(pos, ltree.ctxs.len());
      ltree.exps.push(e.clone());
      ltree.ctxs.push(ctx.clone());
    }
    ltree
  }
}

impl LBuilder {
  pub fn _normalize_kont(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    // TODO
    match &exp.term {
      &LTerm::End => kont(self, exp),
      &LTerm::Apply(ref head, ref args) => {
        // TODO
        unimplemented!();
      }
      &LTerm::Lambda(ref params, ref body) => {
        let body = self._normalize_term(exp.lookup(body));
        let new_exp = exp.append(self, &mut |_| LTerm::Lambda(
            params.clone(),
            body.loc(),
        ));
        kont(self, new_exp)
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
      &LTerm::BitLit(_) => kont(self, exp),
      &LTerm::IntLit(_) => kont(self, exp),
      &LTerm::FloLit(_) => kont(self, exp),
      &LTerm::Lookup(_) => kont(self, exp),
      _ => {
        unimplemented!();
      }
    }
  }

  pub fn _normalize_term(&mut self, exp: LExprCell) -> LExprCell {
    self._normalize_kont(exp, &mut |_, e| e)
  }

  pub fn _normalize_names(&mut self, pre_exps: VecDeque<LExprCell>, post_exps: VecDeque<LExprCell>, kont: &mut dyn FnMut(&mut Self, LExprCell) -> ()) -> () {
    // TODO
  }

  pub fn _normalize_name(&mut self, exp: LExprCell, kont: &mut dyn FnMut(&mut Self, LExprCell) -> LExprCell) -> LExprCell {
    // TODO
    self._normalize_kont(exp, &mut |this, exp| {
      match &exp.term {
        &LTerm::BitLit(_) => kont(this, exp),
        &LTerm::IntLit(_) => kont(this, exp),
        &LTerm::FloLit(_) => kont(this, exp),
        &LTerm::Lookup(_) => kont(this, exp),
        // TODO
        _ => {
          let new_var = this.fresh_var();
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

  pub fn _normalize(&mut self, tree: LTree) -> LTree {
    let tree = LTreeCell::new(tree);
    let new_head = self._normalize_term(tree.start());
    let old_tree = tree.inner.borrow();
    LTree{
      root: new_head.pos,
      mlib: old_tree.mlib.clone(),
      exps: old_tree.exps.clone(),
      ctxs: Vec::new(),
    }
  }
}

impl LBuilder {
  pub fn _rederive_ctxs(&mut self, ltree: LTree) -> LTree {
    // FIXME
    //unimplemented!();
    ltree
  }
}

pub struct LModule {
  // TODO
  pub tree:     LTree,
  //pub code:     LCodeRef,
  pub end_ctx:  Option<LCtxRef>,
}

#[derive(Clone)]
pub enum LCtxBinder {
  Hash(LHash),
  Anon,
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

  pub fn bind_anon_mut(&mut self, var: LVar) {
    self.var_to_bind.insert_mut(var, LCtxBinder::Anon);
  }
}

#[derive(Clone, Default)]
pub struct LTyctxRef {
  var_to_tyvar: HashTrieMap<LVar, LTyvar>,
}

impl LTyctxRef {
  pub fn lookup_var(&self, var: &LVar) -> Option<LTyvar> {
    match self.var_to_tyvar.get(var) {
      None => None,
      Some(tv) => Some(tv.clone()),
    }
  }
}

pub type LTyRef = Rc<LTy>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LTy {
  Var(LTyvar),
  Fun(Vec<LTyRef>, LTyRef),
  Env(RedBlackTreeMap<LEnvKey, LTyRef>),
  STup(Vec<LTyRef>),
  Tup,
  Bit,
  Int,
  Flo,
}

struct TyUnionFind {
  db:   BTreeMap<LTyvar, LTyvar>,
  _mgu: BTreeMap<LTyvar, LTy>,
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

  fn mgu(&mut self, query: LTyvar) -> Option<LTy> {
    let head = self.head(query);
    match self._mgu.get(&head) {
      None => None,
      Some(ty) => Some(ty.clone()),
    }
  }

  fn unify(&mut self, lhs: LTy, rhs: LTy) {
    match (lhs, rhs) {
      (LTy::Var(lv), LTy::Var(rv)) => {
        // TODO
        unimplemented!();
      }
      (LTy::Var(v), ty) => {
        // TODO: there might already be a MGU, in which case unify failed.
        let w = self.head(v);
        self._mgu.insert(w, ty);
      }
      (ty, LTy::Var(v)) => {
        // TODO: there might already be a MGU, in which case unify failed.
        let w = self.head(v);
        self._mgu.insert(w, ty);
      }
      (_, _) => unreachable!(),
    }
  }
}

struct TyHyp {
}

type TyConRef = Rc<TyCon>;

enum TyCon {
  Nil,
  Cnj(TyConRef, TyConRef),
  Eq(LTy, LTy),
  IsACons(LEnvKey, LTy, LTy, LTy),
  IsAConcat(LTy, LTy, LTy),
  IsAApp(Vec<(usize, LVar)>, LTy, LTy),
  IsERet(Vec<(usize, LVar)>, LTy, LTy),
  IsEHash(LTy, LHash, LTy),
}

struct IncTyInfMachine {
  //hyps: VecDeque<TyHyp>,
  //cons: VecDeque<TyCon>,
  sub:  TyUnionFind,
}

impl IncTyInfMachine {
  fn _solve(&mut self, con: TyConRef) -> Result<(), TyConRef> {
    match &*con {
      &TyCon::Nil => Ok(()),
      &TyCon::Cnj(ref lhs, ref rhs) => {
        self._solve(lhs.clone())?;
        self._solve(rhs.clone())
      }
      &TyCon::Eq(ref lty, ref rty) => {
        match (lty, rty) {
          // TODO: more cases.
          (&LTy::Fun(ref lhs_dom, ref lhs_cod), &LTy::Fun(ref rhs_dom, ref rhs_cod)) => {
            if lhs_dom.len() != rhs_dom.len() {
              return Err(con);
            }
            let mut con = con.clone();
            for (lty, rty) in lhs_dom.iter().zip(rhs_dom.iter()) {
              con = TyConRef::new(TyCon::Cnj(
                  TyConRef::new(TyCon::Eq((**lty).clone(), (**rty).clone())),
                  con,
              ));
            }
            con = TyConRef::new(TyCon::Cnj(
                TyConRef::new(TyCon::Eq((**lhs_cod).clone(), (**rhs_cod).clone())),
                con,
            ));
            self._solve(con)
          }
          _ => {
            // TODO: unification may fail.
            self.sub.unify(lty.clone(), rty.clone());
            Ok(())
          }
        }
      }
    }
  }
}

#[derive(Clone)]
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
}

#[derive(Clone, Debug)]
pub struct LLoc {
  pub label:    LLabel,
  pub pos:      usize,
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

pub type LCodeRef = Rc<LCode>;

pub struct LCode {
  pub mlib:     Vec<LMExpr>,
  pub exps:     Vec<LExpr>,
}

#[derive(Clone)]
pub struct LTreeCell {
  inner:    Rc<RefCell<LTree>>,
}

impl LTreeCell {
  pub fn new(inner: LTree) -> LTreeCell {
    LTreeCell{inner: Rc::new(RefCell::new(inner))}
  }

  pub fn start(&self) -> LExprCell {
    let tree = self.inner.borrow();
    let exp = tree.exps[tree.root].clone();
    LExprCell{
      tree:     self.clone(),
      pos:      tree.root,
      label:    exp.label,
      term:     exp.term,
    }
  }
}

#[derive(Default)]
pub struct LTree {
  // TODO
  pub root:     usize,
  pub mlib:     Vec<LMExpr>,
  pub exps:     Vec<LExpr>,
  pub ctxs:     Vec<LCtxRef>,
  //pub ctxs:     HashMap<LLabel, LCtxRef>,
  //pub etys:     HashMap<LLabel, LTyvar>,
  //pub tyctxs:   HashMap<LLabel, LTyctxRef>,
}

#[derive(Default)]
pub struct LTreeData {
  // TODO
  pub mexps:    Vec<LMExpr>,
  pub exps:     Vec<LExpr>,
  pub ctxs:     HashMap<LLabel, LCtxRef>,
  pub etys:     HashMap<LLabel, LTyvar>,
  pub tyctxs:   HashMap<LLabel, LTyctxRef>,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Clone)]
pub struct LExprCell {
  pub tree:     LTreeCell,
  pub pos:      usize,
  pub label:    LLabel,
  pub term:     LTerm,
}

impl LExprCell {
  pub fn loc(&self) -> LLoc {
    LLoc{
      label:    self.label.clone(),
      pos:      self.pos,
    }
  }

  pub fn ctx(&self) -> LCtxRef {
    // TODO
    unimplemented!();
  }

  pub fn lookup(&self, loc: &LLoc) -> LExprCell {
    let tree = self.tree.inner.borrow();
    assert_eq!(loc.label, tree.exps[loc.pos].label);
    LExprCell{
      tree:     self.tree.clone(),
      pos:      loc.pos,
      label:    loc.label.clone(),
      term:     tree.exps[loc.pos].term.clone(),
    }
  }

  pub fn append(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LTerm) -> LExprCell {
    let new_term = (mk_term)(builder);
    let (new_pos, new_label, new_term) = {
      let mut tree = self.tree.inner.borrow_mut();
      let new_pos = tree.exps.len();
      let new_label = builder.fresh_label();
      tree.exps.push(LExpr{
        label:    new_label.clone(),
        term:     new_term.clone(),
      });
      (new_pos, new_label, new_term)
    };
    LExprCell{
      tree:     self.tree.clone(),
      pos:      new_pos,
      label:    new_label,
      term:     new_term,
    }
  }
}

#[derive(Clone)]
pub struct LExprRef {
  pub code:     LCodeRef,
  pub pos:      usize,
  pub label:    LLabel,
  pub term:     LTerm,
}

impl LExprRef {
  pub fn jump(self, rel: LRel) -> LExprRef {
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
  }
}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum LTerm<E=LLoc> {
  End,
  Module(Vec<E>, E),
  TodoRequire,
  Break(E),
  Apply(E, Vec<E>),
  Lambda(Vec<LVar>, E),
  //EImport(E, E),
  D(E),
  //DirD(E, E),
  //SpkD(E),
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
  PathLookupHash(E, LHash),
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
  BLambda(LMLambdaDef<MBModule>),
  CLambda(LMLambdaDef<MCModule>),
}

#[derive(Clone)]
pub struct LMLambdaDef<Module> {
  pub ar:   usize,
  pub cg:   Option<Rc<dyn Fn() -> Module>>,
  pub ty:   Option<Rc<dyn Fn(&mut LBuilder, /*LCtxRef*/) -> (Vec<LTy>, LTy)>>,
  pub adj:  Option<Rc<dyn Fn(&mut LBuilder, /*LCtxRef,*/ Vec<LVar>, LVar) -> LExpr>>,
}
