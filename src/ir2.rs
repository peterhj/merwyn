// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::mach::{MAddr, MBModule, MCModule};

use rpds::{HashTrieMap, Queue, RedBlackTreeMap, Stack};

use std::cell::{RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LLabel(u64);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
  Export,
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
  BLam(LMLambdaDef<MBModule>),
  CLam(LMLambdaDef<MCModule>),
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
  Hash(LHash),
  Anon,
}

impl From<LHash> for LVarBinder {
  fn from(hash: LHash) -> LVarBinder {
    LVarBinder::Hash(hash)
  }
}

#[derive(Default)]
pub struct LBuilder {
  label_ctr:    u64,
  hash_ctr:     u64,
  var_ctr:      u64,
  name_to_hash: HashMap<String, LHash>,
  hash_to_name: HashMap<LHash, String>,
  var_to_bind:  HashMap<LVar, LVarBinder>,
  tyinf:        IncTyInfMachine
}

impl LBuilder {
  pub fn fresh_label(&mut self) -> LLabel {
    self.label_ctr += 1;
    assert!(self.label_ctr != 0);
    LLabel(self.label_ctr)
  }

  pub fn fresh_anon_var(&mut self) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    let new_var = LVar(self.var_ctr);
    assert!(self.var_to_bind.insert(new_var.clone(), LVarBinder::Anon).is_none());
    new_var
  }

  pub fn fresh_hash_var(&mut self, hash: LHash) -> LVar {
    self.var_ctr += 1;
    assert!(self.var_ctr != 0);
    let new_var = LVar(self.var_ctr);
    assert!(self.var_to_bind.insert(new_var.clone(), LVarBinder::Hash(hash.clone())).is_none());
    new_var
  }

  pub fn lookup_var(&mut self, var: &LVar) -> LVarBinder {
    match self.var_to_bind.get(var) {
      None => panic!("bug"),
      Some(binder) => binder.clone(),
    }
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

  pub fn compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef) -> LModule {
  //pub fn compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef) -> Result<LModule, ()> {
  //pub fn compile(&mut self, htree: Rc<HExpr>, top_ctx: LCtxRef, top_tyctx: LTyctxRef) -> Result<LModule, ()> {
    // TODO
    let tree = self._lower(htree, top_ctx.clone());
    let tree = self._normalize(tree);
    let tree = self._recontext(tree, top_ctx.clone());
    //let tree = self._gc(tree);
    //let mut tyinf = IncTyInfMachine::default();
    let mut tyinf_work = TyInfWork::default();
    self.tyinf.gen(&tree, &mut tyinf_work);
    //println!("DEBUG: compile: generated ty constraint: {:?}", ty_con);
    let ty_res = self.tyinf.solve(tree.root(), &mut tyinf_work);
    println!("DEBUG: compile: tyinf result: {:?}", ty_res);
    println!("DEBUG: compile:   deferred: {:?}", tyinf_work.defer_cs);
    println!("DEBUG: compile:   unsatted: {:?}", tyinf_work.unsat_cs);
    let end_ctx = tree.end_ctx();
    LModule{
      tree,
      end_ctx,
    }
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

  pub fn _lower_rec(&mut self, htree: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, /*up: LLoc, label: LLabel,*/ pos: usize) -> (LLabel, usize) {
    match &*htree {
      &HExpr::End => {
        let label = self.fresh_label();
        let e = LExpr{
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
            /*LExpr{
            label:  label.clone(),
            term:   LTerm::Alt(prev_n_var, n_var, body_, rest_)
            }*/
          }
          None => LExpr{
            label:  label.clone(),
            term:   LTerm::Let(n_var, body_, rest_)
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
          label:    label.clone(),
          term:     LTerm::PathLookupHash(lhs_, name_hash)
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
    let mut ltree = LTreeData::default();
    for (&pos, &(ref e, ref ctx, pos2)) in stack.iter() {
      assert_eq!(pos, pos2);
      assert_eq!(pos, ltree.exps.len());
      assert_eq!(pos, ltree.ctxs.len());
      ltree.exps.push(e.clone());
      ltree.ctxs.insert(e.label.clone(), ctx.clone());
    }
    let view = LTreeView{
      root:     LLoc::new(ltree.exps[0].label.clone(), 0),
      version:  ltree.exps.len(),
      revision: 0,
      changed:  false,
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
      &LTerm::PathLookupHash(ref env, ref name) => {
        let env = exp.lookup(env);
        self._normalize_name(env, &mut |this, env| {
          let new_exp = exp.append(this, &mut |_| LTerm::PathLookupHash(
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
    new_root.unsafe_self_root();
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
      &LTerm::PathLookupHash(ref env, _) => {
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

pub struct LModule {
  // TODO
  pub tree:     LTreeCell,
  //pub code:     LCodeRef,
  pub end_ctx:  Option<LCtxRef>,
}

#[derive(Clone, Default)]
pub struct LCtxRef {
  bind_to_var:  HashTrieMap<LVarBinder, LVar>,
  var_to_depth: HashTrieMap<LVar, usize>,
  var_stack:    Stack<LVar>,
}

impl LCtxRef {
  pub fn lookup_hash(&self, hash: LHash) -> Option<LVar> {
    match self.bind_to_var.get(&LVarBinder::Hash(hash)) {
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

#[derive(Clone, Default)]
pub struct LAdjCtxRef {
  var_to_adj:   HashTrieMap<LVar, LVar>,
}

#[derive(Clone, Default)]
pub struct LTyctxRef {
  var_to_ty:    HashTrieMap<LVar, (LTyvar, LTy)>,
}

impl LTyctxRef {
  /*pub fn lookup_var(&self, var: &LVar) -> Option<LTy> {
    match self.var_to_tyvar.get(var) {
      None => None,
      Some(tv) => Some(tv.clone()),
    }
  }*/
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LTyexp {
  Var(LTyvar),
  Fun(Vec<LTyexpRef>, LTyexpRef),
  //EnvCons(LVar, LHash, LTyvar, LTyexpRef),
  //EnvCat(RedBlackTreeMap<LEnvKey, LTyvar>, RedBlackTreeMap<LHash, LVar>, LTyexpRef),
  Env(RedBlackTreeMap<LEnvKey, LTyvar>, RedBlackTreeMap<LHash, LVar>),
  STup(Vec<LTyexpRef>),
  Tup,
  Bit,
  Int,
  Flo,
  VFlo,
  Unit,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct LTyexpRef(Rc<LTyexp>);

impl From<LTyexp> for LTyexpRef {
  fn from(e: LTyexp) -> LTyexpRef {
    LTyexpRef(Rc::new(e))
  }
}

impl From<LTyvar> for LTyexpRef {
  fn from(v: LTyvar) -> LTyexpRef {
    LTyexpRef::from(LTyexp::Var(v))
  }
}

impl Deref for LTyexpRef {
  type Target = LTyexp;

  fn deref(&self) -> &LTyexp {
    &*self.0
  }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LTytag {
  // FIXME: need more of the domain signature, arity alone is not sufficient.
  PtlDf(usize),
  PtlDv,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LTy {
  Fun(Vec<LTyRef>, LTyRef),
  Env(RedBlackTreeMap<LEnvKey, LTyRef>, RedBlackTreeMap<LHash, LVar>),
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
  Eq_(LTyexpRef, LTyexpRef),
  Tagged(LTyexpRef, LTytag),
  IsPtlD(LTyexpRef, LTyexpRef),
  //IsACons(LVar, LTy, LTy, LTy),
  //IsAConcat(LTy, LTy, LTy),
  //IsAApp(Vec<(usize, LVar)>, LTyvar, LTy),
  //IsERet(Vec<(usize, LVar)>, LTyvar, LTy),
  IsEHashSel(LTyexpRef, LTyexpRef, LHash),
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

#[derive(Default)]
struct TyInfWork {
  cons:     VecDeque<TyConRef>,
  defer_cs: VecDeque<TyConRef>,
  unsat_cs: VecDeque<TyConRef>,
}

enum TyReduce {
  Exp(LTyexpRef),
  Var(LTyvar),
}

enum TyUnify {
  OK,
  Maybe,
  No,
}

#[derive(Default)]
struct TyUnionFind {
  db:   BTreeMap<LTyvar, LTyvar>,
  tag:  BTreeMap<LTyvar, LTytag>,
  term: BTreeMap<LTyvar, LTyexpRef>,
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
}

#[derive(Clone, Default)]
struct TyEnv {
  db:   RedBlackTreeMap<LTyvar, LTyvar>,
  tag:  RedBlackTreeMap<LTyvar, LTytag>,
  texp: RedBlackTreeMap<LTyvar, LTyexpRef>,
}

impl TyEnv {
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
    match self.tag.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.tag.remove_mut(&lw);
        self.tag.insert_mut(rw.clone(), t);
      }
    }
    match self.texp.get(&lw) {
      None => {}
      Some(t) => {
        let t = t.clone();
        self.texp.remove_mut(&lw);
        self.texp.insert_mut(rw.clone(), t);
      }
    }
  }

  fn unify_exp(&mut self, v: LTyvar, query: LTyexpRef) {
    let w = self.head(v);
    self.texp.insert_mut(w, query);
  }

  fn reduce(&mut self, v: LTyvar) -> TyReduce {
    let w = self.head(v);
    match self.texp.get(&w) {
      None => TyReduce::Var(w),
      Some(query) => {
        let query = query.clone();
        let query = self.reduce_exp(query);
        self.texp.insert_mut(w, query.clone());
        TyReduce::Exp(query)
      }
    }
  }

  fn reduce_exp(&mut self, query: LTyexpRef) -> LTyexpRef {
    match &*query {
      // TODO: cases.
      &LTyexp::Var(ref v) => {
        match self.reduce(v.clone()) {
          TyReduce::Exp(e) => e,
          TyReduce::Var(w) => w.into(),
        }
      }
      &LTyexp::Fun(ref dom, ref ret) => {
        let mut dom_ = Vec::with_capacity(dom.len());
        for d in dom.iter() {
          dom_.push(self.reduce_exp(d.clone()));
        }
        let ret_ = self.reduce_exp(ret.clone());
        LTyexp::Fun(dom_, ret_).into()
      }
      &LTyexp::Tup |
      &LTyexp::Bit |
      &LTyexp::Int |
      &LTyexp::Flo |
      &LTyexp::Unit => query,
      _ => unimplemented!(),
    }
  }
}

#[derive(Default)]
struct IncTyInfMachine {
  tyv_ctr:  u64,
  //sub:      TyUnionFind,
  tenv:     TyEnv,
}

impl IncTyInfMachine {
  fn fresh_tyvar(&mut self) -> LTyvar {
    self.tyv_ctr += 1;
    assert!(self.tyv_ctr != 0);
    LTyvar(self.tyv_ctr)
  }

  fn _gen_exp(&mut self, exp: LExprCell, cons: &mut VecDeque<TyConRef>) {
    let ety = exp.unsafe_set_fresh_ety(self);
    match &exp.term() {
      &LTerm::End => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Unit.into()));
        cons.push_front(con);
      }
      &LTerm::Break(ref inner) => {
        self._gen_exp(exp.lookup(inner), cons);
        let brk_con = TyConRef::new(TyCon::Eq_(ety.into(), exp.lookup_ety(inner).into()));
        cons.push_front(brk_con);
      }
      &LTerm::Apply(ref head, ref args) => {
        self._gen_exp(exp.lookup(head), cons);
        let mut arg_tys = Vec::with_capacity(args.len());
        for a in args.iter() {
          self._gen_exp(exp.lookup(a), cons);
          arg_tys.push(exp.lookup_ety(a).into());
        }
        let app_con = TyConRef::new(TyCon::Eq_(exp.lookup_ety(head).into(), LTyexp::Fun(arg_tys, ety.into()).into()));
        cons.push_front(app_con);
      }
      &LTerm::Lambda(ref params, ref body) => {
        let mut param_tys = Vec::with_capacity(params.len());
        for p in params.iter() {
          let p_vty = exp.lookup_vty(p, self);
          param_tys.push(p_vty.into());
        }
        self._gen_exp(exp.lookup(body), cons);
        let lam_con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Fun(param_tys, exp.lookup_ety(body).into()).into()));
        cons.push_front(lam_con);
      }
      &LTerm::Import(ref _env, ref _body) => {
        // FIXME: need MGU after tyinf.
        unimplemented!();
      }
      &LTerm::Export => {
        let ctx = exp.ctx();
        let mut keys: RedBlackTreeMap<LEnvKey, LTyvar> = Default::default();
        let mut hashes: RedBlackTreeMap<LHash, LVar> = Default::default();
        for (binder, var) in ctx.bind_to_var.iter() {
          keys.insert_mut(LEnvKey::Var(var.clone()), exp.lookup_vty(var, self));
          match binder {
            &LVarBinder::Hash(ref hash) => {
              hashes.insert_mut(hash.clone(), var.clone());
            }
            &LVarBinder::Anon => {}
          }
        }
        let con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Env(keys, hashes).into()));
        cons.push_front(con);
      }
      &LTerm::PtlD(ref target) => {
        self._gen_exp(exp.lookup(target), cons);
        let con = TyConRef::new(TyCon::IsPtlD(ety.into(), exp.lookup_ety(target).into()));
        cons.push_front(con);
      }
      &LTerm::Let(ref name, ref body, ref rest) => {
        let name_vty = exp.lookup_vty(name, self);
        self._gen_exp(exp.lookup(body), cons);
        self._gen_exp(exp.lookup(rest), cons);
        let let_con1 = TyConRef::new(TyCon::Eq_(name_vty.into(), exp.lookup_ety(body).into()));
        let let_con2 = TyConRef::new(TyCon::Eq_(ety.into(), exp.lookup_ety(rest).into()));
        cons.push_front(let_con2);
        cons.push_front(let_con1);
      }
      &LTerm::Fix(ref fixname, ref fixbody) => {
        let fixname_vty = exp.lookup_vty(fixname, self);
        self._gen_exp(exp.lookup(fixbody), cons);
        let fix_con1 = TyConRef::new(TyCon::Eq_(fixname_vty.into(), exp.lookup_ety(fixbody).into()));
        let fix_con2 = TyConRef::new(TyCon::Eq_(ety.into(), exp.lookup_ety(fixbody).into()));
        cons.push_front(fix_con2);
        cons.push_front(fix_con1);
      }
      /*&LTerm::Alt(ref name, ref alt_name, ref body, ref rest) => {
        // TODO
        panic!("bug: typing of alt bindings is not yet supported");
      }*/
      &LTerm::BitLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Bit.into()));
        cons.push_front(con);
      }
      &LTerm::IntLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Int.into()));
        cons.push_front(con);
      }
      &LTerm::FloLit(_) => {
        let con = TyConRef::new(TyCon::Eq_(ety.into(), LTyexp::Flo.into()));
        cons.push_front(con);
      }
      &LTerm::Lookup(ref name) => {
        let name_vty = exp.lookup_vty(name, self);
        let con = TyConRef::new(TyCon::Eq_(ety.into(), name_vty.into()));
        cons.push_front(con);
      }
      &LTerm::PathLookupHash(ref env, ref hash) => {
        let env_con = self._gen_exp(exp.lookup(env), cons);
        let hashsel_con = TyConRef::new(TyCon::IsEHashSel(ety.into(), exp.lookup_ety(env).into(), hash.clone()));
        cons.push_front(hashsel_con);
      }
      _ => unimplemented!(),
    }
  }

  fn gen(&mut self, tree: &LTreeCell, work: &mut TyInfWork) {
    self._gen_exp(tree.root(), &mut work.cons);
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

  fn _mgu_reduced(&mut self, query: LTyexpRef) -> Result<LTyRef, ()> {
    match &*query {
      // TODO: cases.
      &LTyexp::Var(_) => Err(()),
      &LTyexp::Fun(ref dom, ref ret) => {
        let mut dom_ = Vec::with_capacity(dom.len());
        for d in dom.iter() {
          dom_.push(self._mgu_reduced(d.clone())?);
        }
        let ret_ = self._mgu_reduced(ret.clone())?;
        Ok(LTy::Fun(dom_, ret_).into())
      }
      &LTyexp::Bit => Ok(LTy::Bit.into()),
      &LTyexp::Int => Ok(LTy::Int.into()),
      &LTyexp::Flo => Ok(LTy::Flo.into()),
      &LTyexp::Unit => Ok(LTy::Unit.into()),
      _ => Err(()),
    }
  }

  fn _mgu_exp(&mut self, query: LTyexpRef) -> Option<LTyRef> {
    let query = self._reduce_exp(query);
    self._mgu_reduced(query).ok()
  }

  fn _mgu_var(&mut self, v: LTyvar) -> Option<LTyRef> {
    // TODO
    unimplemented!();
  }

  fn _reduce_exp(&mut self, query: LTyexpRef) -> LTyexpRef {
    self.tenv.reduce_exp(query)
  }

  fn _reduce(&mut self, v: LTyvar) -> TyReduce {
    self.tenv.reduce(v)
  }

  /*fn _unify(&mut self, lv: LTyvar, rv: LTyvar) -> TyUnify {
    self.tenv.unify(lv, rv);
    // TODO: possibly risky to not do the check below.
    /*let lt = self.tenv.texp.get(&lw);
    let rt = self.tenv.texp.get(&rw);
    match (lt.map(|t| &**t), rt.map(|t| &**t)) {
      (None, None) => {
        TyUnify::OK
      }
      (None, Some(_)) => {
        TyUnify::OK
      }
      (Some(t), None) => {
        let t = t.clone().into();
        self.tenv.texp.insert(rw, t);
        self.tenv.texp.remove(&lw);
        TyUnify::OK
      }
      (Some(_), Some(_)) => {
        TyUnify::Maybe
      }
    }*/
    TyUnify::OK
  }*/

  fn _solve_eq_var(&mut self, lv: LTyvar, rv: LTyvar, root: LExprCell, work: &mut TyInfWork) -> Result<(), ()> {
    let lquery = self._reduce(lv.clone());
    let rquery = self._reduce(rv.clone());
    match (lquery, rquery) {
      (TyReduce::Exp(lquery), TyReduce::Exp(rquery)) => {
        let con = TyConRef::new(TyCon::Eq_(lquery, rquery));
        work.cons.push_back(con);
        self.solve(root, work)
      }
      _ => {
        self.tenv.unify(lv, rv);
        self.solve(root, work)
      }
    }
  }

  fn _solve_eq_exp(&mut self, v: LTyvar, query: LTyexpRef, root: LExprCell, work: &mut TyInfWork) -> Result<(), ()> {
    let lquery = self._reduce(v.clone());
    let rquery = self._reduce_exp(query.clone());
    match lquery {
      TyReduce::Exp(lquery) => {
        let con = TyConRef::new(TyCon::Eq_(lquery, rquery));
        work.cons.push_back(con);
        self.solve(root, work)
      }
      TyReduce::Var(_) => {
        self.tenv.unify_exp(v, rquery.clone());
        self.solve(root, work)
      }
    }
  }

  fn solve(&mut self, root: LExprCell, work: &mut TyInfWork) -> Result<(), ()> {
    let con = match work.cons.pop_front() {
      None => {
        /*println!("DEBUG: solve: done");
        println!("DEBUG: solve:   # vtys:");
        //println!("DEBUG: solve:   {:?}", self.root.etys);
        println!("DEBUG: solve:   {:?}", root.tree.data.borrow().vtys);
        println!("DEBUG: solve:   # db:");
        for (lv, _) in self.tenv.db.clone().iter() {
          let lw = self.tenv.head(lv.clone());
          let q = match self.tenv.texp.get(&lw) {
            None => None,
            Some(e) => Some(self._reduce_exp(e.clone())),
          };
          println!("DEBUG: solve:   {:?} => {:?} :: {:?}", lv, lw, q);
        }
        println!("DEBUG: solve:   # texp:");
        for (v, t) in self.tenv.texp.iter() {
          println!("DEBUG: solve:   {:?} => {:?}", v, t);
        }*/
        return Ok(());
      }
      Some(c) => c,
    };
    match &*con {
      &TyCon::Top => {
        self.solve(root, work)
      }
      &TyCon::Eq_(ref lquery, ref rquery) => {
        match (&**lquery, &**rquery) {
          // TODO: cases.
          (&LTyexp::Var(ref lv), &LTyexp::Var(ref rv)) => {
            self._solve_eq_var(lv.clone(), rv.clone(), root, work)
          }
          (&LTyexp::Var(ref lv), _) => {
            self._solve_eq_exp(lv.clone(), rquery.clone(), root, work)
          }
          (_, &LTyexp::Var(ref rv)) => {
            self._solve_eq_exp(rv.clone(), lquery.clone(), root, work)
          }
          (&LTyexp::Fun(ref ldom, ref lret), &LTyexp::Fun(ref rdom, ref rret)) => {
            if ldom.len() != rdom.len() {
              println!("WARNING: Eq_: fun arity mismatch");
              work.unsat_cs.push_back(con.clone());
            } else {
              for (ld, rd) in ldom.iter().zip(rdom.iter()) {
                work.cons.push_back(TyConRef::new(TyCon::Eq_(ld.clone(), rd.clone())));
              }
            }
            work.cons.push_back(TyConRef::new(TyCon::Eq_(lret.clone(), rret.clone())));
            self.solve(root, work)
          }
          (&LTyexp::Tup, &LTyexp::Tup) |
          (&LTyexp::Bit, &LTyexp::Bit) |
          (&LTyexp::Int, &LTyexp::Int) |
          (&LTyexp::Flo, &LTyexp::Flo) |
          (&LTyexp::Unit, &LTyexp::Unit) => {
            self.solve(root, work)
          }
          _ => {
            println!("WARNING: Eq_: type mismatch or unimpl");
            work.unsat_cs.push_back(con);
            self.solve(root, work)
          }
        }
      }
      &TyCon::Tagged(ref query, ref tag) => {
        // TODO
        //let query = self._reduce_exp(query.clone());
        match (&**query, tag) {
          (&LTyexp::Var(ref w), _) => {
            match self.tenv.tag.get(w) {
              None => {
                self.tenv.tag.insert_mut(w.clone(), tag.clone());
                work.defer_cs.push_back(con.clone());
              }
              Some(etag) => if etag == tag {
                work.defer_cs.push_back(con.clone());
              } else {
                work.unsat_cs.push_back(con);
              }
            }
            self.solve(root, work)
          }
          // TODO: cases.
          (_, _) => {
            work.defer_cs.push_back(con.clone());
            self.solve(root, work)
          }
        }
      }
      &TyCon::IsPtlD(ref e, ref target) => {
        let target = self._reduce_exp(target.clone());
        match &*target {
          // TODO: missing cases.
          &LTyexp::Var(_) => {
            let con = TyConRef::new(TyCon::IsPtlD(e.clone(), target.clone()));
            work.cons.push_back(con);
            self.solve(root, work)
          }
          &LTyexp::Fun(ref dom, ref ret) => {
            match &**ret {
              &LTyexp::Var(_) => {
                let con = TyConRef::new(TyCon::IsPtlD(e.clone(), target.clone()));
                work.cons.push_back(con);
                self.solve(root, work)
              }
              &LTyexp::Flo => {
                println!("DEBUG: IsPtlD: differentiating a scalar Fun (... -> Flo)");
                let con = TyConRef::new(TyCon::Tagged(e.clone(), LTytag::PtlDf(dom.len())));
                work.cons.push_back(con);
                self.solve(root, work)
              }
              _ => {
                println!("WARNING: IsPtlD: differentiating a nonscalar Fun");
                work.unsat_cs.push_back(con);
                self.solve(root, work)
              }
            }
          }
          &LTyexp::Flo => {
            println!("DEBUG: IsPtlD: differentiating a Flo");
            let con = TyConRef::new(TyCon::Tagged(e.clone(), LTytag::PtlDv));
            work.cons.push_back(con);
            self.solve(root, work)
          }
          _ => {
            println!("WARNING: IsPtlD: differentiating a nonscalar type");
            work.unsat_cs.push_back(con);
            self.solve(root, work)
          }
        }
      }
      &TyCon::IsEHashSel(ref ety, ref env_ty, ref hash) => {
        // TODO
        let env_pty = self._mgu_exp(env_ty.clone());
        match env_pty.as_ref().map(|t| &**t) {
          None => {
            /* FIXME: defer this constraint */
            self.solve(root, work)
          }
          Some(&LTy::Env(ref keys, ref hashes)) => {
            match hashes.get(hash) {
              None => {
                // FIXME
                self.solve(root, work)
              }
              Some(key_var) => {
                if !keys.contains_key(&LEnvKey::Var(key_var.clone())) {
                  // FIXME
                  self.solve(root, work)
                } else {
                  let key_ty = root.lookup_vty(key_var, self).into();
                  let con = TyConRef::new(TyCon::Eq_(ety.clone(), key_ty));
                  work.cons.push_back(con);
                  self.solve(root, work)
                }
              }
            }
          }
          Some(_) => {
            work.unsat_cs.push_back(con);
            self.solve(root, work)
          }
        }
      }
      _ => unimplemented!(),
    }
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
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

#[derive(Clone, Debug)]
pub struct LExpr {
  // TODO
  //pub up:       LLoc,
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Default)]
pub struct LTreeIndex {
  ptld:     BTreeSet<(LLoc, LLoc)>,
  adjd:     BTreeSet<(LLoc, LLoc)>,
  tngd:     BTreeSet<(LLoc, LLoc)>,
  jac:      BTreeSet<(LLoc, LLoc)>,
  adj:      BTreeSet<(LLoc, LLoc)>,
  tng:      BTreeSet<(LLoc, LLoc)>,
}

#[derive(Default)]
pub struct LTreeData {
  mexps:    Vec<LMExpr>,
  exps:     Vec<LExpr>,
  deltas:   Vec<LLoc>,
  ctxs:     HashMap<LLabel, LCtxRef>,
  etys:     HashMap<LLabel, LTyvar>,
  vtys:     HashMap<LVar, LTyvar>,
  //tyctxs:   HashMap<LLabel, LTyctxRef>,
  index:    LTreeIndex,
}

#[derive(Clone)]
pub struct LTreeView {
  root:     LLoc,
  version:  usize,
  revision: usize,
  changed:  bool,
}

impl From<LTreeViewCell> for LTreeView {
  fn from(view: LTreeViewCell) -> LTreeView {
    view.inner.borrow().clone()
  }
}

#[derive(Clone)]
pub struct LTreeViewCell {
  inner:    Rc<RefCell<LTreeView>>,
}

#[derive(Clone)]
pub struct LTreeCell {
  view: LTreeView,
  data: Rc<RefCell<LTreeData>>,
}

impl LTreeCell {
  pub fn root_loc(&self) -> LLoc {
    let data = self.data.borrow();
    let label = data.exps[self.view.root.pos].label.clone();
    assert_eq!(self.view.root.label, label);
    //LLoc::new(label, self.root)
    self.view.root.clone()
  }

  pub fn root(&self) -> LExprCell {
    let data = self.data.borrow();
    let label = data.exps[self.view.root.pos].label.clone();
    assert_eq!(self.view.root.label, label);
    LExprCell{
      view:     LTreeViewCell{inner: Rc::new(RefCell::new(self.view.clone()))},
      tree:     self.clone(),
      pos:      self.view.root.pos,
      label,
    }
  }

  pub fn end_ctx(&self) -> Option<LCtxRef> {
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
}

#[derive(Clone)]
pub struct LExprCell {
  pub view:     LTreeViewCell,
  pub tree:     LTreeCell,
  //pub data:     LTreeData,
  pub pos:      usize,
  pub label:    LLabel,
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

  fn unsafe_self_root(&self) {
    let mut view = self.view.inner.borrow_mut();
    view.root = LLoc::new(self.label.clone(), self.pos);
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

  fn unsafe_set_fresh_ety(&self, tyinf: &mut IncTyInfMachine) -> LTyvar {
    let mut tree = self.tree.data.borrow_mut();
    let ety = tyinf.fresh_tyvar();
    tree.etys.insert(self.label.clone(), ety.clone());
    ety
  }

  fn lookup_ety(&self, loc: &LLoc) -> LTyvar {
    let tree = self.tree.data.borrow();
    match tree.etys.get(&loc.label) {
      None => panic!(),
      Some(v) => v.clone(),
    }
  }

  fn lookup_vty(&self, var: &LVar, tyinf: &mut IncTyInfMachine) -> LTyvar {
    let mut tree = self.tree.data.borrow_mut();
    match tree.vtys.get(&var) {
      None => {
        let vty = tyinf.fresh_tyvar();
        tree.vtys.insert(var.clone(), vty.clone());
        vty
      }
      Some(v) => v.clone(),
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

  pub fn append(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LTerm) -> LExprCell {
    // FIXME: update the tree view.
    let new_term = (mk_term)(builder);
    let (new_pos, new_label, /*new_term*/) = {
      let root = self.tree.root_loc();
      let mut tree = self.tree.data.borrow_mut();
      let new_pos = tree.exps.len();
      let new_label = builder.fresh_label();
      match &new_term {
        &LTerm::PtlD(..) => {
          tree.index.ptld.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        &LTerm::AdjD(..) => {
          tree.index.adjd.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        &LTerm::TngD(..) => {
          tree.index.tngd.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        &LTerm::Jac(..) => {
          tree.index.jac.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        &LTerm::Adj(..) => {
          tree.index.adj.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        &LTerm::Tng(..) => {
          tree.index.tng.insert((root, LLoc::new(new_label.clone(), new_pos)));
        }
        _ => {}
      }
      tree.exps.push(LExpr{
        label:    new_label.clone(),
        term:     new_term,
      });
      (new_pos, new_label, /*new_term*/)
    };
    LExprCell{
      view:     self.view.clone(),
      tree:     self.tree.clone(),
      pos:      new_pos,
      label:    new_label,
    }
  }

  pub fn unsafe_rewrite(self, mk_term: &dyn Fn() -> LTerm) -> LExprCell {
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
  }
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
  pub term:     LTerm,
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

  pub fn jump(&self, loc: LLoc) -> LExprRef {
    // TODO
    unimplemented!();
  }
}
