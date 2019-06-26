// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};
use crate::mach::{MAddr, MBModule, MCModule};

use rpds::{HashTrieMap, Queue, RedBlackTreeMap, Stack};

use std::cell::{RefCell};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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
  EImport(E, E),
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

  pub fn compile(&mut self, htree: Rc<HExpr>, ctx: LCtxRef) -> LModule {
    // TODO
    let tree = self._lower(htree, ctx);
    let tree = self._normalize(tree);
    let tree = self._recontext(tree);
    //let tree = self._gc(tree);
    let end_ctx = tree.end_ctx();
    LModule{
      tree: tree,
      end_ctx,
    }
  }
}

impl LBuilder {
  pub fn _lower_pat_rec(&mut self, htree: Rc<HExpr>, bindings: ()) -> () {
    // TODO
    unimplemented!();
  }

  pub fn _lower_unop(&mut self, op_name: &str, arg: Rc<HExpr>, ctx: LCtxRef, stack: &mut BTreeMap<usize, (LExpr, LCtxRef, usize)>, pos: usize) -> (LLabel, usize) {
    let op_hash = self.lookup_name(op_name);
    let op_var = match ctx.lookup_hash(op_hash) {
      Some(v) => v,
      None => {
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
      &HExpr::D(ref target) => {
        let target_pos = pos + 1;
        let (target_label, next_pos) = self._lower_rec(target.clone(), ctx.clone(), stack, target_pos);
        let target_ = LLoc::new(target_label, target_pos);
        let label = self.fresh_label();
        let e = LExpr{
          label:    label.clone(),
          term:     LTerm::D(target_)
        };
        stack.insert(pos, (e, ctx, pos));
        (label, next_pos)
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref maybe_attrs) => {
        let body_ctx = ctx.clone();
        let mut rest_ctx = ctx.clone();
        let name = match &**lhs {
          &HExpr::Ident(ref name) => name,
          _ => unimplemented!(),
        };
        let n_hash = self.lookup_name(name);
        let n_var = self.fresh_hash_var(n_hash.clone());
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
        let name_var = match ctx.lookup_hash(name_hash) {
          Some(v) => v,
          None => {
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
    self._lower_rec(htree, ctx, &mut stack, 0);
    let mut ltree = LTreeData::default();
    for (&pos, &(ref e, ref ctx, pos2)) in stack.iter() {
      assert_eq!(pos, pos2);
      assert_eq!(pos, ltree.exps.len());
      assert_eq!(pos, ltree.ctxs.len());
      ltree.exps.push(e.clone());
      ltree.ctxs.insert(e.label.clone(), ctx.clone());
    }
    LTreeCell{
      root: 0,
      next: ltree.exps.len(),
      rev:  0,
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
      &LTerm::EImport(ref env, ref body) => {
        let env = exp.lookup(env);
        let body = exp.lookup(body);
        self._normalize_name(env, &mut |this, env| {
          let body = this._normalize_term(body.clone());
          let new_exp = exp.append(this, &mut |_| LTerm::EImport(
              env.loc(),
              body.loc(),
          ));
          kont(this, new_exp)
        })
      }
      &LTerm::D(ref target) => {
        let target = exp.lookup(target);
        self._normalize_name(target, &mut |this, target| {
          let new_exp = exp.append(this, &mut |_| LTerm::D(target.loc()));
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
    let tail = tree.data.borrow().exps.len();
    let new_root = self._normalize_term(tree.root());
    let new_tail = tree.data.borrow().exps.len();
    let new_next = if new_tail > tail { new_tail } else { tree.next };
    LTreeCell{
      root: new_root.pos,
      next: new_next,
      rev:  tree.rev,
      data: tree.data.clone(),
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
      &LTerm::EImport(ref env, ref body) => {
        let env = exp.lookup(env);
        let body = exp.lookup(body);
        self._recontext_exp(env, ctx);
        // TODO
        body.unsafe_unset_ctx();
      }
      &LTerm::D(ref target) => {
        self._recontext_exp(exp.lookup(target), ctx.clone());
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

  pub fn _recontext(&mut self, tree: LTreeCell) -> LTreeCell {
    self._recontext_exp(tree.root(), LCtxRef::default());
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
  //Env(RedBlackTreeMap<LEnvKey, LTyRef>),
  Env(RedBlackTreeMap<LEnvKey, LTyRef>, RedBlackTreeMap<LHash, LVar>),
  ESel(LTyRef, LVar),
  Diff(LTyRef),
  STup(Vec<LTyRef>),
  Tup,
  Bit,
  Int,
  Flo,
  //Unit,
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

  fn _generalize(&mut self, v: LTyvar, query: LTy) -> Result<(), ()> {
    let w = self.head(v);
    match self._mgu.get(&w) {
      None => {
        self._mgu.insert(w, query);
        Ok(())
      }
      Some(result) => if result == &query {
        Ok(())
      } else {
        // FIXME: dont error if the MGU can be further generalized to be
        // compatible with the query type, on a case-by-case basis.
        Err(())
      }
    }
  }

  fn unify(&mut self, lhs: LTy, rhs: LTy) -> Result<(), ()> {
    match (lhs, rhs) {
      (LTy::Var(lv), LTy::Var(rv)) => {
        let lw = self.head(lv);
        let rw = self.head(rv);
        self.db.insert(lw, rw);
        Ok(())
      }
      (LTy::Var(v), query) => {
        self._generalize(v, query)
      }
      (query, LTy::Var(v)) => {
        self._generalize(v, query)
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
  IsACons(LVar, LTy, LTy, LTy),
  IsAConcat(LTy, LTy, LTy),
  IsAApp(Vec<(usize, LVar)>, LTyvar, LTy),
  IsERet(Vec<(usize, LVar)>, LTyvar, LTy),
  IsEHash(LTyvar, LHash, LTy),
}

struct IncTyInfMachine {
  //hyps: VecDeque<TyHyp>,
  //cons: VecDeque<TyCon>,
  sub:      TyUnionFind,
  def_cons: VecDeque<TyConRef>,
}

impl IncTyInfMachine {
  fn _gen(&mut self, tree: &LTreeCell) -> TyConRef {
    // TODO
    unimplemented!();
  }

  fn _gen_inc(&mut self, old_tree: &LTreeCell, new_tree: &LTreeCell) -> TyConRef {
    // TODO
    assert!(Rc::ptr_eq(&old_tree.data, &new_tree.data));
    unimplemented!();
  }

  fn _solve(&mut self, con: TyConRef) -> Result<usize, TyConRef> {
    match &*con {
      &TyCon::Nil => Ok(1),
      &TyCon::Cnj(ref lhs, ref rhs) => {
        let lhs_ct = self._solve(lhs.clone())?;
        let rhs_ct = self._solve(rhs.clone())?;
        Ok(lhs_ct + rhs_ct)
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
            match self.sub.unify(lty.clone(), rty.clone()) {
              Err(_) => Err(con),
              Ok(_) => Ok(1),
            }
          }
        }
      }
      &TyCon::IsAApp(ref args, ref env_tv, ref ty) => {
        match self.sub.mgu(env_tv.clone()) {
          None => {
            self.def_cons.push_back(con);
            Ok(0)
          }
          Some(LTy::Env(..)) => {
            // FIXME: do the 'AApp' type transform.
            let new_env_ty = unimplemented!();
            let new_con = TyConRef::new(TyCon::Eq(new_env_ty, ty.clone()));
            self._solve(new_con)
          }
          Some(_) => {
            Err(con)
          }
        }
      }
      &TyCon::IsERet(ref params, ref env_tv, ref ty) => {
        match self.sub.mgu(env_tv.clone()) {
          None => {
            self.def_cons.push_back(con);
            Ok(0)
          }
          Some(LTy::Env(..)) => {
            // FIXME: do the 'ERet' type transform.
            let new_env_ty = unimplemented!();
            let new_con = TyConRef::new(TyCon::Eq(new_env_ty, ty.clone()));
            self._solve(new_con)
          }
          Some(_) => {
            Err(con)
          }
        }
      }
      &TyCon::IsEHash(ref env_tv, ref hash, ref ty) => {
        match self.sub.mgu(env_tv.clone()) {
          None => {
            self.def_cons.push_back(con);
            Ok(0)
          }
          Some(LTy::Diff(tg_ty)) => {
            let tg_ty = match &*tg_ty {
              &LTy::Var(ref tg_tv) => self.sub.mgu(tg_tv.clone()),
              t => Some(t.clone()),
            };
            match tg_ty {
              None |
              Some(LTy::Fun(..)) |
              Some(LTy::Flo) => {
                self.def_cons.push_back(con);
                Ok(0)
              }
              Some(_) => {
                Err(con)
              }
            }
          }
          Some(LTy::Env(..)) => {
            // FIXME: search `env_ty` for a var that hashes to the given key.
            let env_ty: LTy = unimplemented!();
            let var = unimplemented!();
            let new_sel_ty = LTy::ESel(LTyRef::new(env_ty.clone()), var);
            let new_con = TyConRef::new(TyCon::Eq(new_sel_ty, ty.clone()));
            self._solve(new_con)
          }
          Some(_) => {
            Err(con)
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

#[derive(Clone, Debug)]
pub struct LExpr {
  pub label:    LLabel,
  pub term:     LTerm,
}

#[derive(Default)]
pub struct LTreeData {
  mexps:    Vec<LMExpr>,
  exps:     Vec<LExpr>,
  deltas:   Vec<LLoc>,
  ctxs:     HashMap<LLabel, LCtxRef>,
  etys:     HashMap<LLabel, LTyvar>,
  tyctxs:   HashMap<LLabel, LTyctxRef>,
}

#[derive(Clone)]
pub struct LTreeCell {
  root: usize,
  next: usize,
  rev:  usize,
  data: Rc<RefCell<LTreeData>>,
}

impl LTreeCell {
  pub fn root(&self) -> LExprCell {
    let data = self.data.borrow();
    let label = data.exps[self.root].label.clone();
    LExprCell{
      tree:     self.clone(),
      pos:      self.root,
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
  pub tree:     LTreeCell,
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

  pub fn unsafe_set_ctx(&self, new_ctx: LCtxRef) {
    let mut tree = self.tree.data.borrow_mut();
    tree.ctxs.insert(self.label.clone(), new_ctx);
  }

  pub fn unsafe_unset_ctx(&self) {
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
      tree:     self.tree.clone(),
      pos:      loc.pos,
      label:    loc.label.clone(),
    }
  }

  pub fn append(&self, builder: &mut LBuilder, mk_term: &mut dyn FnMut(&mut LBuilder) -> LTerm) -> LExprCell {
    let new_term = (mk_term)(builder);
    let (new_pos, new_label, /*new_term*/) = {
      let mut tree = self.tree.data.borrow_mut();
      let new_pos = tree.exps.len();
      let new_label = builder.fresh_label();
      tree.exps.push(LExpr{
        label:    new_label.clone(),
        term:     new_term,
      });
      (new_pos, new_label, /*new_term*/)
    };
    LExprCell{
      tree:     self.tree.clone(),
      pos:      new_pos,
      label:    new_label,
    }
  }

  pub fn rewrite(self, mk_term: &dyn Fn() -> LTerm) -> LExprCell {
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
