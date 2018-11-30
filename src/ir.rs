// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};

use std::collections::{HashMap};
//use std::collections::hash_map::{Entry};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LSym(pub u64);

#[derive(Clone, Debug)]
pub struct LLabel(pub u64);

/*#[derive(Clone, Debug)]
pub struct LIdent {
  pub sym:  LSym,
  pub name: String,
}*/

/*#[derive(Debug)]
pub enum LLambdaTerm {
  pub bind: Vec<LSym>,
  pub code: LExpr,
}*/

#[derive(Debug)]
pub enum LTerm<E> {
  Apply(E, Vec<E>),
  Env,
  DynEnv(LEnv),
  Lambda(Vec<LSym>, E),
  Let(LSym, E, E),
  Fix(LSym, E),
  //LetFunc(LSym, Vec<LSym>, E, E),
  BitLit(bool),
  IntLit(i64),
  FloatLit(f64),
  Lookup(LSym),
  EnvLookup(E, LSym),
  DynEnvLookup(E, String),
  Adj(E),
  AdjDyn(E),
}

#[derive(Clone, Default, Debug)]
pub struct LExprInfo {
  pub env:  Option<LEnv>,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub label:    LLabel,
  pub term:     Rc<LTerm<LExpr>>,
  pub info:     LExprInfo,
}

#[derive(Clone, Debug)]
pub enum LEnvVal {
  Name(LExpr),
  //Func(Vec<LSym>, LExpr),
  //Memo(Vec<LSym>, LExpr),
}

#[derive(Clone, Default, Debug)]
pub struct LEnv {
  //pub bindings: HashMap<LSym, (usize, Rc<LExpr>)>,
  //pub syms:     Vec<(LSym, usize)>,
  pub bindings: HashMap<LSym, (usize, LEnvVal)>,
  pub names:    HashMap<String, LSym>,
  //pub envs:     HashMap<LSym, LEnv>,
  pub syms:     Vec<LSym>,
}

impl LEnv {
  pub fn _bind(&mut self, sym: LSym, code: LExpr) {
    let left_idx = self.syms.len();
    self.bindings.insert(sym.clone(), (left_idx, LEnvVal::Name(code)));
    self.syms.push(sym);
  }

  pub fn _bind_named(&mut self, name: String, sym: LSym, body: LExpr) {
    let left_idx = self.syms.len();
    self.bindings.insert(sym.clone(), (left_idx, LEnvVal::Name(body)));
    self.names.insert(name, sym.clone());
    self.syms.push(sym);
  }

  pub fn _lookup_name(&self, name: String) -> (LSym, LExpr) {
    match self.names.get(&name) {
      Some(sym) => {
        match self.bindings.get(sym) {
          Some(&(_, LEnvVal::Name(ref code))) => {
            (sym.clone(), code.clone())
          }
          None => panic!(),
        }
      }
      None => panic!(),
    }
  }

  /*pub fn _bind_func(&mut self, name: LSym, args: Vec<LSym>, body: LExpr) {
    let left_idx = self.syms.len();
    self.bindings.insert(name.clone(), (left_idx, LEnvVal::Func(args, body)));
    self.syms.push(name);
  }*/

  pub fn fork(&self, name: LSym, body: LExpr) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind(name, body);
    new_env
  }

  /*pub fn fork_func(&self, name: LSym, args: Vec<LSym>, body: LExpr) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind_func(name, args, body);
    new_env
  }*/
}

/*pub enum LSymKey {
  Fresh,
  Name(String),
  IntLit(i64),
  FloatLit(f64),
}*/

#[derive(Debug)]
pub enum LVar {
  Fresh,
  Name(String),
  //IntLit(i64),
  //FloatLit(f64),
}

#[derive(Default)]
struct LSymMapper {
  n_to_id:  HashMap<String, LSym>,
  id_to_v:  HashMap<LSym, LVar>,
  id_ctr:   u64,
}

impl LSymMapper {
  pub fn _debug_dump_syms(&self) {
    println!("DEBUG: symbols: {:?}", self.id_to_v);
  }

  pub fn lookup_rev(&mut self, sym: LSym) -> String {
    let &mut LSymMapper{
      ref mut n_to_id,
      ref mut id_to_v,
      ref mut id_ctr} = self;
    match id_to_v.get(&sym) {
      Some(LVar::Name(ref name)) => {
        name.clone()
      }
      Some(_) => panic!(),
      None => panic!(),
    }
  }

  pub fn lookup(&mut self, name: String) -> LSym {
    let &mut LSymMapper{
      ref mut n_to_id,
      ref mut id_to_v,
      ref mut id_ctr} = self;
    n_to_id.entry(name.clone()).or_insert_with(|| {
      *id_ctr += 1;
      let id = *id_ctr;
      assert!(id != 0);
      let new_sym = LSym(id);
      id_to_v.insert(new_sym.clone(), LVar::Name(name));
      new_sym
    }).clone()
  }

  pub fn insert(&mut self, name: String) {
    let _ = self.bind(name);
  }

  pub fn bind(&mut self, name: String) -> (String, LSym, Option<LSym>) {
    let &mut LSymMapper{
      ref mut n_to_id,
      ref mut id_to_v,
      ref mut id_ctr} = self;
    *id_ctr += 1;
    let id = *id_ctr;
    assert!(id != 0);
    let new_sym = LSym(id);
    let old_sym = n_to_id.insert(name.clone(), new_sym.clone());
    id_to_v.insert(new_sym.clone(), LVar::Name(name.clone()));
    (name, new_sym, old_sym)
  }

  pub fn unbind(&mut self, name: String, new_sym: LSym, old_sym: Option<LSym>) {
    let pop_sym = if let Some(old_sym) = old_sym {
      self.n_to_id.insert(name, old_sym)
    } else {
      self.n_to_id.remove(&name)
    };
    match pop_sym {
      Some(pop_sym) => assert_eq!(pop_sym, new_sym),
      None => panic!(),
    }
  }

  /*pub fn fresh(&mut self) -> LSym {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    let new_sym = LSym(id);
    self.id_to_v.insert(new_sym.clone(), LVar::Fresh);
    new_sym
  }*/
}

#[derive(Default)]
struct LLabelCtr {
  id_ctr:   u64,
}

impl LLabelCtr {
  pub fn fresh(&mut self) -> LLabel {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    LLabel(id)
  }
}

pub struct LBuilder {
  symbols:  LSymMapper,
  labels:   LLabelCtr,
}

impl LBuilder {
  pub fn new() -> LBuilder {
    let mut symbols = LSymMapper::default();
    // TODO: put builtins and "standard library" into the namespace.
    symbols.insert("add".to_string());
    symbols.insert("sub".to_string());
    symbols.insert("mul".to_string());
    symbols.insert("div".to_string());
    let labels = LLabelCtr::default();
    // TODO: initial envionrment.
    LBuilder{
      symbols,
      labels,
    }
  }

  pub fn _debug_dump_syms(&self) {
    self.symbols._debug_dump_syms();
  }

  pub fn _htree_to_ltree_lower_pass(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    match &*htree {
      &HExpr::Apply0(ref lhs) => {
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Apply(lhs, vec![])), info: LExprInfo::default()}
      }
      &HExpr::Apply1(ref lhs, ref arg0) => {
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let arg0 = self._htree_to_ltree_lower_pass(arg0.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Apply(lhs, vec![arg0])), info: LExprInfo::default()}
      }
      &HExpr::ApplyN(ref lhs, ref args) => {
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let args: Vec<_> = args.iter().map(|arg| {
          self._htree_to_ltree_lower_pass(arg.clone())
        }).collect();
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Apply(lhs, args)), info: LExprInfo::default()}
      }
      &HExpr::Adj(ref body) => {
        // TODO
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Adj(body)), info: LExprInfo::default()}
      }
      &HExpr::AdjDyn(ref body) => {
        // TODO
        let body = self._htree_to_ltree_lower_pass(body.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::AdjDyn(body)), info: LExprInfo::default()}
      }
      &HExpr::Let(ref lhs, ref body, ref rest, ref attrs) => {
        match &**lhs {
          &HExpr::Ident(ref name) => {
            let (name, name_sym, name_oldsym) = self.symbols.bind(name.to_string());
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            self.symbols.unbind(name, name_sym.clone(), name_oldsym);
            LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Let(name_sym, body, rest)), info: LExprInfo::default()}
          }
          &HExpr::Apply0(ref lhs) => {
            let (name, name_sym, name_oldsym) = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.bind(name.to_string())
              }
              _ => panic!(),
            };
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let lam = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Lambda(vec![], body)), info: LExprInfo::default()};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            self.symbols.unbind(name, name_sym.clone(), name_oldsym);
            LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Let(name_sym, lam, rest)), info: LExprInfo::default()}
          }
          &HExpr::Apply1(ref lhs, ref arg0) => {
            let (name, name_sym, name_oldsym) = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.bind(name.to_string())
              }
              _ => panic!(),
            };
            let (arg0_, arg0_sym, arg0_oldsym) = match &**arg0 {
              &HExpr::Ident(ref name) => {
                self.symbols.bind(name.to_string())
              }
              _ => panic!(),
            };
            let body = self._htree_to_ltree_lower_pass(body.clone());
            self.symbols.unbind(arg0_, arg0_sym.clone(), arg0_oldsym);
            let lam = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Lambda(vec![arg0_sym], body)), info: LExprInfo::default()};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            self.symbols.unbind(name, name_sym.clone(), name_oldsym);
            LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Let(name_sym, lam, rest)), info: LExprInfo::default()}
          }
          &HExpr::ApplyN(ref lhs, ref args) => {
            let (name, name_sym, name_oldsym) = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.bind(name.to_string())
              }
              _ => panic!(),
            };
            let mut args_ = vec![];
            let mut args_syms = vec![];
            let mut args_oldsyms = vec![];
            for arg in args.iter() {
              let (arg_, arg_sym, arg_oldsym) = match &**arg {
                &HExpr::Ident(ref name) => {
                  self.symbols.bind(name.to_string())
                }
                _ => panic!(),
              };
              args_.push(arg_);
              args_syms.push(arg_sym);
              args_oldsyms.push(arg_oldsym);
            }
            let body = self._htree_to_ltree_lower_pass(body.clone());
            for ((arg_, arg_sym), arg_oldsym) in args_.iter().zip(args_syms.iter()).zip(args_oldsyms.iter()).rev() {
              self.symbols.unbind(arg_.clone(), arg_sym.clone(), arg_oldsym.clone());
            }
            let lam = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Lambda(args_syms, body)), info: LExprInfo::default()};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            self.symbols.unbind(name, name_sym.clone(), name_oldsym);
            LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Let(name_sym, lam, rest)), info: LExprInfo::default()}
          }
          _ => {
            panic!();
          }
        }
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        let op_name = "add".to_string();
        let op_sym = self.symbols.lookup(op_name);
        //let op = LExpr{sym: op_sym.clone(), term: Rc::new(LTerm::Ident(op_sym, op_name))};
        let op = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Lookup(op_sym)), info: LExprInfo::default()};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Apply(op, vec![lhs, rhs])), info: LExprInfo::default()}
      }
      &HExpr::BotLit => {
        // TODO: special symbol key for literal constants.
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::BitLit(false)), info: LExprInfo::default()}
      }
      &HExpr::TeeLit => {
        // TODO: special symbol key for literal constants.
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::BitLit(true)), info: LExprInfo::default()}
      }
      &HExpr::IntLit(x) => {
        // TODO: special symbol key for literal constants.
        //let sym = self.symbols.int_lit(x);
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::IntLit(x)), info: LExprInfo::default()}
      }
      &HExpr::Ident(ref name) => {
        let name_sym = self.symbols.lookup(name.to_string());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Lookup(name_sym)), info: LExprInfo::default()}
      }
      &HExpr::EnvLookup(ref lhs, ref name) => {
        /*let (name, name_sym, name_oldsym) = self.symbols.bind(name.to_string());
        //let body = self._htree_to_ltree_lower_pass(body.clone());
        let env = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Env), info: LExprInfo::default()};
        //let rest = self._htree_to_ltree_lower_pass(rest.clone());
        self.symbols.unbind(name, name_sym.clone(), name_oldsym);
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::Let(name_sym, body, rest)), info: LExprInfo::default()}*/
        // TODO
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::DynEnvLookup(lhs, name.clone())), info: LExprInfo::default()}
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
          term:     Rc::new(LTerm::Apply(
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
          term:     Rc::new(LTerm::Let(
              name.clone(),
              body,
              rest,
          )),
          info,
        }
      }
      &LTerm::IntLit(x) => {
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     Rc::new(LTerm::IntLit(x)),
          info,
        }
      }
      &LTerm::Lookup(ref lookup_sym) => {
        let mut info = ltree.info;
        info.env = Some(env);
        LExpr{
          label:    ltree.label.clone(),
          term:     Rc::new(LTerm::Lookup(lookup_sym.clone())),
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
          term:     Rc::new(LTerm::Adj(body)),
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
          term:     Rc::new(LTerm::AdjDyn(body)),
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
          term:     Rc::new(LTerm::DynEnvLookup(target, name.clone())),
          info,
        }
        /*let target = self._ltree_env_info_pass_rec(env.clone(), target.clone());
        match target.info.env {
          Some(ref tgenv) => {
            let (lk_sym, lk_code) = tgenv._lookup_name(name.clone());
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
          term:     Rc::new(LTerm::Let(
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
          term:     Rc::new(LTerm::IntLit(x)),
          info:     ltree.info,
        }
      }
      &LTerm::Lookup(ref lookup_sym) => {
        LExpr{
          label:    ltree.label.clone(),
          term:     Rc::new(LTerm::Lookup(lookup_sym.clone())),
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
        for (fvar_sym, _) in orig_env.bindings.iter() {
          let fvar_name = self.symbols.lookup_rev(fvar_sym.clone());
          let (shadow_name, shadow_sym, shadow_oldsym) = self.symbols.bind(fvar_name);
          // FIXME: next line is where we bind the adjoint expr;
          // for now, we set the adjoint to be any old literal.
          let shadow_code = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::IntLit(42424242)), info: LExprInfo::default()};
          shadow_env._bind_named(shadow_name.clone(), shadow_sym.clone(), shadow_code);
          shadow.push((shadow_name, shadow_sym, shadow_oldsym));
        }
        for (shadow_name, shadow_sym, shadow_oldsym) in shadow.into_iter().rev() {
          self.symbols.unbind(shadow_name, shadow_sym, shadow_oldsym);
        }
        let mut info = LExprInfo::default();
        info.env = Some(shadow_env);
        LExpr{
          label:    self.labels.fresh(),
          term:     Rc::new(LTerm::Env),
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
        for (fvar_sym, _) in root_env.bindings.iter() {
          let fvar_name = self.symbols.lookup_rev(fvar_sym.clone());
          let (shadow_name, shadow_sym, shadow_oldsym) = self.symbols.bind(fvar_name);
          // FIXME: next line is where we bind the adjoint expr;
          // for now, we set the adjoint to be any old literal.
          let shadow_code = LExpr{label: self.labels.fresh(), term: Rc::new(LTerm::IntLit(42424242)), info: LExprInfo::default()};
          shadow_env._bind_named(shadow_name.clone(), shadow_sym.clone(), shadow_code);
          shadow.push((shadow_name, shadow_sym, shadow_oldsym));
        }
        for (shadow_name, shadow_sym, shadow_oldsym) in shadow.into_iter().rev() {
          self.symbols.unbind(shadow_name, shadow_sym, shadow_oldsym);
        }
        LExpr{
          label:    ltree.label.clone(),
          term:     Rc::new(LTerm::DynEnv(shadow_env)),
          info:     ltree.info,
        }
      }
      &LTerm::DynEnvLookup(ref target, ref name) => {
        // TODO
        let target = self._ltree_adjoint_pass(target.clone());
        LExpr{
          label:    ltree.label.clone(),
          term:     Rc::new(LTerm::DynEnvLookup(target, name.clone())),
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
