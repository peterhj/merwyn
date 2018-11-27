// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};

use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LSym(pub u64);

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
  Lambda(Vec<LSym>, E),
  Let(LSym, E, E),
  Fix(LSym, E),
  //LetFunc(LSym, Vec<LSym>, E, E),
  BitLit(bool),
  IntLit(i64),
  FloatLit(f64),
  Lookup,
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub sym:  LSym,
  pub val:  Rc<LTerm<LExpr>>,
}

#[derive(Clone, Debug)]
pub struct LEnvExpr {
  pub env:  LEnv,
  pub sym:  LSym,
  pub val:  Rc<LTerm<LEnvExpr>>,
}

/*#[derive(Clone, Debug)]
pub enum LEnvExpr {
  Lambda(Vec<LIdent>, Rc<LEnvExpr>),
  Apply(Rc<LEnvExpr>, Vec<Rc<LEnvExpr>>),
  Let(LIdent, Rc<LEnvExpr>, Rc<LEnvExpr>),
  //LetRec(LIdent, Rc<LEnvExpr>, Rc<LEnvExpr>),
  IntLit(i64),
  FloatLit(f64),
  Ident(LIdent),
}*/

#[derive(Clone, Debug)]
pub enum LEnvVal {
  Name(LEnvExpr),
  Func(Vec<LSym>, LEnvExpr),
  //Memo(Vec<LSym>, Rc<LExpr>),
}

#[derive(Clone, Default, Debug)]
pub struct LEnv {
  //pub bindings: HashMap<LSym, (usize, Rc<LExpr>)>,
  //pub syms:     Vec<(LSym, usize)>,
  pub bindings: HashMap<LSym, (usize, LEnvVal)>,
  pub syms:     Vec<LSym>,
}

impl LEnv {
  pub fn _bind_name(&mut self, name: LSym, body: LEnvExpr) {
    let left_idx = self.syms.len();
    self.bindings.insert(name.clone(), (left_idx, LEnvVal::Name(body)));
    self.syms.push(name);
  }

  pub fn _bind_func(&mut self, name: LSym, args: Vec<LSym>, body: LEnvExpr) {
    let left_idx = self.syms.len();
    self.bindings.insert(name.clone(), (left_idx, LEnvVal::Func(args, body)));
    self.syms.push(name);
  }

  pub fn fork_let(&self, name: LSym, body: LEnvExpr) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind_name(name, body);
    new_env
  }

  pub fn fork_let_func(&self, name: LSym, args: Vec<LSym>, body: LEnvExpr) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind_func(name, args, body);
    new_env
  }
}

pub enum LSymKey {
  Fresh,
  Name(String),
  IntLit(i64),
  FloatLit(f64),
}

#[derive(Default)]
struct LSymMap {
  s_to_id:  HashMap<String, LSym>,
  id_to_s:  HashMap<LSym, Option<String>>,
  id_ctr:   u64,
}

impl LSymMap {
  pub fn _debug_dump_syms(&self) {
    println!("DEBUG: symbols: {:?}", self.id_to_s);
  }

  pub fn insert(&mut self, name: String) {
    let _ = self.lookup(name);
  }

  pub fn lookup(&mut self, name: String) -> LSym {
    let &mut LSymMap{
      ref mut s_to_id,
      ref mut id_to_s,
      ref mut id_ctr} = self;
    s_to_id.entry(name.clone()).or_insert_with(|| {
      *id_ctr += 1;
      let id = *id_ctr;
      assert!(id != 0);
      let new_sym = LSym(id);
      id_to_s.insert(new_sym.clone(), Some(name));
      new_sym
    }).clone()
  }

  pub fn fresh(&mut self) -> LSym {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    let new_sym = LSym(id);
    self.id_to_s.insert(new_sym.clone(), None);
    new_sym
  }
}

pub struct LBuilder {
  symbols:  LSymMap,
}

impl LBuilder {
  pub fn new() -> LBuilder {
    let mut symbols = LSymMap::default();
    // TODO: put builtins and "standard library" into the namespace.
    symbols.insert("add".to_string());
    symbols.insert("sub".to_string());
    symbols.insert("mul".to_string());
    symbols.insert("div".to_string());
    // TODO: initial envionrment.
    LBuilder{
      symbols,
    }
  }

  pub fn _debug_dump_syms(&self) {
    self.symbols._debug_dump_syms();
  }

  pub fn _htree_to_ltree_lower_pass(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    match &*htree {
      &HExpr::Apply0(ref lhs) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        LExpr{sym, val: Rc::new(LTerm::Apply(lhs, vec![]))}
      }
      &HExpr::Apply1(ref lhs, ref arg0) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let arg0 = self._htree_to_ltree_lower_pass(arg0.clone());
        LExpr{sym, val: Rc::new(LTerm::Apply(lhs, vec![arg0]))}
      }
      &HExpr::ApplyN(ref lhs, ref args) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let args: Vec<_> = args.iter().map(|arg| {
          self._htree_to_ltree_lower_pass(arg.clone())
        }).collect();
        LExpr{sym, val: Rc::new(LTerm::Apply(lhs, args))}
      }
      &HExpr::Let(ref lhs, ref body, ref rest) => {
        match &**lhs {
          &HExpr::Ident(ref name) => {
            let sym = self.symbols.fresh();
            let name = self.symbols.lookup(name.to_string());
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LTerm::Let(name, body, rest))}
          }
          &HExpr::Apply0(ref lhs) => {
            let sym = self.symbols.fresh();
            let name = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.lookup(name.to_string())
              }
              _ => panic!(),
            };
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let lam_sym = self.symbols.fresh();
            let lam = LExpr{sym: lam_sym, val: Rc::new(LTerm::Lambda(vec![], body))};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LTerm::Let(name, lam, rest))}
          }
          &HExpr::Apply1(ref lhs, ref arg0) => {
            let sym = self.symbols.fresh();
            let name = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.lookup(name.to_string())
              }
              _ => panic!(),
            };
            let arg0 = match &**arg0 {
              &HExpr::Ident(ref name) => {
                self.symbols.lookup(name.to_string())
              }
              _ => panic!(),
            };
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let lam_sym = self.symbols.fresh();
            let lam = LExpr{sym: lam_sym, val: Rc::new(LTerm::Lambda(vec![arg0], body))};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LTerm::Let(name, lam, rest))}
          }
          &HExpr::ApplyN(ref lhs, ref args) => {
            let sym = self.symbols.fresh();
            let name = match &**lhs {
              &HExpr::Ident(ref name) => {
                self.symbols.lookup(name.to_string())
              }
              _ => panic!(),
            };
            let mut args_ = vec![];
            for arg in args.iter() {
              let arg = match &**arg {
                &HExpr::Ident(ref name) => {
                  self.symbols.lookup(name.to_string())
                }
                _ => panic!(),
              };
              args_.push(arg);
            }
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let lam_sym = self.symbols.fresh();
            let lam = LExpr{sym: lam_sym, val: Rc::new(LTerm::Lambda(args_, body))};
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LTerm::Let(name, lam, rest))}
          }
          _ => {
            panic!();
          }
        }
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        let sym = self.symbols.fresh();
        let op_name = "add".to_string();
        let op_sym = self.symbols.lookup(op_name);
        //let op = LExpr{sym: op_sym.clone(), val: Rc::new(LTerm::Ident(op_sym, op_name))};
        let op = LExpr{sym: op_sym, val: Rc::new(LTerm::Lookup)};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{sym, val: Rc::new(LTerm::Apply(op, vec![lhs, rhs]))}
      }
      &HExpr::BotLit => {
        // TODO: special symbol key for literal constants.
        let sym = self.symbols.fresh();
        LExpr{sym, val: Rc::new(LTerm::BitLit(false))}
      }
      &HExpr::TeeLit => {
        // TODO: special symbol key for literal constants.
        let sym = self.symbols.fresh();
        LExpr{sym, val: Rc::new(LTerm::BitLit(true))}
      }
      &HExpr::IntLit(x) => {
        // TODO: special symbol key for literal constants.
        let sym = self.symbols.fresh();
        //let sym = self.symbols.int_lit(x);
        LExpr{sym, val: Rc::new(LTerm::IntLit(x))}
      }
      &HExpr::Ident(ref name) => {
        let sym = self.symbols.lookup(name.to_string());
        LExpr{sym: sym.clone(), val: Rc::new(LTerm::Lookup)}
      }
      _ => {
        // TODO
        unimplemented!();
      }
    }
  }

  pub fn _ltree_normalize_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn _ltree_constant_fold_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn _ltree_unify_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn _ltree_env_pass_rec(&mut self, env: LEnv, ltree: LExpr) -> LEnvExpr {
    // TODO
    match &*ltree.val {
      &LTerm::Apply(ref head, ref args) => {
        let head = self._ltree_env_pass_rec(env.clone(), head.clone());
        let args = args.iter().map(|arg| self._ltree_env_pass_rec(env.clone(), arg.clone())).collect();
        LEnvExpr{
          sym:  ltree.sym.clone(),
          env:  env.clone(),
          val:  Rc::new(LTerm::Apply(
              head,
              args,
          )),
        }
      }
      //Lambda(Vec<LSym>, LExpr),
      &LTerm::Let(ref name, ref body, ref rest) => {
        let body = self._ltree_env_pass_rec(env.clone(), body.clone());
        let rest_env = env.fork_let(name.clone(), body.clone());
        let rest = self._ltree_env_pass_rec(rest_env, rest.clone());
        LEnvExpr{
          sym:  ltree.sym.clone(),
          env:  env.clone(),
          val:  Rc::new(LTerm::Let(
              name.clone(),
              body,
              rest,
          )),
        }
      }
      //LetFunc(LSym, Vec<LSym>, LExpr, LExpr),
      &LTerm::IntLit(x) => {
        LEnvExpr{
          sym:  ltree.sym.clone(),
          env:  env.clone(),
          val:  Rc::new(LTerm::IntLit(x)),
        }
      }
      //FloatLit(f64),
      &LTerm::Lookup => {
        LEnvExpr{
          sym:  ltree.sym.clone(),
          env:  env.clone(),
          val:  Rc::new(LTerm::Lookup),
        }
      }
      _ => unimplemented!(),
    }
  }

  pub fn _ltree_env_pass(&mut self, ltree: LExpr) -> LEnvExpr {
    // TODO: fill initial env.
    let env = LEnv::default();
    self._ltree_env_pass_rec(env, ltree)
  }

  pub fn _ltree_noenv_pass(&mut self, letree: LEnvExpr) -> LExpr {
    // TODO
    unimplemented!();
  }
}
