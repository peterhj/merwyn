// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::lang::{HExpr};

use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct LSymbol {
  pub id:   u64,
}

#[derive(Clone, Debug)]
pub struct LIdent {
  pub sym:  LSymbol,
  pub name: String,
}

#[derive(Clone, Debug)]
pub enum LEnvVal {
  Name(Rc<LExpr>),
  Func(Vec<LSymbol>, Rc<LExpr>),
  //Memo(Vec<LSymbol>, Rc<LExpr>),
}

#[derive(Clone, Default, Debug)]
pub struct LEnv {
  //pub bindings: HashMap<LSymbol, (usize, Rc<LExpr>)>,
  //pub syms:     Vec<(LSymbol, usize)>,
  pub bindings: HashMap<LSymbol, (usize, LEnvVal)>,
  pub syms:     Vec<LSymbol>,
}

impl LEnv {
  pub fn _bind_name(&mut self, name: LSymbol, body: Rc<LExpr>) {
    let left_idx = self.syms.len();
    self.bindings.insert(name.clone(), (left_idx, LEnvVal::Name(body)));
    self.syms.push(name);
  }

  pub fn _bind_func(&mut self, name: LSymbol, args: Vec<LSymbol>, body: Rc<LExpr>) {
    let left_idx = self.syms.len();
    self.bindings.insert(name.clone(), (left_idx, LEnvVal::Func(args, body)));
    self.syms.push(name);
  }

  pub fn fork_let(&self, name: LSymbol, body: Rc<LExpr>) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind_name(name, body);
    new_env
  }

  pub fn fork_let_func(&self, name: LSymbol, args: Vec<LSymbol>, body: Rc<LExpr>) -> LEnv {
    // TODO
    let mut new_env = self.clone();
    new_env._bind_func(name, args, body);
    new_env
  }
}

#[derive(Debug)]
pub enum LExprVal {
  Lambda(Vec<LSymbol>, LExpr),
  Apply(LExpr, Vec<LExpr>),
  LetName(LSymbol, LExpr, LExpr),
  LetFunc(LSymbol, Vec<LSymbol>, LExpr, LExpr),
  IntLit(i64),
  FloatLit(f64),
  Ident(LSymbol, String),
  //Ident(String),
}

#[derive(Clone, Debug)]
pub struct LExpr {
  pub sym:  LSymbol,
  pub val:  Rc<LExprVal>,
}

#[derive(Clone, Debug)]
pub struct LEnvExpr {
  pub env:  LEnv,
  pub sym:  LSymbol,
  pub val:  Rc<LExprVal>,
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

#[derive(Default)]
struct LSymbolMap {
  s_to_id:  HashMap<String, LSymbol>,
  id_to_s:  HashMap<LSymbol, Option<String>>,
  id_ctr:   u64,
}

impl LSymbolMap {
  pub fn insert(&mut self, name: String) {
    let _ = self.lookup(name);
  }

  pub fn lookup(&mut self, name: String) -> LSymbol {
    let &mut LSymbolMap{
      ref mut s_to_id,
      ref mut id_to_s,
      ref mut id_ctr} = self;
    s_to_id.entry(name.clone()).or_insert_with(|| {
      *id_ctr += 1;
      let id = *id_ctr;
      assert!(id != 0);
      let new_sym = LSymbol{id};
      id_to_s.insert(new_sym.clone(), Some(name));
      new_sym
    }).clone()
  }

  pub fn fresh(&mut self) -> LSymbol {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    let new_sym = LSymbol{id};
    self.id_to_s.insert(new_sym.clone(), None);
    new_sym
  }
}

pub struct LBuilder {
  symbols:  LSymbolMap,
}

impl LBuilder {
  pub fn new() -> LBuilder {
    let mut symbols = LSymbolMap::default();
    // TODO: put "standard library" into the namespace.
    symbols.insert("add".to_string());
    symbols.insert("sub".to_string());
    symbols.insert("mul".to_string());
    symbols.insert("div".to_string());
    LBuilder{
      symbols,
    }
  }

  pub fn _htree_to_ltree_lower_pass(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    match &*htree {
      &HExpr::Apply0(ref lhs) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        LExpr{sym, val: Rc::new(LExprVal::Apply(lhs, vec![]))}
      }
      &HExpr::Apply1(ref lhs, ref arg0) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let arg0 = self._htree_to_ltree_lower_pass(arg0.clone());
        LExpr{sym, val: Rc::new(LExprVal::Apply(lhs, vec![arg0]))}
      }
      &HExpr::ApplyN(ref lhs, ref args) => {
        let sym = self.symbols.fresh();
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let args: Vec<_> = args.iter().map(|arg| {
          self._htree_to_ltree_lower_pass(arg.clone())
        }).collect();
        LExpr{sym, val: Rc::new(LExprVal::Apply(lhs, args))}
      }
      &HExpr::Let(ref lhs, ref body, ref rest) => {
        match &**lhs {
          &HExpr::Ident(ref name) => {
            let sym = self.symbols.fresh();
            let name = self.symbols.lookup(name.to_string());
            let body = self._htree_to_ltree_lower_pass(body.clone());
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LExprVal::LetName(name, body, rest))}
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
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LExprVal::LetFunc(name, vec![], body, rest))}
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
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LExprVal::LetFunc(name, vec![arg0], body, rest))}
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
            let rest = self._htree_to_ltree_lower_pass(rest.clone());
            LExpr{sym, val: Rc::new(LExprVal::LetFunc(name, args_, body, rest))}
          }
          _ => {
            panic!();
          }
        }
      }
      &HExpr::Add(ref lhs, ref rhs) => {
        let sym = self.symbols.fresh();
        let op_name = "add".to_string();
        let op_sym = self.symbols.lookup(op_name.clone());
        let op = LExpr{sym: op_sym.clone(), val: Rc::new(LExprVal::Ident(op_sym, op_name))};
        let lhs = self._htree_to_ltree_lower_pass(lhs.clone());
        let rhs = self._htree_to_ltree_lower_pass(rhs.clone());
        LExpr{sym, val: Rc::new(LExprVal::Apply(op, vec![lhs, rhs]))}
      }
      &HExpr::IntLit(x) => {
        // TODO: reuse symbols for constant literals.
        let sym = self.symbols.fresh();
        LExpr{sym, val: Rc::new(LExprVal::IntLit(x))}
      }
      &HExpr::Ident(ref name) => {
        let sym = self.symbols.lookup(name.to_string());
        LExpr{sym: sym.clone(), val: Rc::new(LExprVal::Ident(sym, name.to_string()))}
      }
      _ => {
        // TODO
        unimplemented!();
      }
    }
  }

  pub fn _ltree_canonicalize_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn _ltree_unify_pass(&mut self, ltree: LExpr) -> LExpr {
    // TODO
    unimplemented!();
  }

  pub fn _ltree_env_pass(&mut self, ltree: LExpr) -> LEnvExpr {
    // TODO
    unimplemented!();
  }

  pub fn build(&mut self, htree: Rc<HExpr>) -> LExpr {
    // TODO
    htree.pre_walk(&mut |e| match e {
      &HExpr::Ident(ref name) => {
        self.symbols.insert(name.clone());
      }
      _ => {}
    });
    // TODO
    unimplemented!();
  }
}
