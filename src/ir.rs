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
  pub name: Option<String>,
  pub sym:  LSymbol,
}

#[derive(Clone, Debug)]
pub struct LEnv {
  pub bindings: HashMap<LSymbol, (usize, Rc<LExpr>)>,
  pub syms:     Vec<(LSymbol, usize)>,
}

impl LEnv {
  pub fn fork(&self, new_sym: LSymbol, val: Rc<LExpr>) -> LEnv {
    let mut new_env = self.clone();
    // TODO
    unimplemented!();
  }
}

#[derive(Clone, Debug)]
pub enum LExpr {
  Lambda(Vec<LIdent>, Rc<LExpr>),
  Apply(Rc<LExpr>, Vec<Rc<LExpr>>),
  Let(LIdent, Rc<LExpr>, Rc<LExpr>),
  LetRec(LIdent, Rc<LExpr>, Rc<LExpr>),
  IntLit(i64),
  FloatLit(f64),
  Ident(LIdent),
}

#[derive(Clone, Debug)]
pub enum LEnvExpr {
  Lambda(Vec<LIdent>, Rc<LEnvExpr>),
  Apply(Rc<LEnvExpr>, Vec<Rc<LEnvExpr>>),
  Let(LIdent, Rc<LEnvExpr>, Rc<LEnvExpr>),
  LetRec(LIdent, Rc<LEnvExpr>, Rc<LEnvExpr>),
  IntLit(i64),
  FloatLit(f64),
  Ident(LIdent),
}

#[derive(Default)]
struct LSymbolMap {
  s_to_id:  HashMap<String, LSymbol>,
  id_ctr:   u64,
}

impl LSymbolMap {
  pub fn insert(&mut self, name: String) {
    let _ = self.lookup(name);
  }

  pub fn lookup(&mut self, name: String) -> LSymbol {
    let &mut LSymbolMap{ref mut s_to_id, ref mut id_ctr} = self;
    s_to_id.entry(name).or_insert_with(|| {
      *id_ctr += 1;
      let id = *id_ctr;
      assert!(id != 0);
      LSymbol{id}
    }).clone()
  }

  pub fn anon(&mut self) -> LSymbol {
    self.id_ctr += 1;
    let id = self.id_ctr;
    assert!(id != 0);
    LSymbol{id}
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

  pub fn build(&mut self, ast: HExpr) -> LExpr {
    // TODO
    unimplemented!();
  }
}
