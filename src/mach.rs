// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ir2::{LEnvKey, LExprRef, LVar};
use crate::num_util::{Checked};

use rpds::{HashTrieMap};

use std::cell::{RefCell};
use std::collections::{VecDeque};
use std::rc::{Rc};

pub type MKontRef = Rc<MKont>;

pub type MEnvRef = MNamedEnvRef;

pub type MAddr = MRcAddr;
pub type MStore = MRcStore;

pub type MValRef = Rc<MVal>;

#[repr(C)]
pub struct MCValRef {
  // TODO
}

pub enum MVal {
  Rec(MRecord),
  Clo(MClosure),
  STup(Vec<MValRef>),
  Tup(Vec<MValRef>),
  Bit(bool),
  Int(Checked<i64>),
  Flo(f64),
  //Box(_),
  //Ref(_),
  //...
}

pub struct MRecord {
  pub key_addr: HashTrieMap<LEnvKey, MAddr>,
}

pub struct MClosure {
  // TODO
  pub env:  MEnvRef,
  //pub lam:  _,
}

#[derive(Clone)]
pub struct MBModule {
  // TODO
  pub fun:  Rc<dyn Fn(Vec<MValRef>) -> MValRef>,
}

#[repr(C)]
#[derive(Clone)]
pub struct MCModule {
  // TODO
  pub cfun: Option<extern "C" fn (*mut MCValRef, usize) -> MCValRef>,
}

pub enum MReg {
  Rst,
  Val(MValRef),
  Expr(LExprRef),
  //BCode(_),
  //CCode(_),
}

impl Default for MReg {
  fn default() -> MReg {
    MReg::Rst
  }
}

pub enum MKont {
  // TODO
  Hlt,
  Thk(MAddr, LExprRef, MEnvRef, MKontRef),
  App(Option<MClosure>, Vec<MValRef>, VecDeque<LExprRef>, MEnvRef, MKontRef),
  Ret(MEnvRef, MKontRef),
  EImp(LExprRef, MEnvRef, MKontRef),
  //Mch(VecDeque<(LPat, LExpr)>, VMEnvRef, VMKontRef),
  //STup(Vec<LExpr>, Vec<VMValRef>, VMEnvRef, VMKontRef),
  //Tup(Vec<LExpr>, Vec<VMValRef>, VMEnvRef, VMKontRef),
}

impl Default for MKont {
  fn default() -> MKont {
    MKont::Hlt
  }
}

#[derive(Clone, Default)]
pub struct MNamedEnvRef {
  v_addr:   HashTrieMap<LVar, MAddr>,
}

impl MNamedEnvRef {
  pub fn lookup(&self, name: LVar) -> MAddr {
    match self.v_addr.get(&name) {
      None => {
        eprintln!("mach: runtime error: missing var");
        panic!();
      }
      Some(a) => a.clone(),
    }
  }

  pub fn bind(&self, name: LVar, addr: MAddr) -> MNamedEnvRef {
    MNamedEnvRef{
      v_addr:   self.v_addr.insert(name, addr),
    }
  }

  pub fn unbind(&self, name: LVar) -> MNamedEnvRef {
    MNamedEnvRef{
      v_addr:   self.v_addr.remove(&name),
    }
  }
}

#[derive(Clone)]
pub struct MRcAddr {
  pub ptr:  MThunkRef,
}

#[derive(Default)]
pub struct MRcStore {
}

impl MRcStore {
  pub fn lookup(&self, thk_a: MRcAddr) -> MThunkRef {
    thk_a.ptr.clone()
  }

  pub fn insert(&mut self, thk: MThunkRef) -> MRcAddr {
    MRcAddr{ptr: thk}
  }

  pub fn update(&mut self, thk_a: MRcAddr, val: MValRef) {
    // TODO
  }
}

pub type MThunkRef = Rc<MThunk>;

pub struct MThunk {
  // TODO
  pub env:  MEnvRef,
  //pub lam:  MLam,
  pub data: RefCell<MThunkData>,
}

pub enum MThunkData {
  Emp,
  Blk,
  Val(MValRef),
}

#[derive(Default)]
pub struct Machine {
  ctrl:     MReg,
  env:      MEnvRef,
  kont:     MKontRef,
  store:    MStore,
}

impl Machine {
  pub fn _step(&mut self) {
    // TODO
  }
}
