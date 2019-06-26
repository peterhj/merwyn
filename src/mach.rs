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

pub type MThunkRef = Rc<MThunk>;

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
  pub keys: HashTrieMap<LEnvKey, MAddr>,
}

pub struct MClosure {
  // TODO
  pub env:  MEnvRef,
  pub exp:  LExprRef,
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

#[derive(Clone)]
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
  vars: HashTrieMap<LVar, MAddr>,
}

impl MNamedEnvRef {
  pub fn lookup(&self, name: LVar) -> MAddr {
    match self.vars.get(&name) {
      None => {
        eprintln!("mach: runtime error: missing var");
        panic!();
      }
      Some(a) => a.clone(),
    }
  }

  pub fn bind(&self, name: LVar, addr: MAddr) -> MNamedEnvRef {
    MNamedEnvRef{
      vars: self.vars.insert(name, addr),
    }
  }

  pub fn unbind(&self, name: LVar) -> MNamedEnvRef {
    MNamedEnvRef{
      vars: self.vars.remove(&name),
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
    let mut data = thk_a.ptr.data.borrow_mut();
    match &mut *data {
      &mut MThunkData::Emp => panic!("machine: runtime error"),
      &mut MThunkData::Blk => {
        *data = MThunkData::Val(val);
      }
      &mut MThunkData::Val(_) => panic!("machine: runtime error"),
    }
  }
}

pub struct MThunk {
  pub env:  MEnvRef,
  pub exp:  LExprRef,
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
    let ctrl = self.ctrl.clone();
    let env = self.env.clone();
    let kont = self.kont.clone();
    /*let (next_ctrl, next_env, next_kont) =*/ match ctrl {
      MReg::Rst => {
        panic!("machine: reset");
      }
      MReg::Val(val) => {
        // TODO
        unimplemented!();
      }
      MReg::Expr(exp) => {
        // TODO
        unimplemented!();
      }
      _ => unimplemented!(),
    };
  }
}
