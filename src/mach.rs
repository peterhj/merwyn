// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//use crate::cffi::{MCValRef};
//use crate::coll::{HTreapMap};
use crate::coll::{IHTreapMap, IHTreapSet};
use crate::ir2::{LCodeRef, /*LEnvMask,*/ LExprCell, LMExprCell, LIdent, LPat, LPatRef, LQuote, LQuoteRef, LTerm, LTermRef, LMTerm, LMTermRef, LVar};
use crate::num_util::{Checked, checked};

use packed_simd::{f64x2, f64x4};

use std::cell::{RefCell};
use std::collections::{VecDeque};
//use std::fmt::{Debug as FmtDebug, Error as FmtError, Formatter};
use std::iter::{FromIterator};
use std::ops::{Deref};
use std::rc::{Rc};

pub type MKontRef = Rc<MKont>;

pub type MEnvRef = MNamedEnvRef;

pub type MAddr = MRcAddr;
pub type MStore = MRcStore;

pub type MThunkRef = Rc<MThunk>;

#[derive(Clone)]
pub struct MValRef(Rc<MVal>);

impl Deref for MValRef {
  type Target = MVal;

  fn deref(&self) -> &MVal {
    &*self.0
  }
}

impl From<MVal> for MValRef {
  fn from(val: MVal) -> MValRef {
    MValRef(Rc::new(val))
  }
}

impl From<bool> for MValRef {
  fn from(x: bool) -> MValRef {
    MVal::Bit(x).into()
  }
}

impl From<u8> for MValRef {
  fn from(x: u8) -> MValRef {
    MVal::Oct(x).into()
  }
}

impl From<i64> for MValRef {
  fn from(x: i64) -> MValRef {
    MVal::Int(x.into()).into()
  }
}

impl From<f32> for MValRef {
  fn from(x: f32) -> MValRef {
    MVal::Flp(x as f64).into()
  }
}

impl From<f64> for MValRef {
  fn from(x: f64) -> MValRef {
    MVal::Flp(x).into()
  }
}

impl From<(f64, f64)> for MValRef {
  fn from(x: (f64, f64)) -> MValRef {
    MVal::V2Flp([x.0, x.1].into()).into()
  }
}

impl From<(f64, f64, f64)> for MValRef {
  fn from(x: (f64, f64, f64)) -> MValRef {
    MVal::V3Flp([x.0, x.1, x.2, 0.].into()).into()
  }
}

impl From<(f64, f64, f64, f64)> for MValRef {
  fn from(x: (f64, f64, f64, f64)) -> MValRef {
    MVal::V4Flp([x.0, x.1, x.2, x.3].into()).into()
  }
}

#[derive(Clone)]
pub enum MVal {
  //Box(_),
  Quo(MQuoteRef),
  Env(MEnvRef),
  Clo(MClosure),
  STup(Vec<MValRef>),
  UTup(Vec<MValRef>),
  Iota,
  Bit(bool),
  Oct(u8),
  Int(Checked<i64>),
  Flp(f64),
  V2Flp(f64x2),
  V3Flp(f64x4),
  V4Flp(f64x4),
  Bot,
}

impl MVal {
  pub fn is_undef(&self) -> bool {
    match self {
      &MVal::Bot => true,
      _ => false,
    }
  }

  pub fn as_quote(&self) -> MQuoteRef {
    match self {
      &MVal::Quo(ref quote) => quote.clone(),
      _ => panic!("machine: runtime error: MVal: expected quote"),
    }
  }
}

pub trait MValUnpack<T> {
  fn try_unpack(self) -> Option<T>;
}

impl MValUnpack<()> for MVal {
  fn try_unpack(self) -> Option<()> {
    match self {
      // TODO
      MVal::STup(elems) => {
        if elems.len() == 0 {
          Some(())
        } else {
          None
        }
      }
      MVal::UTup(_) => unimplemented!(),
      MVal::Iota => Some(()),
      _ => None,
    }
  }
}

impl MValUnpack<bool> for MVal {
  fn try_unpack(self) -> Option<bool> {
    match self {
      MVal::Bit(x) => Some(x),
      _ => None,
    }
  }
}

impl MValUnpack<u8> for MVal {
  fn try_unpack(self) -> Option<u8> {
    match self {
      MVal::Oct(x) => Some(x),
      _ => None,
    }
  }
}

impl MValUnpack<i64> for MVal {
  fn try_unpack(self) -> Option<i64> {
    match self {
      MVal::Int(x) => Some(x.into()),
      _ => None,
    }
  }
}

impl MValUnpack<f64> for MVal {
  fn try_unpack(self) -> Option<f64> {
    match self {
      MVal::Flp(x) => Some(x),
      _ => None,
    }
  }
}

impl MValUnpack<(f64, f64)> for MVal {
  fn try_unpack(self) -> Option<(f64, f64)> {
    match self {
      MVal::V2Flp(x) => Some((x.extract(0), x.extract(1))),
      _ => None,
    }
  }
}

impl MValUnpack<[f64; 2]> for MVal {
  fn try_unpack(self) -> Option<[f64; 2]> {
    match self {
      MVal::V2Flp(x) => {
        let mut y = [0.0, 0.0];
        x.write_to_slice_unaligned(&mut y);
        Some(y)
      }
      _ => None,
    }
  }
}

#[derive(Clone, Debug)]
pub enum MQuote {
  Ident(LIdent),
}

#[derive(Clone, Debug)]
pub struct MQuoteRef(Rc<MQuote>);

impl From<LQuoteRef> for MQuoteRef {
  fn from(quote: LQuoteRef) -> MQuoteRef {
    let mquote = match &*quote {
      &LQuote::Ident(ref ident) => MQuote::Ident(ident.clone()),
    };
    MQuoteRef(mquote.into())
  }
}

impl Deref for MQuoteRef {
  type Target = MQuote;

  fn deref(&self) -> &MQuote {
    &*self.0
  }
}

#[derive(Clone)]
pub enum MCode {
  Term(LExprCell),
  MTerm(LMExprCell),
  //Term(LTermRef),
  //MTerm(LMTermRef),
  //UnsafeCTerm(...),
}

#[derive(Clone)]
pub enum MLamCode {
  Term(Vec<LVar>, LExprCell),
  MTerm(usize, MLamTerm),
  //Term(Vec<LVar>, LTermRef),
  //MTerm(usize, LMTermRef),
  //UnsafeCTerm(...),
}

#[derive(Clone)]
pub struct MClosure {
  pub env:  MEnvRef,
  pub code: MLamCode,
}

/*#[derive(Clone)]
pub struct MTerm {
  // TODO
  pub fun:  Rc<dyn Fn(Vec<MValRef>) -> MValRef>,
}*/

#[derive(Clone)]
pub struct MLamTerm {
  // TODO
  pub fun:  Rc<dyn Fn(Vec<MValRef>) -> MValRef>,
}

#[repr(C)]
#[derive(Clone)]
pub struct MUnsafeCLamTerm {
  // TODO
  //pub cfun: Option<extern "C" fn (*mut MCValRef, usize) -> MCValRef>,
}

#[derive(Clone)]
pub enum MReg {
  Addr(MAddr),
  Val(MValRef),
  Term(LExprCell),
  MTerm(LMExprCell),
  //Term(LTermRef),
  //MTerm(LMTermRef),
  //UnsafeCTerm(_),
  Bot,
}

impl Default for MReg {
  fn default() -> MReg {
    MReg::Bot
  }
}

impl MReg {
  pub fn value(&self) -> bool {
    match self {
      &MReg::Val(_) => true,
      _ => false
    }
  }
}

#[derive(Clone)]
pub enum MKont<E=LExprCell> {
//pub enum MKont<E=LTermRef> {
  Ret(MEnvRef, MKontRef),
  Knt(E, MEnvRef, MKontRef),
  Thk(MAddr, MEnvRef, MKontRef),
  //EImp(LEnvMask, E, MKontRef),
  //EApp(Vec<(usize, LVar)>, E, MKontRef),
  //ERet(LEnvMask, Vec<(usize, LVar)>, MEnvRef, MKontRef),
  EImpI1(usize, E, MEnvRef, MKontRef),
  EImpV1(LVar, E, MEnvRef, MKontRef),
  EImpV(IHTreapSet<LVar>, E, MEnvRef, MKontRef),
  EConsIL(usize, E, MEnvRef, MKontRef),
  EConsVL(LVar, E, MEnvRef, MKontRef),
  EPConsIL(usize, LVar, E, MEnvRef, MKontRef),
  EPopI1(usize, LVar, MEnvRef, MKontRef),
  EPopI(Vec<usize>, Vec<(usize, LVar)>, MEnvRef, MKontRef),
  EPopV(Vec<(LVar, usize)>, MEnvRef, MKontRef),
  ESymmVl(E, MEnvRef, MKontRef),
  ESymmVr(MEnvRef, MEnvRef, MKontRef),
  App(Option<MClosure>, Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
  Mch(VecDeque<(LPatRef, E)>, MEnvRef, MKontRef),
  STup(Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
  UTup(Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
  XInc(E, MKontRef),
  Hlt,
}

impl Default for MKont {
  fn default() -> MKont {
    MKont::Hlt
  }
}

impl MKont {
  pub fn halt(&self) -> bool {
    match self {
      &MKont::Hlt => true,
      _ => false
    }
  }
}

#[derive(Clone)]
pub enum MMultiEnvRef {
  Named(MNamedEnvRef),
  Dense(MDenseEnvRef),
}

#[derive(Clone, Default)]
pub struct MDenseEnvRef {
  top:  Vec<usize>,
}

#[derive(Clone, Default)]
pub struct MNamedEnvRef {
  idxs: IHTreapMap<usize, MAddr>,
  vars: IHTreapMap<LVar, MAddr>,
}

impl MNamedEnvRef {
  pub fn lookup_idx(&self, idx: usize) -> Option<MAddr> {
    self.idxs.get(&idx).map(|thk_a| thk_a.clone())
  }

  pub fn lookup_var(&self, var: &LVar) -> Option<MAddr> {
    self.vars.get(var).map(|thk_a| thk_a.clone())
  }

  pub fn bind_idx(&self, idx: usize, addr: MAddr) -> MNamedEnvRef {
    MNamedEnvRef{
      idxs: self.idxs.insert(idx, addr),
      vars: self.vars.clone(),
    }
  }

  pub fn bind_idx_mut(&mut self, idx: usize, addr: MAddr) {
    self.idxs.insert_mut(idx, addr);
  }

  pub fn bind_var(&self, var: LVar, addr: MAddr) -> MNamedEnvRef {
    MNamedEnvRef{
      idxs: self.idxs.clone(),
      vars: self.vars.insert(var, addr),
    }
  }

  pub fn bind_var_mut(&mut self, var: LVar, addr: MAddr) {
    self.vars.insert_mut(var, addr);
  }

  pub fn unbind_var(&self, var: LVar) -> MNamedEnvRef {
    MNamedEnvRef{
      idxs: self.idxs.clone(),
      vars: self.vars.remove(&var),
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
  pub fn reset(&mut self) {
  }

  pub fn lookup(&self, thk_a: &MRcAddr) -> MThunkRef {
    thk_a.ptr.clone()
  }

  pub fn insert(&mut self, thk: MThunkRef) -> MRcAddr {
    MRcAddr{ptr: thk}
  }

  pub fn lock(&mut self, thk_a: &MRcAddr) {
    let mut data = thk_a.ptr.data.borrow_mut();
    match &mut *data {
      &mut MThunkData::Emp => {
        *data = MThunkData::Lck;
      }
      _ => panic!("machine: runtime error"),
    }
  }

  pub fn update(&mut self, thk_a: &MRcAddr, val: MValRef) {
    let mut data = thk_a.ptr.data.borrow_mut();
    match &mut *data {
      &mut MThunkData::Lck => {
        *data = MThunkData::Val(val);
      }
      _ => panic!("machine: runtime error"),
    }
  }
}

pub enum MThunkState {
  Val,
  Emp,
  Lck,
  Dst,
}

pub enum MThunkData {
  Val(MValRef),
  Emp,
  Lck,
  Dst,
}

pub struct MThunk {
  pub env:  Option<MEnvRef>,
  pub code: Option<MCode>,
  //pub lens: Vec<usize>,
  pub data: RefCell<MThunkData>,
}

impl MThunk {
  pub fn new_bound() -> MThunk {
    MThunk{
      env:  None,
      code: None,
      //lens: vec![],
      data: RefCell::new(MThunkData::Emp),
    }
  }

  /*pub fn new_lens_1(idx: usize, env: MEnvRef, code: MCode) -> MThunk {
    MThunk{
      env:  Some(env),
      code: Some(code),
      lens: vec![1],
      data: RefCell::new(MThunkData::Emp),
    }
  }*/

  pub fn new(env: MEnvRef, code: MCode) -> MThunk {
    MThunk{
      env:  Some(env),
      code: Some(code),
      //lens: vec![],
      data: RefCell::new(MThunkData::Emp),
    }
  }

  pub fn state(&self) -> MThunkState {
    match &*self.data.borrow() {
      &MThunkData::Val(_)   => MThunkState::Val,
      &MThunkData::Emp      => MThunkState::Emp,
      &MThunkData::Lck      => MThunkState::Lck,
      &MThunkData::Dst      => MThunkState::Dst,
    }
  }
}

#[derive(Default)]
pub struct MachineTuple {
  ctrl:     MReg,
  env:      MEnvRef,
  kont:     MKontRef,
}

#[derive(Default)]
pub struct MachineState {
  store:    MStore,
  brk_sig:  bool,
}

impl MachineState {
  fn _reset_sigs(&mut self) {
    self.brk_sig = false;
  }

  fn _reset(&mut self) -> MachineTuple {
    self.store.reset();
    self._reset_sigs();
    MachineTuple{
      ctrl: MReg::Bot,
      env:  MEnvRef::default(),
      kont: MKont::Hlt.into(),
    }
  }

  fn _load(&mut self, mut tuple: MachineTuple, exp: LExprCell) -> MachineTuple {
    tuple.ctrl = MReg::Term(exp);
    tuple
  }

  fn _match_rec(&mut self, val: MValRef, pat: LPatRef, env: &mut MEnvRef) -> Result<(), ()> {
    match (&*val, &*pat) {
      // TODO
      (&MVal::STup(ref elems), &LPat::STuple(ref elems_p)) => {
        if elems.len() != elems_p.len() {
          return Err(());
        }
        for (elem, elem_p) in elems.iter().zip(elems_p.iter()) {
          self._match_rec(elem.clone(), elem_p.clone(), env)?;
        }
        Ok(())
      }
      (&MVal::Iota, _) => {
        unimplemented!();
      }
      (&MVal::Bit(x), &LPat::BitLit(xp)) => {
        if x != xp {
          return Err(());
        }
        Ok(())
      }
      (&MVal::Oct(_), _) => {
        unimplemented!();
      }
      (&MVal::Int(x), &LPat::IntLit(xp)) => {
        let x: i64 = x.into();
        if x != xp {
          return Err(());
        }
        Ok(())
      }
      (_, &LPat::Var(ref var)) => {
        let thk = MThunk::new_bound().into();
        let thk_a = self.store.insert(thk);
        self.store.lock(&thk_a);
        self.store.update(&thk_a, val);
        env.bind_var_mut(var.clone(), thk_a.clone());
        Ok(())
      }
      _ => Err(())
    }
  }

  fn _match(&mut self, val: MValRef, pat: LPatRef, env: &mut MEnvRef) -> Result<(), ()> {
    self._match_rec(val, pat, env)
  }

  fn _step(&mut self, tuple: MachineTuple) -> MachineTuple {
    let MachineTuple{ctrl, env, kont} = tuple;
    let next_tuple = match ctrl {
      MReg::Addr(thk_a) => {
        let thk = self.store.lookup(&thk_a);
        match thk.state() {
          MThunkState::Val => {
            let val = match &*thk.data.borrow() {
              &MThunkData::Val(ref val) => val.clone(),
              _ => panic!("machine: bug"),
            };
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          MThunkState::Emp => {
            let (next_env, next_ctrl) = match (thk.env.clone(), thk.code.clone()) {
              (Some(thk_env), Some(MCode::Term(term))) => {
                (thk_env, MReg::Term(term))
              }
              (Some(thk_env), Some(MCode::MTerm(mterm))) => {
                (thk_env, MReg::MTerm(mterm))
              }
              _ => panic!("machine: bug"),
            };
            MachineTuple{
              ctrl: next_ctrl,
              env:  next_env,
              kont: MKont::Thk(thk_a, env, kont).into(),
            }
          }
          MThunkState::Lck => {
            panic!("machine: bug");
          }
          MThunkState::Dst => {
            panic!("machine: bug");
          }
        }
      }
      MReg::Val(val) => {
        let kont = match Rc::try_unwrap(kont) {
          Ok(kont) => kont,
          Err(k) => (*k).clone()
        };
        match kont {
          MKont::Ret(prev_env, prev_kont) => {
            MachineTuple{
              ctrl: MReg::Val(val),
              env:  prev_env,
              kont: prev_kont,
            }
          }
          MKont::Knt(term, prev_env, prev_kont) => {
            MachineTuple{
              ctrl: MReg::Term(term),
              env:  prev_env,
              kont: prev_kont,
            }
          }
          MKont::Thk(thk_a, prev_env, prev_kont) => {
            let val: MValRef = val.into();
            self.store.lock(&thk_a);
            self.store.update(&thk_a, val.clone());
            MachineTuple{
              ctrl: MReg::Val(val),
              env:  prev_env,
              kont: prev_kont,
            }
          }
          MKont::EImpI1(sel_idx, rest, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(target) => {
                let next_env = match target.lookup_idx(sel_idx) {
                  None => env,
                  Some(value) => env.bind_idx(sel_idx, value)
                };
                MachineTuple{
                  ctrl: MReg::Term(rest),
                  kont: MKont::Ret(prev_env, prev_kont).into(),
                  env:  next_env,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EImpV1(sel_var, rest, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(target) => {
                let next_env = match target.lookup_var(&sel_var) {
                  None => env,
                  Some(value) => env.bind_var(sel_var, value)
                };
                MachineTuple{
                  ctrl: MReg::Term(rest),
                  kont: MKont::Ret(prev_env, prev_kont).into(),
                  env:  next_env,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EImpV(sel_vars, rest, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                target.vars.set_intersection_mut(&sel_vars);
                let next_env = MEnvRef{
                  idxs: env.idxs,
                  vars: target.vars.left_union(&env.vars),
                };
                MachineTuple{
                  ctrl: MReg::Term(rest),
                  kont: MKont::Ret(prev_env, prev_kont).into(),
                  env:  next_env,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EConsIL(idx, value, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                let thk = MThunk::new(env, MCode::Term(value)).into();
                let thk_a = self.store.insert(thk);
                target.idxs.insert_mut(idx, thk_a);
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EConsVL(var, value, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                let thk = MThunk::new(env, MCode::Term(value)).into();
                let thk_a = self.store.insert(thk);
                target.vars.insert_mut(var, thk_a);
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EPConsIL(idx, var, value, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                let thk = MThunk::new(env, MCode::Term(value)).into();
                let thk_a = self.store.insert(thk);
                target.idxs.remove_mut(&idx);
                target.vars.insert_mut(var, thk_a);
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EPopI1(idx, var, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                match target.idxs.remove_pop_mut(&idx) {
                  None => {}
                  Some(thk_a) => {
                    target.vars.insert_mut(var, thk_a);
                  }
                }
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EPopI(rem_idxs, pop_idxs, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                for idx in rem_idxs.into_iter() {
                  target.idxs.remove_mut(&idx);
                }
                for (idx, var) in pop_idxs.into_iter() {
                  match target.idxs.remove_pop_mut(&idx) {
                    None => {}
                    Some(thk_a) => {
                      target.vars.insert_mut(var, thk_a);
                    }
                  }
                }
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::EPopV(vars, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(mut target) => {
                for (var, idx) in vars.into_iter() {
                  match target.vars.remove_pop_mut(&var) {
                    None => {}
                    Some(thk_a) => {
                      target.idxs.insert_mut(idx, thk_a);
                    }
                  }
                }
                let val = MVal::Env(target).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::ESymmVl(rhs, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(lhs) => {
                MachineTuple{
                  ctrl: MReg::Term(rhs),
                  kont: MKont::ESymmVr(lhs, prev_env, prev_kont).into(),
                  env,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::ESymmVr(mut lhs, prev_env, prev_kont) => {
            let val = match Rc::try_unwrap(val.0) {
              Ok(val) => val,
              Err(v) => (*v).clone()
            };
            match val {
              MVal::Env(rhs) => {
                lhs.vars.symmetric_difference_mut(&rhs.vars);
                let val = MVal::Env(lhs).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              _ => panic!("machine: bug"),
            }
          }
          MKont::App(closure, mut arg_vals, mut arg_terms, prev_env, prev_kont) => {
            match closure {
              None => {
                let val = match Rc::try_unwrap(val.0) {
                  Ok(val) => val,
                  Err(v) => (*v).clone()
                };
                match val {
                  MVal::Clo(closure) => {
                    match arg_terms.pop_front() {
                      None => {
                        assert!(arg_vals.is_empty(), "machine: bug");
                        match closure.code {
                          MLamCode::Term(params, body) => {
                            assert!(params.is_empty());
                            let next_ctrl = MReg::Term(body);
                            MachineTuple{
                              ctrl: next_ctrl,
                              env:  closure.env,
                              kont: MKont::Ret(prev_env, prev_kont).into(),
                            }
                          }
                          MLamCode::MTerm(arity, mlamterm) => {
                            assert_eq!(arity, 0);
                            let ret_val = (mlamterm.fun)(arg_vals);
                            MachineTuple{
                              ctrl: MReg::Val(ret_val),
                              env:  prev_env,
                              kont: prev_kont,
                            }
                          }
                        }
                      }
                      Some(next_term) => {
                        MachineTuple{
                          ctrl: MReg::Term(next_term),
                          kont: MKont::App(Some(closure), arg_vals, arg_terms, prev_env, prev_kont).into(),
                          env,
                        }
                      }
                    }
                  }
                  _ => panic!("machine: bug"),
                }
              }
              Some(closure) => {
                arg_vals.push(val);
                match arg_terms.pop_front() {
                  None => {
                    match closure.code {
                      MLamCode::Term(params, body) => {
                        assert_eq!(params.len(), arg_vals.len());
                        let mut bot = false;
                        for arg_val in arg_vals.iter() {
                          if arg_val.is_undef() {
                            bot = true;
                            break;
                          }
                        }
                        if bot {
                          MachineTuple{
                            ctrl: MReg::Val(MVal::Bot.into()),
                            env:  prev_env,
                            kont: prev_kont,
                          }
                        } else {
                          let mut next_env = closure.env;
                          for (param, arg_val) in params.into_iter().zip(arg_vals.into_iter()) {
                            let thk = MThunk::new_bound().into();
                            let thk_a = self.store.insert(thk);
                            self.store.lock(&thk_a);
                            self.store.update(&thk_a, arg_val);
                            next_env.bind_var_mut(param, thk_a);
                          }
                          MachineTuple{
                            ctrl: MReg::Term(body),
                            kont: MKont::Ret(prev_env, prev_kont).into(),
                            env:  next_env,
                          }
                        }
                      }
                      MLamCode::MTerm(arity, mlamterm) => {
                        assert_eq!(arity, arg_vals.len());
                        let mut bot = false;
                        for arg_val in arg_vals.iter() {
                          if arg_val.is_undef() {
                            bot = true;
                            break;
                          }
                        }
                        if bot {
                          MachineTuple{
                            ctrl: MReg::Val(MVal::Bot.into()),
                            env:  prev_env,
                            kont: prev_kont,
                          }
                        } else {
                          let ret_val = (mlamterm.fun)(arg_vals);
                          MachineTuple{
                            ctrl: MReg::Val(ret_val),
                            env:  prev_env,
                            kont: prev_kont,
                          }
                        }
                      }
                    }
                  }
                  Some(next_term) => {
                    MachineTuple{
                      ctrl: MReg::Term(next_term),
                      kont: MKont::App(Some(closure), arg_vals, arg_terms, prev_env, prev_kont).into(),
                      env,
                    }
                  }
                }
              }
            }
          }
          MKont::Mch(mut pat_arms, prev_env, prev_kont) => {
            match pat_arms.pop_front() {
              None => panic!("machine: bug"),
              Some((pat, arm)) => {
                let mut next_env = env.clone();
                match self._match(val.clone(), pat, &mut next_env) {
                  Err(_) => {
                    MachineTuple{
                      ctrl: MReg::Val(val),
                      kont: MKont::Mch(pat_arms, prev_env, prev_kont).into(),
                      env,
                    }
                  }
                  Ok(_) => {
                    MachineTuple{
                      ctrl: MReg::Term(arm),
                      kont: MKont::Ret(prev_env, prev_kont).into(),
                      env:  next_env,
                    }
                  }
                }
              }
            }
          }
          MKont::STup(mut vals, mut terms, prev_env, prev_kont) => {
            vals.push(val);
            match terms.pop_front() {
              None => {
                let val = MVal::STup(vals).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env:  prev_env,
                  kont: prev_kont,
                }
              }
              Some(term) => {
                MachineTuple{
                  ctrl: MReg::Term(term),
                  kont: MKont::STup(vals, terms, prev_env, prev_kont).into(),
                  env,
                }
              }
            }
          }
          _ => unimplemented!(),
        }
      }
      MReg::Term(exp) => {
        match exp.term() {
          LTerm::Top => {
            match &*kont {
              &MKont::Hlt => {
                MachineTuple{
                  ctrl: MReg::Bot,
                  kont: MKont::Hlt.into(),
                  env,
                }
              }
              &MKont::XInc(ref next_term, ref prev_kont) => {
                MachineTuple{
                  ctrl: MReg::Term(next_term.clone()),
                  kont: prev_kont.clone(),
                  env,
                }
              }
              _ => {
                panic!("machine: bug");
              }
            }
          }
          LTerm::Break(rest) => {
            self.brk_sig = true;
            MachineTuple{
              ctrl: MReg::Term(exp.jump(rest)),
              env,
              kont,
            }
          }
          /*LTerm::Export => {
            let tg_env = MEnvRef{
              idxs: Default::default(),
              vars: env.vars.clone(),
            };
            let val = MVal::Env(tg_env).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }*/
          /*LTerm::Import(free, target, rest) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EImp(free, exp.jump(rest), kont).into(),
              env,
            }
          }*/
          /*LTerm::EApply(args, target, rest) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EApp(args, exp.jump(rest), kont).into(),
              env,
            }
          }*/
          /*LTerm::EReturn(free, params, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::ERet(free, params, env.clone(), kont.into()).into(),
              env,
            }
          }*/
          LTerm::EIdxRecLazy(idx_keys) => {
            let mut target = MEnvRef::default();
            for (idx, value) in idx_keys.into_iter() {
              let thk = MThunk::new(env.clone(), MCode::Term(exp.jump(value))).into();
              let thk_a = self.store.insert(thk);
              target.bind_idx_mut(idx, thk_a.clone());
            }
            let val = MVal::Env(target).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::ERecLazy(var_keys) => {
            let mut target = MEnvRef::default();
            for (var, value) in var_keys.into_iter() {
              let thk = MThunk::new(env.clone(), MCode::Term(exp.jump(value))).into();
              let thk_a = self.store.insert(thk);
              target.bind_var_mut(var, thk_a.clone());
            }
            let val = MVal::Env(target).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::EImportIdx(sel_idx, target, rest) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EImpI1(sel_idx, exp.jump(rest), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EImportVar(sel_var, target, rest) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EImpV1(sel_var, exp.jump(rest), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EImportVars(sel_vars, target, rest) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EImpV(sel_vars, exp.jump(rest), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EConsIdxLazy(idx, value, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EConsIL(idx, exp.jump(value), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EConsVarLazy(var, value, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EConsVL(var, exp.jump(value), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EPopConsIdxLazy(idx, var, value, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EPConsIL(idx, var, exp.jump(value), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EPopIdx(var, idx, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EPopI1(var, idx, env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EPopIdxs(rem_idxs, pop_idxs, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EPopI(rem_idxs, pop_idxs, env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::EPopVars(vars, target) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EPopV(vars, env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::ESymmVars(lhs, rhs) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(lhs)),
              kont: MKont::ESymmVl(exp.jump(rhs), env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::Apply(head, args) => {
            let vals = Vec::with_capacity(args.len());
            let mut terms = VecDeque::new();
            for arg in args.into_iter() {
              terms.push_back(exp.jump(arg));
            }
            match &*kont {
              &MKont::Ret(ref prev_env, ref prev_kont) => {
                MachineTuple{
                  ctrl: MReg::Term(exp.jump(head)),
                  kont: MKont::App(None, vals, terms, prev_env.clone(), prev_kont.clone()).into(),
                  env,
                }
              }
              _ => {
                MachineTuple{
                  ctrl: MReg::Term(exp.jump(head)),
                  kont: MKont::App(None, vals, terms, env.clone(), kont).into(),
                  env,
                }
              }
            }
          }
          LTerm::Lambda(params, body) => {
            let body = exp.jump(body);
            let closure = MClosure{
              env:  env.clone(),
              code: MLamCode::Term(params, body),
            };
            let val = MVal::Clo(closure).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::FixLambda(fixvar, params, body) => {
            let body = exp.jump(body);
            let thk = MThunk::new(env.clone(), MCode::Term(exp.clone())).into();
            let thk_a = self.store.insert(thk);
            let fix_env = env.bind_var(fixvar, thk_a);
            let closure = MClosure{
              env:  fix_env,
              code: MLamCode::Term(params, body),
            };
            let val = MVal::Clo(closure).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::Let(_, var, body, rest) => {
            let body = exp.jump(body);
            let rest = exp.jump(rest);
            let thk = MThunk::new(env.clone(), MCode::Term(body.clone())).into();
            let thk_a = self.store.insert(thk);
            let next_env = env.bind_var(var, thk_a.clone());
            MachineTuple{
              ctrl: MReg::Term(body),
              kont: MKont::Thk(thk_a, env.clone(), MKont::Knt(rest, next_env, kont).into()).into(),
              env,
            }
          }
          LTerm::SLet(_, s_pat, body, rest) => {
            let mut pat_arms_ = VecDeque::new();
            pat_arms_.push_back((s_pat.into(), exp.jump(rest)));
            MachineTuple{
              ctrl: MReg::Term(exp.jump(body)),
              kont: MKont::Mch(pat_arms_, env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::Alt(_, rest) => {
            let rest = exp.jump(rest);
            MachineTuple{
              ctrl: MReg::Term(rest),
              env,
              kont,
            }
          }
          LTerm::LetAlt(_, var, _, body, rest) => {
            let body = exp.jump(body);
            let rest = exp.jump(rest);
            let thk = MThunk::new(env.clone(), MCode::Term(body.clone())).into();
            let thk_a = self.store.insert(thk);
            let next_env = env.bind_var(var, thk_a.clone());
            MachineTuple{
              ctrl: MReg::Term(body),
              kont: MKont::Thk(thk_a, env.clone(), MKont::Knt(rest, next_env, kont).into()).into(),
              env,
            }
          }
          /*LTerm::Fix(fixvar, fixbody) => {
            let fixbody = exp.jump(fixbody);
            let thk = MThunk::new(env.clone(), MCode::Term(exp.clone())).into();
            let thk_a = self.store.insert(thk);
            let next_env = env.bind_var(fixvar, thk_a);
            MachineTuple{
              ctrl: MReg::Term(fixbody),
              env:  next_env,
              kont,
            }
          }
          LTerm::SFix(fixvars, fixbody) => {
            let fixbody = exp.jump(fixbody);
            let mut next_env = env.clone();
            for (idx, fixvar) in fixvars.into_iter().enumerate() {
              let thk = MThunk::new_lens_1(idx, env.clone(), MCode::Term(exp.clone())).into();
              let thk_a = self.store.insert(thk);
              next_env.bind_var_mut(fixvar, thk_a);
            }
            MachineTuple{
              ctrl: MReg::Term(fixbody),
              env:  next_env,
              kont,
            }
          }*/
          LTerm::Match(query, pat_arms) => {
            let mut pat_arms_ = VecDeque::new();
            for (pat, arm) in pat_arms.into_iter() {
              pat_arms_.push_back((pat, exp.jump(arm)));
            }
            MachineTuple{
              ctrl: MReg::Term(exp.jump(query)),
              kont: MKont::Mch(pat_arms_, env.clone(), kont.into()).into(),
              env,
            }
          }
          LTerm::STuple(elems) => {
            match elems.len() {
              0 => {
                let val = MVal::STup(vec![]).into();
                MachineTuple{
                  ctrl: MReg::Val(val),
                  env,
                  kont,
                }
              }
              _ => {
                let vals = Vec::with_capacity(elems.len());
                let mut terms = VecDeque::new();
                for elem in elems.into_iter() {
                  terms.push_back(exp.jump(elem));
                }
                MachineTuple{
                  ctrl: MReg::Term(terms.pop_front().unwrap()),
                  kont: MKont::STup(vals, terms, env.clone(), kont.into()).into(),
                  env,
                }
              }
            }
          }
          LTerm::UTuple(elems) => {
            // TODO
            unimplemented!();
          }
          LTerm::Def(inner) => {
            // TODO
            unimplemented!();
          }
          LTerm::Quote(quote) => {
            let val = MVal::Quo(quote.into()).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::IotaLit => {
            let val = MVal::Iota.into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::BitLit(x) => {
            let val = MVal::Bit(x).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::IntLit(x) => {
            let val = MVal::Int(checked(x)).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::FlpLit(x) => {
            let val = MVal::Flp(x).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::LookupIndex(idx) => {
            let thk_a = match env.lookup_idx(idx) {
              None => panic!("machine: bug"),
              Some(a) => a,
            };
            MachineTuple{
              ctrl: MReg::Addr(thk_a),
              env,
              kont,
            }
          }
          LTerm::LookupVar(var) => {
            let thk_a = match env.lookup_var(&var) {
              None => panic!("machine: bug"),
              Some(a) => a,
            };
            MachineTuple{
              ctrl: MReg::Addr(thk_a),
              env,
              kont,
            }
          }
          LTerm::MX(mterm) => {
            MachineTuple{
              ctrl: MReg::MTerm(exp.mjump(mterm)),
              env,
              kont,
            }
          }
          //_ => unimplemented!(),
          t => panic!("machine: unimplemented term: {:?}", t),
        }
      }
      MReg::MTerm(mexp) => {
        match mexp.term() {
          LMTerm::Value(val) => {
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LMTerm::Lambda(mlamdef, mlamterm) => {
            let closure = MClosure{
              env:  env.clone(),
              code: MLamCode::MTerm(mlamdef.ar, mlamterm),
            };
            let val = MVal::Clo(closure).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          _ => panic!("machine: unimplemented m-term: <m-term>"),
        }
      }
      MReg::Bot => {
        panic!("machine: invalid state");
      }
      _ => unimplemented!(),
    };
    next_tuple
  }
}

#[derive(Default)]
pub struct Machine {
  state:    MachineState,
  tuple:    Option<MachineTuple>,
}

impl Machine {
  pub fn step(&mut self) {
    self.tuple = Some(self.state._step(self.tuple.take().unwrap()));
  }

  pub fn reset_eval(&mut self, exp: LExprCell) -> &MVal {
    self.tuple = Some(self.state._reset());
    self.tuple = Some(self.state._load(self.tuple.take().unwrap(), exp));
    loop {
      match self.tuple.as_ref() {
        None => unreachable!(),
        Some(tuple) => if tuple.ctrl.value() && tuple.kont.halt() {
          break;
        }
      }
      self.step();
    }
    match self.tuple.as_ref() {
      None => unreachable!(),
      Some(tuple) => match &tuple.ctrl {
        &MReg::Val(ref val) => val,
        _ => unreachable!(),
      }
    }
  }

  pub fn eval(&mut self) {
  }
}
