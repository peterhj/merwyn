// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//use crate::cffi::{MCValRef};
use crate::coll::hashtreap::{HashTreapMap};
use crate::ir2::{LCodeRef, LEnvKeys, LExprCell, LMExprCell, LPatRef, LTerm, LTermRef, LMTermRef, LVar};
use crate::num_util::{Checked, checked};

//use rpds::{HashTrieMap};

use std::cell::{RefCell};
use std::collections::{VecDeque};
use std::iter::{FromIterator};
use std::rc::{Rc};

pub type MKontRef = Rc<MKont>;

pub type MEnvRef = MNamedEnvRef;

pub type MAddr = MRcAddr;
pub type MStore = MRcStore;

pub type MValRef = Rc<MVal>;

pub type MThunkRef = Rc<MThunk>;

#[derive(Clone)]
pub enum MVal {
  //Box(_),
  Env(MEnvRef),
  Clo(MClosure),
  STup(Vec<MValRef>),
  HTup(Vec<MValRef>),
  Bit(bool),
  Int(Checked<i64>),
  Flp(f64),
  Unit,
}

pub trait MValUnpack<T> {
  fn try_unpack(self) -> Option<T>;
}

impl MValUnpack<bool> for MVal {
  fn try_unpack(self) -> Option<bool> {
    match self {
      MVal::Bit(x) => Some(x),
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

impl MValUnpack<()> for MVal {
  fn try_unpack(self) -> Option<()> {
    match self {
      // TODO
      MVal::STup(_) => unimplemented!(),
      MVal::HTup(_) => unimplemented!(),
      MVal::Unit => Some(()),
      _ => None,
    }
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
  MTerm(usize, LMExprCell),
  //Term(Vec<LVar>, LTermRef),
  //MTerm(usize, LMTermRef),
  //UnsafeCTerm(...),
}

#[derive(Clone)]
pub struct MClosure {
  pub env:  MEnvRef,
  pub code: MLamCode,
}

#[derive(Clone)]
pub struct MTerm {
  // TODO
  pub fun:  Rc<dyn Fn(Vec<MValRef>) -> MValRef>,
}

#[repr(C)]
#[derive(Clone)]
pub struct MUnsafeCTerm {
  // TODO
  //pub cfun: Option<extern "C" fn (*mut MCValRef, usize) -> MCValRef>,
}

#[derive(Clone)]
pub enum MReg {
  Rst,
  Val(MValRef),
  Term(LExprCell),
  MTerm(LMExprCell),
  //Term(LTermRef),
  //MTerm(LMTermRef),
  //UnsafeCTerm(_),
}

impl Default for MReg {
  fn default() -> MReg {
    MReg::Rst
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
  App(Option<MClosure>, Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
  //EImp(LEnvKeys, E, MKontRef),
  //EApp(Vec<(usize, LVar)>, E, MKontRef),
  //ERet(LEnvKeys, Vec<(usize, LVar)>, MEnvRef, MKontRef),
  Mch(VecDeque<(LPatRef, E)>, MEnvRef, MKontRef),
  STup(Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
  HTup(Vec<MValRef>, VecDeque<E>, MEnvRef, MKontRef),
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
  //idxs: HashTrieMap<usize, MAddr>,
  //vars: HashTrieMap<LVar, MAddr>,
  idxs: HashTreapMap<usize, MAddr>,
  vars: HashTreapMap<LVar, MAddr>,
}

impl MNamedEnvRef {
  pub fn lookup(&self, var: LVar) -> MAddr {
    match self.vars.get(&var) {
      None => {
        eprintln!("mach: runtime error: missing var");
        panic!();
      }
      Some(a) => a.clone(),
    }
  }

  pub fn bind(&self, var: LVar, addr: MAddr) -> MNamedEnvRef {
    MNamedEnvRef{
      idxs: self.idxs.clone(),
      vars: self.vars.insert(var, addr),
    }
  }

  pub fn bind_mut(&mut self, var: LVar, addr: MAddr) {
    self.vars.insert_mut(var, addr);
  }

  pub fn unbind(&self, var: LVar) -> MNamedEnvRef {
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
  pub lens: Vec<usize>,
  pub data: RefCell<MThunkData>,
}

impl MThunk {
  pub fn new_bound() -> MThunk {
    MThunk{
      env:  None,
      code: None,
      lens: vec![],
      data: RefCell::new(MThunkData::Emp),
    }
  }

  pub fn new_lens_1(idx: usize, env: MEnvRef, code: MCode) -> MThunk {
    MThunk{
      env:  Some(env),
      code: Some(code),
      lens: vec![1],
      data: RefCell::new(MThunkData::Emp),
    }
  }

  pub fn new(env: MEnvRef, code: MCode) -> MThunk {
    MThunk{
      env:  Some(env),
      code: Some(code),
      lens: vec![],
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
}

impl MachineState {
  pub fn _reset(&mut self, exp: LExprCell) -> MachineTuple {
    self.store.reset();
    MachineTuple{
      ctrl: MReg::Term(exp),
      env:  MEnvRef::default(),
      kont: MKont::Hlt.into(),
    }
  }

  pub fn _step(&mut self, tuple: MachineTuple) -> MachineTuple {
    let MachineTuple{ctrl, env, kont} = tuple;
    let next_tuple = match ctrl {
      MReg::Rst => {
        panic!("machine: reset");
      }
      MReg::Val(val) => {
        let kont = match Rc::try_unwrap(kont) {
          Ok(k) => k,
          Err(kont) => (*kont).clone(),
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
              kont: prev_kont.into(),
            }
          }
          MKont::App(closure, mut arg_vals, mut arg_terms, prev_env, prev_kont) => {
            match closure {
              None => {
                let val = match Rc::try_unwrap(val) {
                  Ok(v) => v,
                  Err(val) => (*val).clone(),
                };
                match val {
                  MVal::Clo(closure) => {
                    match arg_terms.pop_front() {
                      Some(next_term) => {
                        MachineTuple{
                          ctrl: MReg::Term(next_term),
                          kont: MKont::App(Some(closure), arg_vals, arg_terms, prev_env.clone(), prev_kont.into()).into(),
                          env:  prev_env,
                        }
                      }
                      None => {
                        assert!(arg_vals.is_empty(), "machine: bug");
                        let next_ctrl = match closure.code {
                          MLamCode::Term(_, body) => MReg::Term(body),
                          MLamCode::MTerm(_, mbody) => MReg::MTerm(mbody),
                        };
                        MachineTuple{
                          ctrl: next_ctrl,
                          kont: MKont::Ret(prev_env.clone(), prev_kont.into()).into(),
                          env:  prev_env,
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
                  Some(next_term) => {
                    MachineTuple{
                      ctrl: MReg::Term(next_term),
                      kont: MKont::App(Some(closure), arg_vals, arg_terms, prev_env.clone(), prev_kont.into()).into(),
                      env:  prev_env,
                    }
                  }
                  None => {
                    match closure.code {
                      MLamCode::Term(params, body) => {
                        let mut next_env = closure.env.clone();
                        for (p, p_val) in params.into_iter().zip(arg_vals.into_iter()) {
                          let thk = MThunk::new_bound().into();
                          let thk_a = self.store.insert(thk);
                          self.store.lock(&thk_a);
                          self.store.update(&thk_a, p_val);
                          next_env = next_env.bind(p, thk_a);
                        }
                        MachineTuple{
                          ctrl: MReg::Term(body),
                          kont: MKont::Ret(prev_env.clone(), prev_kont.into()).into(),
                          env:  next_env,
                        }
                      }
                      MLamCode::MTerm(arity, _) => {
                        // FIXME
                        assert_eq!(arity, arg_vals.len());
                        unimplemented!();
                      }
                    }
                  }
                }
              }
            }
          }
          /*(MVal::Env(tg_env), MKont::EImp(free, rest, prev_kont)) => {
            let next_env = match free {
              LEnvKeys::Empty => MEnvRef::default(),
              LEnvKeys::Var(var) => {
                let mut next_env = MEnvRef::default();
                match tg_env.vars.get(&var) {
                  None => {}
                  Some(addr) => {
                    let addr = addr.clone();
                    next_env.vars.insert_mut(var, addr);
                  }
                }
                next_env
              }
              /*LEnvKeys::List(/*idxs,*/ vars) => {
                let mut next_env = MEnvRef::default();
                for var in vars.into_iter() {
                  match tg_env.vars.get(&var) {
                    None => {}
                    Some(addr) => {
                      let addr = addr.clone();
                      next_env.vars.insert_mut(var, addr);
                    }
                  }
                }
                next_env
              }*/
              LEnvKeys::Set(_) => {
                // TODO
                unimplemented!();
              }
              LEnvKeys::All => tg_env.clone()
            };
            MachineTuple{
              ctrl: MReg::Term(rest),
              env:  next_env,
              kont: prev_kont,
            }
          }
          (_, MKont::EImp(..)) => {
            panic!("machine: bug");
          }*/
          /*(MVal::Env(tg_env), MKont::EApp(args, rest, prev_kont)) => {
            let mut next_env = MEnvRef::default();
            for (idx, key) in args.into_iter() {
              match tg_env.idxs.get(&idx) {
                None => {}
                Some(addr) => {
                  let addr = addr.clone();
                  next_env.vars.insert_mut(key, addr);
                }
              }
            }
            MachineTuple{
              ctrl: MReg::Term(rest),
              env:  next_env,
              kont: prev_kont,
            }
          }
          (_, MKont::EApp(..)) => {
            panic!("machine: bug");
          }*/
          /*(MVal::Env(mut tg_env), MKont::ERet(_free, params, prev_env, prev_kont)) => {
            // TODO: keep `free` keys.
            for (idx, key) in params.into_iter() {
              match tg_env.vars.get(&key) {
                None => {}
                Some(addr) => {
                  let addr = addr.clone();
                  tg_env.vars.remove_mut(&key);
                  tg_env.idxs.insert_mut(idx, addr);
                }
              }
            }
            let val = MVal::Env(tg_env).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env:  prev_env,
              kont: prev_kont,
            }
          }
          (_, MKont::ERet(..)) => {
            panic!("machine: bug");
          }*/
          _ => unimplemented!(),
        }
      }
      MReg::Term(exp) => {
        match exp.term() {
          LTerm::End => {
            match &*kont {
              &MKont::Hlt => {
                MachineTuple{
                  ctrl: MReg::Rst,
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
          LTerm::Export => {
            let val = MVal::Env(MEnvRef{
              idxs: Default::default(),
              vars: env.vars.clone(),
            }).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
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
          LTerm::Apply(head, args) => {
            match &*kont {
              &MKont::Ret(ref prev_env, ref prev_kont) => {
                MachineTuple{
                  ctrl: MReg::Term(exp.jump(head)),
                  kont: MKont::App(None, Vec::new(), VecDeque::new(), prev_env.clone(), prev_kont.clone()).into(),
                  env,
                }
              }
              _ => {
                MachineTuple{
                  ctrl: MReg::Term(exp.jump(head)),
                  kont: MKont::App(None, Vec::new(), VecDeque::new(), env.clone(), kont).into(),
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
          LTerm::Let(var, body, rest) => {
            let body = exp.jump(body);
            let rest = exp.jump(rest);
            let thk = MThunk::new(env.clone(), MCode::Term(body.clone())).into();
            let thk_a = self.store.insert(thk);
            let next_env = env.bind(var, thk_a.clone());
            MachineTuple{
              ctrl: MReg::Term(body),
              kont: MKont::Thk(thk_a, env.clone(), MKont::Knt(rest, next_env, kont).into()).into(),
              env,
            }
          }
          LTerm::Fix(fixvar, fixbody) => {
            let fixbody = exp.jump(fixbody);
            let thk = MThunk::new(env.clone(), MCode::Term(exp.clone())).into();
            let thk_a = self.store.insert(thk);
            let next_env = env.bind(fixvar, thk_a);
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
              next_env.bind_mut(fixvar, thk_a);
            }
            MachineTuple{
              ctrl: MReg::Term(fixbody),
              env:  next_env,
              kont,
            }
          }
          LTerm::Match(query, pat_arms) => {
            // TODO
            unimplemented!();
          }
          LTerm::STuple(elems) => {
            // TODO
            unimplemented!();
          }
          LTerm::Tuple(elems) => {
            // TODO
            unimplemented!();
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
          LTerm::UnitLit => {
            let val = MVal::Unit.into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont,
            }
          }
          LTerm::Lookup(var) => {
            let thk_a = env.lookup(var);
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
                  (Some(e), Some(MCode::Term(term))) => (e, MReg::Term(term)),
                  (Some(e), Some(MCode::MTerm(mterm))) => (e, MReg::MTerm(mterm)),
                  _ => panic!("machine: bug"),
                };
                MachineTuple{
                  ctrl: next_ctrl,
                  env:  next_env,
                  kont: MKont::Thk(thk_a, env.clone(), kont).into(),
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
          // TODO
          LTerm::MX(mterm) => {
            let mterm = exp.mjump(mterm);
            MachineTuple{
              ctrl: MReg::MTerm(mterm),
              env,
              kont,
            }
          }
          _ => unimplemented!(),
        }
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
    self.tuple = Some(self.state._reset(exp));
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
