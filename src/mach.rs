// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//use crate::cffi::{MCValRef};
use crate::ir2::{LCodeRef, LEnvKeys, LPatRef, LTerm, LTermRef, LVar};
use crate::num_util::{Checked, checked};

use rpds::{HashTrieMap};

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
  Env(MEnvRef),
  Clo(MClosure),
  STup(Vec<MValRef>),
  HTup(Vec<MValRef>),
  Unit,
  Bit(bool),
  Int(Checked<i64>),
  Flp(f64),
  //Box(_),
  //Ref(_),
  //...
}

#[derive(Clone)]
pub struct MClosure {
  // TODO
  pub env:  MEnvRef,
  pub term: LTermRef,
}

#[derive(Clone)]
pub struct MLambda {
  // TODO
  pub fun:  Rc<dyn Fn(Vec<MValRef>) -> MValRef>,
}

#[repr(C)]
#[derive(Clone)]
pub struct MUnsafeCLambda {
  // TODO
  //pub cfun: Option<extern "C" fn (*mut MCValRef, usize) -> MCValRef>,
}

#[derive(Clone)]
pub enum MReg {
  Rst,
  Val(MValRef),
  Term(LTermRef),
  //BCode(_),
  //CCode(_),
}

impl Default for MReg {
  fn default() -> MReg {
    MReg::Rst
  }
}

#[derive(Clone)]
pub enum MKont {
  // TODO
  Hlt,
  XInc(LTermRef, MKontRef),
  Thk(MAddr, LTermRef, MEnvRef, MKontRef),
  EImp(LEnvKeys, LTermRef, MKontRef),
  EApp(Vec<(usize, LVar)>, LTermRef, MKontRef),
  ERet(LEnvKeys, Vec<(usize, LVar)>, MEnvRef, MKontRef),
  App(Option<MClosure>, Vec<MValRef>, VecDeque<LTermRef>, MEnvRef, MKontRef),
  Ret(MEnvRef, MKontRef),
  Mch(VecDeque<(LPatRef, LTermRef)>, MEnvRef, MKontRef),
  STup(Vec<MValRef>, VecDeque<LTermRef>, MEnvRef, MKontRef),
  HTup(Vec<MValRef>, VecDeque<LTermRef>, MEnvRef, MKontRef),
}

impl Default for MKont {
  fn default() -> MKont {
    MKont::Hlt
  }
}

#[derive(Clone, Default)]
pub struct MNamedEnvRef {
  idxs: HashTrieMap<usize, MAddr>,
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
      idxs: self.idxs.clone(),
      vars: self.vars.insert(name, addr),
    }
  }

  pub fn unbind(&self, name: LVar) -> MNamedEnvRef {
    MNamedEnvRef{
      idxs: self.idxs.clone(),
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
        *data = MThunkData::Fin(val);
      }
      &mut MThunkData::Fin(_) => panic!("machine: runtime error"),
      &mut MThunkData::Dst => panic!("machine: runtime error"),
    }
  }
}

pub struct MThunk {
  pub env:  MEnvRef,
  pub exp:  LTermRef,
  pub lens: Vec<usize>,
  pub data: RefCell<MThunkData>,
}

pub enum MThunkData {
  // TODO
  Emp,
  Blk,
  //Fut(MValRef),
  Fin(MValRef),
  //Exc,
  Dst,
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
  pub fn _step(&mut self, tuple: MachineTuple) -> MachineTuple {
    // TODO
    /*let ctrl = self.ctrl.clone();
    let env = self.env.clone();
    let kont = self.kont.clone();*/
    let MachineTuple{ctrl, env, kont} = tuple;
    let next_tuple = match ctrl {
      MReg::Rst => {
        panic!("machine: reset");
      }
      MReg::Val(val) => {
        // TODO
        let val = match Rc::try_unwrap(val) {
          Ok(v) => v,
          Err(val) => (*val).clone(),
        };
        let kont = match Rc::try_unwrap(kont) {
          Ok(k) => k,
          Err(kont) => (*kont).clone(),
        };
        match (val, kont) {
          (MVal::Clo(closure), MKont::App(None, ..)) => {
            // TODO
            unimplemented!();
          }
          (_, MKont::App(Some(_), ..)) => {
            // TODO
            unimplemented!();
          }
          (_, MKont::App(..)) => {
            panic!("machine: bug");
          }
          (val, MKont::Ret(prev_env, prev_kont)) => {
            MachineTuple{
              ctrl: MReg::Val(val.into()),
              env:  prev_env,
              kont: prev_kont,
            }
          }
          (MVal::Env(tg_env), MKont::EImp(free, rest, prev_kont)) => {
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
          }
          (MVal::Env(tg_env), MKont::EApp(args, rest, prev_kont)) => {
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
          }
          (MVal::Env(mut tg_env), MKont::ERet(_free, params, prev_env, prev_kont)) => {
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
          }
          _ => unimplemented!(),
        }
      }
      MReg::Term(exp) => {
        // TODO
        let kont = match Rc::try_unwrap(kont) {
          Ok(k) => k,
          Err(kont) => (*kont).clone(),
        };
        match (exp.term(), kont) {
          (LTerm::End, MKont::Hlt) => {
            MachineTuple{
              ctrl: MReg::Rst,
              kont: MKont::Hlt.into(),
              env,
            }
          }
          (LTerm::End, MKont::XInc(next_exp, prev_kont)) => {
            MachineTuple{
              ctrl: MReg::Term(next_exp),
              kont: prev_kont,
              env,
            }
          }
          (LTerm::End, _) => {
            panic!("machine: bug");
          }
          (LTerm::Export, kont) => {
            let val = MVal::Env(MEnvRef{
              idxs: HashTrieMap::default(),
              vars: env.vars.clone(),
            }).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont: kont.into(),
            }
          }
          (LTerm::Import(free, target, rest), kont) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EImp(free, exp.jump(rest), kont.into()).into(),
              env,
            }
          }
          (LTerm::EApply(args, target, rest), kont) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::EApp(args, exp.jump(rest), kont.into()).into(),
              env,
            }
          }
          /*(LTerm::EReturn(free, params, target), kont) => {
            MachineTuple{
              ctrl: MReg::Term(exp.jump(target)),
              kont: MKont::ERet(free, params, env.clone(), kont.into()).into(),
              env,
            }
          }*/
          (LTerm::Apply(head, args), MKont::Ret(prev_env, prev_kont)) => {
            // TODO
            MachineTuple{
              ctrl: MReg::Term(exp.jump(head)),
              kont: MKont::App(None, Vec::new(), VecDeque::new(), prev_env, prev_kont).into(),
              env,
            }
          }
          (LTerm::Apply(head, args), kont) => {
            // TODO
            MachineTuple{
              ctrl: MReg::Term(exp.jump(head)),
              kont: MKont::App(None, Vec::new(), VecDeque::new(), env.clone(), kont.into()).into(),
              env,
            }
          }
          (LTerm::Lambda(params, body), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::Let(name, body, rest), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::Fix(fixname, fixbody), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::SFix(fixnames, fixbody), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::Match(query, pat_arms), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::STuple(elems), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::Tuple(elems), _) => {
            // TODO
            unimplemented!();
          }
          (LTerm::UnitLit, kont) => {
            let val = MVal::Unit.into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont: kont.into(),
            }
          }
          (LTerm::BitLit(x), kont) => {
            let val = MVal::Bit(x).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont: kont.into(),
            }
          }
          (LTerm::IntLit(x), kont) => {
            let val = MVal::Int(checked(x)).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont: kont.into(),
            }
          }
          (LTerm::FlpLit(x), kont) => {
            let val = MVal::Flp(x).into();
            MachineTuple{
              ctrl: MReg::Val(val),
              env,
              kont: kont.into(),
            }
          }
          (LTerm::Lookup(name), _) => {
            // TODO
            unimplemented!();
          }
          _ => unimplemented!(),
        }
      }
      _ => unimplemented!(),
    };
    next_tuple
  }

  pub fn eval(&mut self, code: LCodeRef) {
    // TODO
  }
}

#[derive(Default)]
pub struct Machine {
  state:    MachineState,
  tuple:    MachineTuple,
}

impl Machine {
  pub fn _step(mut self) -> Machine {
    self.tuple = self.state._step(self.tuple);
    self
  }
}
