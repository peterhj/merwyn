// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::cfg::{Config};
use crate::ir::{LDef, LEnv, LExpr, LTerm, LVar};
use crate::rngs::{HwRng};

use rand::prelude::*;
use rand_chacha::{ChaChaRng};
use vertreap::{VertreapMap};

use std::any::{Any};
use std::cell::{RefCell, RefMut};
use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VMAddr {
  pub raw:  u64,
}

pub struct VMBox {
  // TODO
  ival: Rc<dyn Any>,
}

#[derive(Clone)]
pub struct VMBoxCode {
  // TODO
  ifun: Rc<dyn Fn(usize, VMEnvRef) -> VMValRef>,
}

pub struct VMModule {
  pub env:  VMEnvRef,
}

pub enum VMLamCode {
  Box_(VMBoxCode),
  Expr(LExpr),
}

pub struct VMLam {
  pub bind: Vec<LVar>,
  pub code: LExpr,
  //pub code: VMLamCode,
}

pub struct VMClosure {
  pub env:  VMEnvRef,
  pub lam:  VMLam,
}

pub enum VMThunkState {
  Emp,
  Blk,
  Ret,
}

pub enum VMThunkSlot {
  Emp,
  Blk,
  Ret(VMValRef),
}

pub type VMThunkRef = Rc<VMThunk>;

pub struct VMThunk {
  pub env:  VMEnvRef,
  pub lam:  VMLam,
  pub slot: RefCell<VMThunkSlot>,
}

impl VMThunk {
  pub fn new(lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
    }
  }

  pub fn new_blkhole(lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Blk),
    }
  }

  pub fn state(&self) -> VMThunkState {
    let mslot = self.slot.borrow();
    match &*mslot {
      &VMThunkSlot::Emp => VMThunkState::Emp,
      &VMThunkSlot::Blk => VMThunkState::Blk,
      &VMThunkSlot::Ret(_) => VMThunkState::Ret,
    }
  }

  pub fn _prep_update(&self) {
    let mut mslot = self.slot.borrow_mut();
    *mslot = VMThunkSlot::Blk;
  }

  pub fn _kill(&self) {
    let mut mslot = self.slot.borrow_mut();
    *mslot = VMThunkSlot::Emp;
  }
}

pub type VMValRef = Rc<VMVal>;

//#[derive(Debug)]
pub enum VMVal {
  //Code(LExpr),
  Env(VMEnvRef),
  DEnv(LEnv),
  Clo(VMClosure),
  Box_(VMBox),
  Bit(bool),
  Int(i64),
  Flo(f64),
  Tup,
  //Thk,
}

#[derive(Clone)]
pub enum VMReg {
  Uninit,
  BCode(VMBoxCode, usize),
  Code(LExpr),
  MVal(VMValRef),
}

#[derive(Clone, Default)]
pub struct VMEnvRef {
  // TODO
  //mval_map: HashMap<LVar, VMValRef>,
  //addr_map: HashMap<LVar, VMAddr>,
  addr_map: VertreapMap<LVar, VMAddr>,
}

impl VMEnvRef {
  //pub fn lookup(&self, name: LVar) -> VMValRef {
  pub fn lookup(&self, name: LVar) -> VMAddr {
    //match self.mval_map.get(&name) {
    //match self.addr_map.get(&name) {
    match self.addr_map.find(&name) {
      None => panic!(),
      //Some(mval) => mval.clone(),
      //Some(addr) => addr.clone(),
      Some(kv) => kv.v.clone(),
    }
  }

  //pub fn insert(&self, name: LVar, mval: VMValRef) -> VMEnvRef {
  pub fn insert(&self, name: LVar, addr: VMAddr) -> VMEnvRef {
    // TODO
    /*let mut new_env = self.clone();
    //new_env.mval_map.insert(name, mval);
    new_env.addr_map.insert(name, addr);
    new_env*/
    VMEnvRef{
      addr_map: self.addr_map.append(name, addr),
    }
  }
}

pub type VMKontRef = Rc<VMKont>;

pub enum VMKont {
  Stop,
  //Next(VMKontRef),
  Lkd(String, VMEnvRef, VMKontRef),
  Thk1(VMAddr, VMLam, VMEnvRef, VMKontRef),
  App0(VMEnvRef, VMKontRef),
  //App1(VMClosure, VMKontRef),
  App1(VMLam, VMEnvRef, VMKontRef),
  // TODO: like "arg" and "fun" konts but w/ arity.
  App(usize, Vec<LExpr>, Option<VMLam>, Vec<VMValRef>, VMEnvRef, VMKontRef),
  ApBc(VMEnvRef, VMKontRef),
  Swh(LExpr, LExpr, VMEnvRef, VMKontRef),
  //Frc(LVar, VMEnvRef, VMKontRef),
  // TODO: "ret" kont may be unnecessary.
  //Ret(VMValRef, VMKontRef),
}

impl Default for VMKont {
  fn default() -> VMKont {
    VMKont::Stop
  }
}

/*impl VMKont {
  pub fn is_terminal(&self) -> bool {
    // TODO: version below assumes a "ret" kont.
    match self {
      &VMKont::Ret(_, ref next) => {
        match &**next {
          &VMKont::Stop => true,
          _ => false,
        }
      }
      _ => false,
    }
  }
}*/

#[derive(Default)]
pub struct VMStore {
  // TODO
  //mval_map: HashMap<VMAddr, VMValRef>,
  mthk_map: HashMap<VMAddr, VMThunkRef>,
  addr_ctr: u64,
}

impl VMStore {
  pub fn nil_addr(&mut self) -> VMAddr {
    VMAddr{raw: 0}
  }

  pub fn fresh_addr(&mut self) -> VMAddr {
    let new_addr = self.addr_ctr + 1;
    assert!(new_addr != 0);
    self.addr_ctr += 1;
    VMAddr{raw: new_addr}
  }

  //pub fn lookup(&self, addr: VMAddr) -> VMValRef {
  pub fn lookup(&self, addr: VMAddr) -> VMThunkRef {
    //match self.mval_map.get(&addr) {
    match self.mthk_map.get(&addr) {
      None => panic!(),
      //Some(mval) => mval.clone(),
      Some(mthk) => mthk.clone(),
    }
  }

  //pub fn insert_new(&mut self, addr: VMAddr, mval: VMValRef) {
  pub fn insert_new(&mut self, addr: VMAddr, mthk: VMThunkRef) {
    //assert!(self.mval_map.insert(addr, mval).is_none());
    assert!(self.mthk_map.insert(addr, mthk).is_none());
  }

  pub fn update(&mut self, addr: VMAddr, mval: VMValRef) {
    // TODO
    match self.mthk_map.get(&addr) {
      None => panic!(),
      Some(mthk) => {
        match mthk.state() {
          VMThunkState::Emp => {
            println!("WARNING: updating an empty thunk");
            let mut mslot = mthk.slot.borrow_mut();
            *mslot = VMThunkSlot::Ret(mval);
          }
          VMThunkState::Blk => {
            let mut mslot = mthk.slot.borrow_mut();
            *mslot = VMThunkSlot::Ret(mval);
          }
          VMThunkState::Ret => {
            panic!();
          }
        }
      }
    }
  }
}

pub struct MState {
  // TODO
  pub rng:      ChaChaRng,
}

#[derive(Clone)]
pub struct MRngSaveState {
  pub seed:     [u8; 32],
  pub wpos:     u128,
  pub seqnr:    u64,
}

impl Default for MRngSaveState {
  fn default() -> Self {
    let seed = HwRng::default().gen();
    //println!("DEBUG: rng save state: default seed: {:?}", seed);
    MRngSaveState{
      seed:     seed,
      wpos:     0,
      seqnr:    0,
    }
  }
}

impl MRngSaveState {
  pub fn seek(&self, seqnr: u64) -> MRngSaveState {
    MRngSaveState{
      seed:     self.seed.clone(),
      wpos:     0,
      seqnr,
    }
  }
}

#[derive(Clone, Default)]
pub struct MSaveState {
  // TODO
  pub rngsave:  MRngSaveState,
}

impl MSaveState {
  pub fn seek(&self, seqnr: u64) -> MSaveState {
    MSaveState{
      rngsave:  self.rngsave.seek(seqnr),
    }
  }

  pub fn restore(&self) -> MState {
    let mut rng: ChaChaRng = ChaChaRng::from_seed(self.rngsave.seed);
    rng.set_word_pos(self.rngsave.wpos);
    rng.set_stream(self.rngsave.seqnr);
    MState{
      rng,
    }
  }
}

pub struct VMachine {
  pub cfg:      Config,
  pub ctrl:     VMReg,
  pub env:      VMEnvRef,
  pub kont:     VMKontRef,
  pub store:    VMStore,
  pub initsave: MSaveState,
}

impl VMachine {
  pub fn new() -> VMachine {
    VMachine{
      cfg:      Config::default(),
      ctrl:     VMReg::Uninit,
      env:      VMEnvRef::default(),
      kont:     VMKontRef::default(),
      store:    VMStore::default(),
      initsave: MSaveState::default(),
    }
  }

  pub fn _debug_dump_ctrl(&self) {
    match &self.ctrl {
      &VMReg::Uninit => println!("DEBUG: vm: ctrl: uninit"),
      &VMReg::Code(_) => println!("DEBUG: vm: ctrl: code"),
      &VMReg::MVal(ref mval) => {
        match &**mval {
          VMVal::Bit(x) => println!("DEBUG: vm: ctrl: mval: bit: {:?}", x),
          VMVal::Int(x) => println!("DEBUG: vm: ctrl: mval: int: {:?}", x),
          _ => println!("DEBUG: vm: ctrl: mval: other"),
        }
      }
      _ => unimplemented!(),
    }
  }

  pub fn _lookup_thunk(&self, var: LVar) -> (VMAddr, VMThunkRef) {
    let addr = self.env.lookup(var);
    let mthk = self.store.lookup(addr);
    (addr, mthk)
  }

  pub fn _lookup(&self, var: LVar) -> VMValRef {
    // TODO
    let addr = self.env.lookup(var);
    let mthk = self.store.lookup(addr);
    let mslot = mthk.slot.borrow();
    match &*mslot {
      &VMThunkSlot::Ret(ref mval) => mval.clone(),
      _ => panic!(),
    }
  }

  pub fn _reset(&mut self, ltree: LExpr) {
    // TODO
    //self.ctrl = Some(ltree);
    self.ctrl = VMReg::Code(ltree);
    //self.env = None;
    self.env = VMEnvRef::default();
    //self.kont = VMKont::Stop;
    self.kont = VMKontRef::default();
  }

  pub fn _is_terminal(&self) -> bool {
    // TODO: as written this is for the version w/ "ret" konts.
    /*self.ctrl.is_none() &&
        self.env.is_none() &&
        self.kont.is_terminal()*/
    match (&self.ctrl, &*self.kont) {
      (&VMReg::MVal(_), &VMKont::Stop) => true,
      _ => false,
    }
  }

  pub fn _step(&mut self) {
    // TODO
    println!("TRACE: vm: step");
    let ctrl = self.ctrl.clone();
    let env = self.env.clone();
    let kont = self.kont.clone();
    let (next_ctrl, next_env, next_kont) = match ctrl {
      VMReg::Uninit => {
        /*match &*kont {
          &VMKont::App(0, ref arg_codes, ref maybe_mlam, ref args, ref env, ref kont) => {
            assert_eq!(arg_codes.len(), 0);
            let mlam = match maybe_mlam {
              &Some(ref mlam) => mlam.clone(),
              &None => panic!(),
            };
            let mut next_env = env.clone();
            for (bvar, arg) in mlam.bind.iter().zip(args.iter()) {
              next_env = next_env.insert(bvar.clone(), arg.clone());
            }
            let next_ctrl = VMReg::Code(mlam.code.clone());
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          _ => unreachable!(),
        }*/
        unreachable!();
      }
      VMReg::BCode(bcode, nargs) => {
        match &*kont {
          &VMKont::ApBc(..) => {
            // TODO
            let mval = (bcode.ifun)(nargs, env.clone());
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          _ => panic!(),
        }
      }
      VMReg::Code(ltree) => {
        match (&*ltree.term, &*kont) {
          (&LTerm::Env, _) => {
            // TODO
            unimplemented!();
          }
          (&LTerm::DynEnv(ref lenv), _) => {
            // TODO
            println!("TRACE: vm:   capturing dyn env...");
            /*for (k, _) in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", k);
            }*/
            // FIXME
            //let mval = VMValRef::new(VMVal::Env(env.clone()));
            let mval = VMValRef::new(VMVal::DEnv(lenv.clone()));
            let next_ctrl = VMReg::MVal(mval);
            let next_kont = kont;
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Let(ref name, ref body, ref rest), _) => {
            println!("TRACE: vm:   expr: let");
            let rest_mlam = VMLam{
              bind: vec![name.clone()],
              code: rest.clone(),
            };
            let thk_a = self.store.fresh_addr();
            // NB: The `Thk1` continuation does not create bind the var to the
            // thunk address, instead that happens here.
            let rest_env = env.insert(name.clone(), thk_a.clone());
            let body_mlam = VMLam{
              bind: vec![],
              code: body.clone(),
            };
            // NB: The thunk will be immediately updated, so can directly
            // construct it in the "black hole" state.
            let mthk = VMThunkRef::new(VMThunk::new_blkhole(body_mlam, env.clone()));
            self.store.insert_new(thk_a.clone(), mthk);
            let next_ctrl = VMReg::Code(body.clone());
            let next_kont = VMKontRef::new(VMKont::Thk1(thk_a, rest_mlam, rest_env, kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Fix(ref name, ref expr), _) => {
            // TODO
            unimplemented!();
            /*let cap_env = env.clone();
            let fix_code = ltree.clone();
            let fix_mlam = VMLam{
              bind: vec![],
              code: fix_code,
            };
            let fix_mclosure = VMClosure{
              lam:  fix_mlam,
              env:  env.clone(),
            };
            let next_env = env.insert(name, fix_mclosure);
            let next_ctrl = VMReg::Code(body.clone());
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)*/
          }
          (&LTerm::BitLit(x), _) => {
            println!("TRACE: vm:   expr: bitlit");
            let mval = VMValRef::new(VMVal::Bit(x));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::IntLit(x), _) => {
            println!("TRACE: vm:   expr: intlit");
            let mval = VMValRef::new(VMVal::Int(x));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Lookup(ref lookup_var), _) => {
            println!("TRACE: vm:   expr: lookup");
            let (thk_a, mthk) = self._lookup_thunk(lookup_var.clone());
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                let rest_mlam = VMLam{
                  bind: vec![],
                  code: ltree.clone(),
                };
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = VMReg::Code(mthk.lam.code.clone());
                let next_kont = VMKontRef::new(VMKont::Thk1(thk_a, rest_mlam, env.clone(), kont));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:   emp end");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Ret => {
                println!("TRACE: vm:   expr:   ret...");
                let mslot = mthk.slot.borrow();
                let mval = match &*mslot {
                  &VMThunkSlot::Ret(ref mval) => mval.clone(),
                  _ => unreachable!(),
                };
                // TODO: this basically overwrites the current env if the mval
                // is a closure... is this the correct behavior?
                let next_env = match &*mval {
                  &VMVal::Clo(ref mclosure) => mclosure.env.clone(),
                  _ => env,
                };
                let next_ctrl = VMReg::MVal(mval);
                let next_kont = kont;
                println!("TRACE: vm:   expr:   ret end");
                (next_ctrl, next_env, next_kont)
              }
              _ => panic!(),
            }
          }
          (&LTerm::DynEnvLookup(ref target, ref name), _) => {
            // TODO
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::Lkd(name.clone(), env.clone(), kont));
            let next_env = env.clone();
            (next_ctrl, next_env, next_kont)
          }
          _ => unimplemented!(),
        }
      }
      VMReg::MVal(mval) => {
        match (&*mval, &*kont) {
          /*(&VMVal::Lam(ref mlam), &VMKont::App0(ref env, ref kont)) => {
            // TODO
            let next_ctrl = VMReg::Code(mlam.code.clone());
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }*/
          (&VMVal::DEnv(ref tg_lenv), &VMKont::Lkd(ref name, ref env, ref kont)) => {
            // TODO
            let lk_var = match tg_lenv.names.get(name) {
              Some(lk_var) => lk_var.clone(),
              None => panic!(),
            };
            let lk_code = match tg_lenv.bindings.get(&lk_var) {
              Some(&(_, LDef::Code(ref lk_code))) => lk_code.clone(),
              None => panic!(),
            };
            let next_ctrl = VMReg::Code(lk_code);
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::Thk1(ref thk_a, ref rest_mlam, ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: thk1");
            self.store.update(thk_a.clone(), mval);
            let next_ctrl = VMReg::Code(rest_mlam.code.clone());
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::App0(ref env, ref kont)) => {
            // TODO: runtime panic if the reg is not a lambda.
            panic!();
          }
          /*(&VMVal::Env(ref menv), &VMKont::App1(ref mlam, ref env, ref kont)) => {
            // TODO
            unimplemented!();
          }*/
          (_, &VMKont::App1(ref mlam, ref env, ref kont)) => {
            // FIXME
            unimplemented!();
            /*let bvar = mlam.bind[0].clone();
            let thk_a = self.store.fresh_addr();
            self.store.insert_new(a.clone(), mval);
            /*let mthk = VMThunkRef::new(VMThunk::new(mval, env.clone()));
            self.store.insert_new(thk_a.clone(), mthk);*/
            let next_env = env.insert(bvar, thk_a);
            let next_ctrl = VMReg::Code(mlam.code.clone());
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)*/
          }
          (_, &VMKont::App(rem, ref arg_codes, ref maybe_mlam, ref args, ref next_env, ref next_kont)) => {
            // TODO
            assert_eq!(rem, arg_codes.len());
            let mut arg_codes = arg_codes.clone();
            let _ = arg_codes.pop();
            let mut args = args.clone();
            args.push(mval.clone());
            match rem {
              0 => {
                let mlam = match maybe_mlam {
                  &Some(ref mlam) => mlam.clone(),
                  &None => panic!(),
                };
                let mut next_env = next_env.clone();
                for (bvar, arg) in mlam.bind.iter().zip(args.iter()) {
                  // FIXME
                  unimplemented!();
                  /*let a = self.store.fresh_addr();
                  self.store.insert_new(a.clone(), arg.clone());
                  next_env = next_env.insert(bvar.clone(), a);*/
                }
                let next_ctrl = VMReg::Code(mlam.code.clone());
                let next_kont = next_kont.clone();
                (next_ctrl, next_env, next_kont)
              }
              _ => {
                // TODO
                unimplemented!();
                //let next_kont = VMKontRef::new(VMKont::App(rem - 1, arg_codes, maybe_mlam.clone(), args, next_env.clone(), next_kont.clone()));
                //let next_env = env.clone();
                //(next_ctrl, next_env, next_kont)
              }
            }
          }
          (&VMVal::Bit(x), &VMKont::Swh(ref on_code, ref off_code, ref env, ref kont)) => {
            let next_ctrl = VMReg::Code(match x {
              true  => on_code.clone(),
              false => off_code.clone(),
            });
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::Swh(..)) => {
            // TODO: runtime panic if the reg is not a bit.
            panic!();
          }
          _ => unimplemented!(),
        }
      }
    };
    self.ctrl = next_ctrl;
    self.env = next_env;
    self.kont = next_kont;
  }

  pub fn eval(&mut self, ltree: LExpr) {
    // TODO
    self._reset(ltree);
    while !self._is_terminal() {
      self._step()
    }
  }

  pub fn _debug_eval(&mut self, ltree: Option<LExpr>, nsteps: usize) {
    if let Some(ltree) = ltree {
      self._reset(ltree);
    }
    for _ in 0 .. nsteps {
      if self._is_terminal() {
        break;
      }
      self._step()
    }
  }
}
