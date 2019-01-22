// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::cfg::{Config};
use crate::ir::{LDef, LEnv, LExpr, LTerm, LVar, LTermVMExt, LTermRef};
use crate::rngs::{HwRng};

use rand::prelude::*;
use rand_chacha::{ChaChaRng};
use vertreap::{VertreapMap};

use std::any::{Any};
use std::cell::{RefCell};
use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VMAddr {
  pub raw:  u64,
}

pub struct VMBoxVal {
  // TODO
  pub ival: Rc<dyn Any>,
}

#[derive(Clone)]
pub struct VMBoxCode {
  // TODO
  pub ifun: Rc<dyn Fn(Vec<VMValRef>) -> VMValRef>,
  pub ladj: Option<Rc<dyn Fn(usize, LExpr) -> LTermRef>>,
}

pub struct VMModule {
  pub env:  VMEnvRef,
}

#[derive(Clone)]
pub enum VMLamCode {
  Expr(LExpr),
  Box_(VMBoxCode),
}

#[derive(Clone)]
pub struct VMLam {
  //pub bind: Vec<LVar>,
  //pub code: LExpr,
  pub code: VMLamCode,
}

#[derive(Clone)]
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
  pub froz: bool,
}

impl VMThunk {
  pub fn new_empty(lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
      froz: false,
    }
  }

  pub fn new_blkhole(lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Blk),
      froz: false,
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
  Env(VMEnvRef),
  DEnv(LEnv),
  Clo(VMClosure),
  Bit(bool),
  Int(i64),
  Flo(f64),
  Tup,
  Box_(VMBoxVal),
}

impl VMVal {
  pub fn _mval_name(&self) -> &'static str {
    match self {
      &VMVal::Env(_) => "Env",
      &VMVal::DEnv(_) => "DEnv",
      &VMVal::Clo(_) => "Clo",
      &VMVal::Box_(_) => "Box_",
      &VMVal::Bit(_) => "Bit",
      &VMVal::Int(_) => "Int",
      &VMVal::Flo(_) => "Flo",
      &VMVal::Tup => "Tup",
    }
  }
}

#[derive(Clone)]
pub enum VMReg {
  Uninit,
  Code(LExpr),
  BCode(VMBoxCode),
  BCodeArgs(VMBoxCode, Vec<VMValRef>),
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
      None => {
        eprintln!("missing var in env: {:?}", name);
        for kv in self.addr_map.iter() {
          eprintln!("  kv: {:?}, _", kv.k);
        }
        panic!();
      }
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
  Halt,
  //Next(VMKontRef),
  Lkd(String, VMEnvRef, VMKontRef),
  Thk0(VMAddr, VMLam, VMEnvRef, VMKontRef),
  App0(VMEnvRef, VMKontRef),
  //App1(VMClosure, VMKontRef),
  //App1(VMLam, VMEnvRef, VMKontRef),
  App1(LExpr, Option<VMClosure>, Option<VMValRef>, VMEnvRef, VMKontRef),
  // TODO: like "arg" and "fun" konts but w/ arity.
  App(Vec<LExpr>, Option<VMLam>, Vec<VMValRef>, VMEnvRef, VMKontRef),
  //ApBc(VMEnvRef, VMKontRef),
  Call(VMEnvRef, VMKontRef),
  Swch(LExpr, LExpr, VMEnvRef, VMKontRef),
  //Frc(LVar, VMEnvRef, VMKontRef),
  // TODO: "ret" kont may be unnecessary.
  //Ret(VMValRef, VMKontRef),
}

impl Default for VMKont {
  fn default() -> VMKont {
    VMKont::Halt
  }
}

impl VMKont {
  pub fn _kont_name(&self) -> &'static str {
    match self {
      &VMKont::Halt => "Halt",
      &VMKont::Lkd(..) => "Lkd",
      &VMKont::Thk0(..) => "Thk0",
      &VMKont::App0(..) => "App0",
      &VMKont::App1(..) => "App1",
      &VMKont::App(..) => "App",
      &VMKont::Call(..) => "Call",
      &VMKont::Swch(..) => "Swch",
    }
  }

  /*pub fn is_terminal(&self) -> bool {
    // TODO: version below assumes a "ret" kont.
    match self {
      &VMKont::Ret(_, ref next) => {
        match &**next {
          &VMKont::Halt => true,
          _ => false,
        }
      }
      _ => false,
    }
  }*/
}

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
            if mthk.froz {
              panic!("bug");
            } else {
              *mslot = VMThunkSlot::Ret(mval);
            }
          }
          VMThunkState::Ret => {
            panic!("bug");
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
          VMVal::Clo(_) => println!("DEBUG: vm: ctrl: mval: closure"),
          VMVal::Bit(x) => println!("DEBUG: vm: ctrl: mval: bit: {:?}", x),
          VMVal::Int(x) => println!("DEBUG: vm: ctrl: mval: int: {:?}", x),
          _ => println!("DEBUG: vm: ctrl: mval: other"),
        }
      }
      _ => unimplemented!(),
    }
  }

  pub fn _debug_dump_stack_depth(&self) {
    let mut depth = 0;
    let mut kont = self.kont.clone();
    loop {
      match &*kont {
        &VMKont::Halt => break,
        &VMKont::Lkd(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Thk0(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::App0(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::App1(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::App(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Call(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Swch(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
      }
    }
    println!("DEBUG: vm: stack depth: {}", depth);
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
    //self.kont = VMKont::Halt;
    self.kont = VMKontRef::default();
  }

  pub fn _is_terminal(&self) -> bool {
    // TODO: as written this is for the version w/ "ret" konts.
    /*self.ctrl.is_none() &&
        self.env.is_none() &&
        self.kont.is_terminal()*/
    match (&self.ctrl, &*self.kont) {
      (&VMReg::MVal(_), &VMKont::Halt) => true,
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
      VMReg::Code(ltree) => {
        match (&*ltree.term, &*kont) {
          (&LTerm::Apply(ref head, ref args), _) => {
            // TODO
            match args.len() {
              0 => {
                println!("TRACE: vm:   expr: apply 0");
                /*for kv in env.addr_map.iter() {
                  println!("TRACE: vm:     kv: {:?}, _", kv.k);
                }*/
                let next_ctrl = VMReg::Code(head.clone());
                let next_kont = VMKontRef::new(VMKont::App0(env.clone(), kont));
                let next_env = env;
                (next_ctrl, next_env, next_kont)
              }
              1 => {
                println!("TRACE: vm:   expr: apply 1");
                /*for kv in env.addr_map.iter() {
                  println!("TRACE: vm:     kv: {:?}, _", kv.k);
                }*/
                let next_ctrl = VMReg::Code(head.clone());
                let next_kont = VMKontRef::new(VMKont::App1(args[0].clone(), None, None, env.clone(), kont));
                let next_env = env;
                (next_ctrl, next_env, next_kont)
              }
              _ => unimplemented!("apply with 2 or more args"),
            }
          }
          (&LTerm::Env, _) => {
            // TODO
            unimplemented!();
          }
          (&LTerm::DynEnv(ref lenv), _) => {
            // TODO
            println!("TRACE: vm:   capturing dyn env...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::DEnv(lenv.clone()));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Lambda(ref bvars, ref body), _) => {
            // TODO
            println!("TRACE: vm:   capturing lambda...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              env: env.clone(),
              lam: VMLam{
                //bind: bvars.clone(),
                code: VMLamCode::Expr(body.clone()),
              },
            }));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::VMExt(LTermVMExt::BcLambda(ref bvars, ref body)), _) => {
            // TODO
            println!("TRACE: vm:   capturing bc lambda...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              env: env.clone(),
              lam: VMLam{
                //bind: bvars.clone(),
                code: VMLamCode::Box_(body.clone()),
              },
            }));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Let(ref name, ref body, ref rest), _) => {
            println!("TRACE: vm:   expr: let");
            let rest_mlam = VMLam{
              //bind: vec![name.clone()],
              code: VMLamCode::Expr(rest.clone()),
            };
            let thk_a = self.store.fresh_addr();
            // NB: The `Thk0` continuation does not create bind the var to the
            // thunk address, instead that happens here.
            let rest_env = env.insert(name.clone(), thk_a.clone());
            let body_mlam = VMLam{
              //bind: vec![],
              code: VMLamCode::Expr(body.clone()),
            };
            // NB: The thunk will be immediately updated, so can directly
            // construct it in the "black hole" state.
            let mthk = VMThunkRef::new(VMThunk::new_blkhole(body_mlam, env.clone()));
            self.store.insert_new(thk_a.clone(), mthk);
            let next_ctrl = VMReg::Code(body.clone());
            let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, rest_mlam, rest_env, kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Fix(ref fixname, ref fixbody), _) => {
            println!("TRACE: vm:   expr: fix");
            let thk_a = self.store.fresh_addr();
            let fix_env = env.insert(fixname.clone(), thk_a.clone());
            let fix_mlam = VMLam{
              //bind: vec![],
              code: VMLamCode::Expr(ltree.clone()),
            };
            // NB: The fixpoint thunk maybe delayed, so must construct it in
            // the "empty" state.
            // TODO: should `mthk` capture `env` or `fix_env`?
            let mthk = VMThunkRef::new(VMThunk::new_empty(fix_mlam, env.clone()));
            self.store.insert_new(thk_a.clone(), mthk);
            let fixbody_mlam = VMLam{
              //bind: vec![],
              code: VMLamCode::Expr(fixbody.clone()),
            };
            let next_ctrl = VMReg::Code(fixbody.clone());
            let next_env = fix_env.clone();
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Switch(ref pred, ref top, ref bot), _) => {
            println!("TRACE: vm:   expr: switch");
            let next_ctrl = VMReg::Code(pred.clone());
            let next_kont = VMKontRef::new(VMKont::Swch(top.clone(), bot.clone(), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
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
            println!("TRACE: vm:   expr: lookup: {:?}", lookup_var);
            let (thk_a, mthk) = self._lookup_thunk(lookup_var.clone());
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                let rest_mlam = VMLam{
                  //bind: vec![],
                  code: VMLamCode::Expr(ltree.clone()),
                };
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::Expr(e) => VMReg::Code(e),
                  VMLamCode::Box_(bc) => VMReg::BCode(bc),
                };
                let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, rest_mlam, env.clone(), kont));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:     end emp");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Blk => {
                panic!("invalid thunk state (blkhole)");
              }
              VMThunkState::Ret => {
                println!("TRACE: vm:   expr:   ret...");
                let mslot = mthk.slot.borrow();
                let mval = match &*mslot {
                  &VMThunkSlot::Ret(ref mval) => mval.clone(),
                  _ => panic!("bug"),
                };
                /*// TODO: this basically overwrites the current env if the mval
                // is a closure... is this the correct behavior?
                let next_env = match &*mval {
                  &VMVal::Clo(ref mclosure) => mclosure.env.clone(),
                  _ => env,
                };*/
                let next_ctrl = VMReg::MVal(mval);
                let next_env = env;
                let next_kont = kont;
                println!("TRACE: vm:   expr:     end ret");
                (next_ctrl, next_env, next_kont)
              }
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
      VMReg::BCode(bcode) => {
        println!("TRACE: vm:   bcode");
        let ret_mval = (bcode.ifun)(vec![]);
        let next_ctrl = VMReg::MVal(ret_mval);
        let next_env = env.clone();
        let next_kont = kont.clone();
        (next_ctrl, next_env, next_kont)
      }
      VMReg::BCodeArgs(bcode, arg_mvals) => {
        println!("TRACE: vm:   bcode args");
        let ret_mval = (bcode.ifun)(arg_mvals);
        let next_ctrl = VMReg::MVal(ret_mval);
        let next_env = env.clone();
        let next_kont = kont.clone();
        (next_ctrl, next_env, next_kont)
      }
      VMReg::MVal(mval) => {
        match (&*mval, &*kont) {
          (&VMVal::DEnv(ref tg_lenv), &VMKont::Lkd(ref name, ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: lkd");
            let lk_var = match tg_lenv.names.get(name) {
              Some(lk_var) => lk_var.clone(),
              None => panic!(),
            };
            let lk_code = match tg_lenv.bindings.get(&lk_var) {
              Some(&(_, LDef::Code(ref lk_code))) => lk_code.clone(),
              Some(&(_, LDef::Fixpoint(..))) => {
                // FIXME
                unimplemented!();
              }
              None => panic!(),
            };
            let next_ctrl = VMReg::Code(lk_code);
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::Lkd(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (_, &VMKont::Thk0(ref thk_a, ref rest_mlam, ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: thk0");
            self.store.update(thk_a.clone(), mval);
            let next_ctrl = match rest_mlam.code.clone() {
              VMLamCode::Expr(e) => VMReg::Code(e),
              VMLamCode::Box_(bc) => {
                println!("WARNING: rest of the code after thk0 is bc, this path is untested and likely to be broken");
                VMReg::BCode(bc)
              }
            };
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&VMVal::Clo(ref closure), &VMKont::App0(ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: app0");
            let next_ctrl = match closure.lam.code.clone() {
              VMLamCode::Expr(e) => VMReg::Code(e),
              VMLamCode::Box_(bc) => VMReg::BCode(bc),
            };
            let next_env = closure.env.clone();
            //let next_kont = VMKontRef::new(VMKont::Call(env.clone(), kont.clone()));
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::App0(..)) => {
            self._debug_dump_ctrl();
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          /*(&VMVal::Env(ref menv), &VMKont::App1(ref mlam, ref env, ref kont)) => {
            // TODO
            unimplemented!();
          }*/
          /*(_, &VMKont::App1(ref mlam, ref env, ref kont)) => {
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
          }*/
          (&VMVal::Clo(ref closure), &VMKont::App1(ref arg_code, None, None, ref k_env, ref k_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: app1 (closure)");
            /*for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }*/
            let next_ctrl = VMReg::Code(arg_code.clone());
            let next_env = env.clone();
            let next_kont = VMKontRef::new(VMKont::App1(arg_code.clone(), Some(closure.clone()), None, k_env.clone(), k_kont.clone()));
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::App1(ref arg_code, Some(ref closure), None, ref k_env, ref k_kont)) => {
            println!("TRACE: vm:   kont: app1 (arg)");
            /*for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }*/
            let next_ctrl = VMReg::MVal(mval.clone());
            let next_env = env.clone();
            let next_kont = VMKontRef::new(VMKont::App1(arg_code.clone(), Some(closure.clone()), Some(mval), k_env.clone(), k_kont.clone()));
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::App1(_, Some(ref closure), Some(ref arg_mval), ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: app1 (eval)");
            /*for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }*/
            let next_ctrl = match closure.lam.code.clone() {
              VMLamCode::Expr(e) => VMReg::Code(e),
              VMLamCode::Box_(bc) => VMReg::BCodeArgs(bc, vec![arg_mval.clone()]),
            };
            let next_env = closure.env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::App1(..)) => {
            panic!("bug");
          }
          (_, &VMKont::App(ref arg_codes, ref maybe_mlam, ref mval_args, ref next_env, ref next_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: app");
            let rem = arg_codes.len();
            let mut arg_codes = arg_codes.clone();
            let _ = arg_codes.pop();
            let mut mval_args = mval_args.clone();
            mval_args.push(mval.clone());
            match rem {
              0 => {
                let mlam = match maybe_mlam {
                  &Some(ref mlam) => mlam.clone(),
                  &None => panic!(),
                };
                let mut next_env = next_env.clone();
                // TODO: freevars.
                /*for (bvar, arg) in mlam.bind.iter().zip(mval_args.iter()) {
                  // FIXME
                  unimplemented!();
                  /*let a = self.store.fresh_addr();
                  self.store.insert_new(a.clone(), arg.clone());
                  next_env = next_env.insert(bvar.clone(), a);*/
                }*/
                let next_ctrl = match mlam.code.clone() {
                  VMLamCode::Expr(e) => VMReg::Code(e),
                  VMLamCode::Box_(bc) => VMReg::BCode(bc),
                };
                let next_kont = next_kont.clone();
                (next_ctrl, next_env, next_kont)
              }
              _ => {
                // TODO
                unimplemented!();
                //let next_kont = VMKontRef::new(VMKont::App(rem - 1, arg_codes, maybe_mlam.clone(), mval_args, next_env.clone(), next_kont.clone()));
                //let next_env = env.clone();
                //(next_ctrl, next_env, next_kont)
              }
            }
          }
          (&VMVal::Bit(x), &VMKont::Swch(ref top_code, ref bot_code, ref env, ref kont)) => {
            println!("TRACE: vm:   kont: swch");
            let next_ctrl = VMReg::Code(match x {
              true  => top_code.clone(),
              false => bot_code.clone(),
            });
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::Swch(..)) => {
            // TODO: runtime panic if the reg is not a bit.
            panic!();
          }
          _ => {
            panic!("unimpl: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
        }
      }
    };
    self.ctrl = next_ctrl;
    self.env = next_env;
    self.kont = next_kont;
  }

  pub fn _eval(&mut self) {
    while !self._is_terminal() {
      self._step()
    }
  }

  pub fn eval(&mut self, ltree: LExpr) {
    // TODO
    self._reset(ltree);
    self._eval();
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
