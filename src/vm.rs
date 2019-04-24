// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::cfg::{GlobalConfig};
use crate::ir::{LDef, LEnv, LExpr, LPat, LTerm, LTermPat, LVar, LTermRef, LVMExt};
use crate::num_util::{Checked, checked};
use crate::rngs::{HwRng};

use rand::prelude::*;
use rand_chacha::{ChaChaRng};
use vertreap::{VertreapMap};

use std::any::{Any};
use std::cell::{RefCell};
use std::collections::{HashMap, VecDeque};
use std::iter::{FromIterator};
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
  //pub ladj: Option<Rc<dyn Fn(usize, LExpr) -> LTermRef>>,
}

pub struct VMModule {
  pub env:  VMEnvRef,
}

#[derive(Clone)]
pub enum VMLamCode {
  NoExec,
  LamTerm(Vec<LVar>, LExpr),
  BoxCode(VMBoxCode),
}

#[derive(Clone)]
pub struct VMLam {
  pub code: VMLamCode,
}

#[derive(Clone)]
pub struct VMClosure {
  pub lam:  VMLam,
  pub env:  VMEnvRef,
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
  pub addr: VMAddr,
  pub lam:  VMLam,
  pub env:  VMEnvRef,
  //pub save: MSaveState,
  pub slot: RefCell<VMThunkSlot>,
}

impl VMThunk {
  pub fn new_empty_tmp(addr: VMAddr, env: VMEnvRef) -> VMThunk {
    VMThunk{
      addr,
      lam:  VMLam{code: VMLamCode::NoExec},
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
    }
  }

  pub fn new_empty(addr: VMAddr, lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      addr,
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
    }
  }

  pub fn new_blkhole_tmp(addr: VMAddr, env: VMEnvRef) -> VMThunk {
    VMThunk{
      addr,
      lam:  VMLam{code: VMLamCode::NoExec},
      env,
      slot: RefCell::new(VMThunkSlot::Blk),
    }
  }

  pub fn new_blkhole(addr: VMAddr, lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      addr,
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

pub trait VMUnpack<T> {
  fn try_unpack(&self) -> Option<T>;
}

pub type VMValRef = Rc<VMVal>;

//#[derive(Debug)]
pub enum VMVal {
  //DEnv(LEnv),
  Env(VMEnvRef),
  Clo(VMClosure),
  Tup(Vec<VMValRef>),
  Bit(bool),
  Int(Checked<i64>),
  Flo(f64),
  Box_(VMBoxVal),
  State(MState),
}

impl VMUnpack<bool> for VMVal {
  fn try_unpack(&self) -> Option<bool> {
    match self {
      &VMVal::Bit(x) => {
        Some(x)
      }
      _ => None,
    }
  }
}

impl VMUnpack<i64> for VMVal {
  fn try_unpack(&self) -> Option<i64> {
    match self {
      &VMVal::Int(x) => {
        Some(x.into())
      }
      _ => None,
    }
  }
}

impl VMUnpack<f64> for VMVal {
  fn try_unpack(&self) -> Option<f64> {
    match self {
      &VMVal::Flo(x) => {
        Some(x)
      }
      _ => None,
    }
  }
}

impl VMUnpack<()> for VMVal {
  fn try_unpack(&self) -> Option<()> {
    match self {
      &VMVal::Tup(ref elems) => {
        if elems.is_empty() {
          Some(())
        } else {
          None
        }
      }
      _ => None,
    }
  }
}

impl<T1> VMUnpack<(T1,)> for VMVal where VMVal: VMUnpack<T1> {
  fn try_unpack(&self) -> Option<(T1,)> {
    match self {
      &VMVal::Tup(ref elems) => {
        if elems.len() == 1 {
          elems[0].try_unpack().map(|v1| (v1,))
        } else {
          None
        }
      }
      _ => None,
    }
  }
}

impl<T1, T2> VMUnpack<(T1, T2)> for VMVal where VMVal: VMUnpack<T1> + VMUnpack<T2> {
  fn try_unpack(&self) -> Option<(T1, T2)> {
    match self {
      &VMVal::Tup(ref elems) => {
        if elems.len() == 2 {
          elems[0].try_unpack().and_then(|v1|
            elems[1].try_unpack().map(|v2|
              (v1, v2)
            )
          )
        } else {
          None
        }
      }
      _ => None,
    }
  }
}

impl<T1, T2, T3> VMUnpack<(T1, T2, T3)> for VMVal where VMVal: VMUnpack<T1> + VMUnpack<T2> + VMUnpack<T3> {
  fn try_unpack(&self) -> Option<(T1, T2, T3)> {
    match self {
      &VMVal::Tup(ref elems) => {
        if elems.len() == 3 {
          elems[0].try_unpack().and_then(|v1|
            elems[1].try_unpack().and_then(|v2|
              elems[2].try_unpack().map(|v3|
                (v1, v2, v3)
              )
            )
          )
        } else {
          None
        }
      }
      _ => None,
    }
  }
}

impl VMVal {
  pub fn _mval_name(&self) -> &'static str {
    match self {
      //&VMVal::DEnv(_) => "DEnv",
      &VMVal::Env(_) => "Env",
      &VMVal::Clo(_) => "Clo",
      &VMVal::Tup(_) => "Tup",
      &VMVal::Bit(_) => "Bit",
      &VMVal::Int(_) => "Int",
      &VMVal::Flo(_) => "Flo",
      &VMVal::Box_(_) => "Box_",
      &VMVal::State(_) => "State",
    }
  }

  fn _pattern_match_bind(this: VMValRef, pat: LPat, pat_env: &mut Vec<(LVar, VMValRef)>) -> bool {
    match (&*this, &*pat.term) {
      (&VMVal::Tup(ref es), &LTermPat::Tup(ref esp)) => {
        if es.len() == esp.len() {
          let mut pm = true;
          for (e, ep) in es.iter().zip(esp.iter()) {
            pm &= VMVal::_pattern_match_bind(e.clone(), ep.clone(), pat_env);
          }
          pm
        } else {
          false
        }
      }
      (_, &LTermPat::Tup(_)) => {
        panic!("vm: runtime error: tried to match a tup pattern, but mval is not a tup: {}", this._mval_name());
      }
      (&VMVal::Bit(x), &LTermPat::BitLit(xp)) => {
        if x == xp { true }
        else { false }
      }
      (&VMVal::Int(x), &LTermPat::IntLit(xp)) => {
        let x: i64 = x.into();
        if x == xp { true }
        else { false }
      }
      (_, &LTermPat::IntLit(_)) => {
        panic!("vm: runtime error: tried to match a int pattern, but mval is not a int: {}", this._mval_name());
      }
      (&VMVal::Flo(x), &LTermPat::FloLit(xp)) => {
        if x == xp { true }
        else { false }
      }
      (_, &LTermPat::Var(ref vp)) => {
        pat_env.push((vp.clone(), this));
        true
      }
      (_, &LTermPat::Wild) => {
        true
      }
      _ => unimplemented!(),
    }
  }

  pub fn _pattern_match(this: VMValRef, pat: LPat) -> Option<Vec<(LVar, VMValRef)>> {
    let mut pat_env = vec![];
    if VMVal::_pattern_match_bind(this, pat, &mut pat_env) {
      Some(pat_env)
    } else {
      None
    }
  }
}

#[derive(Clone)]
pub enum VMReg {
  Uninit,
  Code(LExpr),
  //BCode(VMBoxCode),
  BCode(VMBoxCode, Vec<VMValRef>),
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
  //Lkd(String, VMEnvRef, VMKontRef),
  ELku(LVar, VMLam, VMEnvRef, VMKontRef),
  Thk0(VMAddr, VMLam, VMEnvRef, VMKontRef),
  App0(VMEnvRef, VMKontRef),
  App(Option<VMClosure>, Vec<VMValRef>, VecDeque<LExpr>, VMEnvRef, VMKontRef),
  //ApBc(VMEnvRef, VMKontRef),
  Ret(VMEnvRef, VMKontRef),
  Swch(LExpr, LExpr, VMEnvRef, VMKontRef),
  Mch(VecDeque<(LPat, LExpr)>, VMEnvRef, VMKontRef),
  //Frc(LVar, VMEnvRef, VMKontRef),
  Tup(Vec<LExpr>, Vec<VMValRef>, VMEnvRef, VMKontRef),
  // TODO: final "ret" kont may be unnecessary.
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
      //&VMKont::Lkd(..) => "Lkd",
      &VMKont::ELku(..) => "ELku",
      &VMKont::Thk0(..) => "Thk0",
      &VMKont::App0(..) => "App0",
      &VMKont::App(..) => "App",
      &VMKont::Ret(..) => "Ret",
      &VMKont::Swch(..) => "Swch",
      &VMKont::Mch(..) => "Mch",
      &VMKont::Tup(..) => "Tup",
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
            println!("vm: runtime warning: updating an empty thunk");
            let mut mslot = mthk.slot.borrow_mut();
            *mslot = VMThunkSlot::Ret(mval);
          }
          VMThunkState::Blk => {
            let mut mslot = mthk.slot.borrow_mut();
            *mslot = VMThunkSlot::Ret(mval);
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

pub struct MSeqState {
  // TODO
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
  pub cfg:      GlobalConfig,
  pub ctrl:     VMReg,
  pub env:      VMEnvRef,
  pub kont:     VMKontRef,
  pub store:    VMStore,
  pub initsave: MSaveState,
}

impl VMachine {
  pub fn new() -> VMachine {
    VMachine{
      cfg:      GlobalConfig::default(),
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
          VMVal::Tup(elems) => println!("DEBUG: vm: ctrl: mval: tuple (num elems: {})", elems.len()),
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
        /*&VMKont::Lkd(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }*/
        &VMKont::ELku(.., ref prev_kont) => {
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
        &VMKont::App(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Ret(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Swch(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Mch(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Tup(.., ref prev_kont) => {
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
            println!("TRACE: vm:   expr: apply");
            let next_ctrl = VMReg::Code(head.clone());
            let next_kont = VMKontRef::new(VMKont::App(None, Vec::new(), VecDeque::from_iter(args.iter().map(|a| a.clone())), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          /*(&LTerm::Env, _) => {
            // TODO
            unimplemented!();
          }*/
          /*(&LTerm::DynEnv(ref lenv), _) => {
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
          }*/
          (&LTerm::Lambda(ref params, ref body), _) => {
            // TODO
            println!("TRACE: vm:   capturing lambda...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              lam: VMLam{
                code: VMLamCode::LamTerm(params.clone(), body.clone()),
              },
              env: env.clone(),
            }));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          /*(&LTerm::LambdaEnv(ref closed_env, ref env_param, ref params, ref body), _) => {
            // TODO
            unimplemented!();
          }*/
          /*(&LTerm::VMExt(LTermVMExt::BCLambda(ref bvars, ref body)), _) => {
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
          }*/
          (&LTerm::VMExt(LVMExt::BCLambda(ref _params, ref bcdef)), _) => {
            // TODO
            println!("TRACE: vm:   capturing bc lambda...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              lam: VMLam{
                code: VMLamCode::BoxCode(match bcdef.cg {
                  None => panic!(),
                  Some(ref cg) => (cg)(),
                }),
              },
              env: env.clone(),
            }));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Let(ref name, ref body, ref rest), _) => {
            println!("TRACE: vm:   expr: let");
            let rest_mlam = VMLam{
              code: VMLamCode::LamTerm(Vec::new(), rest.clone()),
            };
            let thk_a = self.store.fresh_addr();
            // NB: The `Thk0` continuation does not create bind the var to the
            // thunk address, instead that happens here.
            let rest_env = env.insert(name.clone(), thk_a.clone());
            let body_mlam = VMLam{
              code: VMLamCode::LamTerm(Vec::new(), body.clone()),
            };
            // NB: The thunk will be immediately updated, so can directly
            // construct it in the "black hole" state.
            let mthk = VMThunkRef::new(VMThunk::new_blkhole(thk_a.clone(), body_mlam, env.clone()));
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
              code: VMLamCode::LamTerm(Vec::new(), ltree.clone()),
            };
            // NB: The fixpoint thunk maybe delayed, so must construct it in
            // the "empty" state.
            // TODO: should `mthk` capture `env` or `fix_env`?
            let mthk = VMThunkRef::new(VMThunk::new_empty(thk_a.clone(), fix_mlam, env.clone()));
            self.store.insert_new(thk_a, mthk);
            // FIXME: this next part needs some reworking, as the current env is
            // basically overwritten with `fix_env`.
            let fixbody_mlam = VMLam{
              code: VMLamCode::LamTerm(Vec::new(), fixbody.clone()),
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
          (&LTerm::Match(ref query, ref pat_arms), _) => {
            println!("TRACE: vm:   expr: match");
            let next_ctrl = VMReg::Code(query.clone());
            let next_kont = VMKontRef::new(VMKont::Mch(VecDeque::from(pat_arms.clone()), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Tuple(ref args), _) => {
            println!("TRACE: vm:   expr: tuple");
            if args.is_empty() {
              let mval = VMValRef::new(VMVal::Tup(vec![]));
              let next_ctrl = VMReg::MVal(mval);
              let next_env = env;
              let next_kont = kont;
              (next_ctrl, next_env, next_kont)
            } else {
              let next_ctrl = VMReg::Code(args[0].clone());
              let next_kont = VMKontRef::new(VMKont::Tup(args.clone(), vec![], env.clone(), kont));
              let next_env = env;
              (next_ctrl, next_env, next_kont)
            }
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
            let mval = VMValRef::new(VMVal::Int(checked(x)));
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
                  code: VMLamCode::LamTerm(Vec::new(), ltree.clone()),
                };
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::NoExec => panic!("vm: runtime error"),
                  VMLamCode::LamTerm(_, e) => VMReg::Code(e),
                  VMLamCode::BoxCode(bc) => VMReg::BCode(bc, Vec::new()),
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
          (&LTerm::EnvLookup(ref target, ref name), _) => {
            println!("TRACE: vm:   expr: env lookup");
            let lookup_mlam = VMLam{
              code: VMLamCode::LamTerm(Vec::new(), ltree.clone()),
            };
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::ELku(name.clone(), lookup_mlam, env.clone(), kont));
            let next_env = env.clone();
            (next_ctrl, next_env, next_kont)
          }
          /*(&LTerm::DynEnvLookup(ref target, ref name_s), _) => {
            // TODO
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::Lkd(name_s.clone(), env.clone(), kont));
            let next_env = env.clone();
            (next_ctrl, next_env, next_kont)
          }*/
          _ => unimplemented!(),
        }
      }
      /*VMReg::BCode(bcode) => {
        println!("TRACE: vm:   bcode");
        let ret_mval = (bcode.ifun)(vec![]);
        let next_ctrl = VMReg::MVal(ret_mval);
        let next_env = env.clone();
        let next_kont = kont.clone();
        (next_ctrl, next_env, next_kont)
      }*/
      VMReg::BCode(bcode, arg_mvals) => {
        println!("TRACE: vm:   bcode args");
        let ret_mval = (bcode.ifun)(arg_mvals);
        let next_ctrl = VMReg::MVal(ret_mval);
        let next_env = env.clone();
        let next_kont = kont.clone();
        (next_ctrl, next_env, next_kont)
      }
      VMReg::MVal(mval) => {
        match (&*mval, &*kont) {
          /*(&VMVal::DEnv(ref tg_lenv), &VMKont::Lkd(ref name, ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: lkd");
            let lk_var = match tg_lenv.names.get(name) {
              Some(lk_var) => lk_var.clone(),
              None => panic!(),
            };
            let lk_code = match tg_lenv.bindings.get(&lk_var) {
              Some(&(_, LDef::BVar)) => unimplemented!(),
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
          }*/
          (&VMVal::Env(ref tg_env), &VMKont::ELku(ref name, ref lookup_mlam, ref saved_env, ref saved_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: elku");
            let thk_a = tg_env.lookup(name.clone());
            let mthk = self.store.lookup(thk_a);
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::NoExec => panic!("vm: runtime error"),
                  VMLamCode::LamTerm(_, e) => VMReg::Code(e),
                  VMLamCode::BoxCode(bc) => VMReg::BCode(bc, Vec::new()),
                };
                let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, lookup_mlam.clone(), saved_env.clone(), saved_kont.clone()));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:     end emp");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Blk => {
                panic!("invalid thunk state (blkhole)");
              }
              VMThunkState::Ret => {
                println!("TRACE: vm:   kont:   ret...");
                let mval = match &*mthk.slot.borrow() {
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
                let next_env = saved_env.clone();
                let next_kont = saved_kont.clone();
                println!("TRACE: vm:   kont:     end ret");
                (next_ctrl, next_env, next_kont)
              }
            }
          }
          (_, &VMKont::ELku(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (_, &VMKont::Thk0(ref thk_a, ref rest_mlam, ref env, ref kont)) => {
            // TODO
            println!("TRACE: vm:   kont: thk0");
            self.store.update(thk_a.clone(), mval);
            let next_ctrl = match rest_mlam.code.clone() {
              VMLamCode::NoExec => panic!("vm: runtime error"),
              VMLamCode::LamTerm(_, e) => VMReg::Code(e),
              VMLamCode::BoxCode(bc) => {
                println!("WARNING: rest of the code after thk0 is bc, this path is less tested and may be broken");
                VMReg::BCode(bc, Vec::new())
              }
            };
            let next_env = env.clone();
            let next_kont = kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&VMVal::Clo(ref closure), &VMKont::App(None, ref arg_mvals, ref arg_codes, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: app (closure)");
            let mut next_arg_codes = arg_codes.clone();
            match next_arg_codes.pop_front() {
              Some(next_arg) => {
                let next_ctrl = VMReg::Code(next_arg);
                let next_kont = VMKontRef::new(VMKont::App(Some(closure.clone()), arg_mvals.clone(), next_arg_codes, saved_env.clone(), saved_kont.clone()));
                let next_env = saved_env.clone();
                (next_ctrl, next_env, next_kont)
              }
              None => {
                assert!(arg_mvals.is_empty());
                let next_ctrl = match closure.lam.code.clone() {
                  VMLamCode::NoExec => panic!("vm: runtime error"),
                  VMLamCode::LamTerm(params, body) => {
                    assert!(params.is_empty());
                    VMReg::Code(body)
                  }
                  VMLamCode::BoxCode(bc) => {
                    VMReg::BCode(bc, Vec::new())
                  }
                };
                let next_env = closure.env.clone();
                let next_kont = VMKontRef::new(VMKont::Ret(saved_env.clone(), saved_kont.clone()));
                (next_ctrl, next_env, next_kont)
              }
            }
          }
          (_, &VMKont::App(Some(ref closure), ref arg_mvals, ref arg_codes, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: app (arg)");
            let mut next_arg_mvals = arg_mvals.clone();
            let mut next_arg_codes = arg_codes.clone();
            next_arg_mvals.push(mval);
            match next_arg_codes.pop_front() {
              Some(next_arg) => {
                let next_ctrl = VMReg::Code(next_arg);
                let next_kont = VMKontRef::new(VMKont::App(Some(closure.clone()), next_arg_mvals, next_arg_codes, saved_env.clone(), saved_kont.clone()));
                let next_env = saved_env.clone();
                (next_ctrl, next_env, next_kont)
              }
              None => {
                match closure.lam.code.clone() {
                  VMLamCode::NoExec => panic!("vm: runtime error"),
                  VMLamCode::LamTerm(params, body) => {
                    assert_eq!(params.len(), arg_mvals.len());
                    let mut next_env = closure.env.clone();
                    for (pv, p_mval) in params.into_iter().zip(arg_mvals.iter()) {
                      let thk_a = self.store.fresh_addr();
                      let mthk = VMThunkRef::new(VMThunk::new_blkhole_tmp(thk_a.clone(), env.clone()));
                      self.store.insert_new(thk_a.clone(), mthk);
                      self.store.update(thk_a.clone(), p_mval.clone());
                      next_env = next_env.insert(pv, thk_a);
                    }
                    let next_ctrl = VMReg::Code(body);
                    let next_kont = VMKontRef::new(VMKont::Ret(saved_env.clone(), saved_kont.clone()));
                    (next_ctrl, next_env, next_kont)
                  }
                  VMLamCode::BoxCode(bc) => {
                    let next_env = closure.env.clone();
                    let next_ctrl = VMReg::BCode(bc, next_arg_mvals);
                    let next_kont = VMKontRef::new(VMKont::Ret(saved_env.clone(), saved_kont.clone()));
                    (next_ctrl, next_env, next_kont)
                  }
                }
              }
            }
          }
          (_, &VMKont::App(..)) => {
            self._debug_dump_ctrl();
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (_, &VMKont::Ret(ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: ret");
            let next_ctrl = VMReg::MVal(mval);
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
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
            panic!("vm: runtime error: switch expected bit value");
          }
          (_, &VMKont::Mch(ref pat_arms, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: mch");
            match pat_arms.front() {
              None => panic!("vm: runtime error: no matching pattern"),
              Some(&(ref pat, ref arm)) => {
                match VMVal::_pattern_match(mval.clone(), pat.clone()) {
                  None => {
                    let mut next_pat_arms = pat_arms.clone();
                    next_pat_arms.pop_front();
                    let next_ctrl = VMReg::MVal(mval);
                    let next_kont = VMKontRef::new(VMKont::Mch(next_pat_arms, saved_env.clone(), saved_kont.clone()));
                    let next_env = saved_env.clone();
                    (next_ctrl, next_env, next_kont)
                  }
                  Some(pat_env) => {
                    let mut next_env = saved_env.clone();
                    for (pv, p_mval) in pat_env.into_iter() {
                      let thk_a = self.store.fresh_addr();
                      let mthk = VMThunkRef::new(VMThunk::new_blkhole_tmp(thk_a.clone(), env.clone()));
                      self.store.insert_new(thk_a.clone(), mthk);
                      self.store.update(thk_a.clone(), p_mval);
                      next_env = next_env.insert(pv, thk_a);
                    }
                    let next_ctrl = VMReg::Code(arm.clone());
                    let next_kont = saved_kont.clone();
                    (next_ctrl, next_env, next_kont)
                  }
                }
              }
            }
          }
          (_, &VMKont::Tup(ref elem_codes, ref elem_mvals, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: tup");
            let mut elem_mvals = elem_mvals.clone();
            elem_mvals.push(mval);
            if elem_codes.len() < elem_mvals.len() {
              panic!();
            } else if elem_codes.len() == elem_mvals.len() {
              let next_ctrl = VMReg::MVal(VMValRef::new(VMVal::Tup(elem_mvals)));
              let next_env = saved_env.clone();
              let next_kont = saved_kont.clone();
              (next_ctrl, next_env, next_kont)
            } else if elem_codes.len() > elem_mvals.len() {
              let next_ctrl = VMReg::Code(elem_codes[elem_mvals.len()].clone());
              let next_kont = VMKontRef::new(VMKont::Tup(elem_codes.clone(), elem_mvals, saved_env.clone(), saved_kont.clone()));
              let next_env = env.clone();
              (next_ctrl, next_env, next_kont)
            } else {
              unreachable!();
            }
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

  pub fn eval(&mut self, ltree: LExpr) -> VMValRef {
    // TODO
    self._reset(ltree);
    self._eval();
    match (&self.ctrl, &*self.kont) {
      (&VMReg::MVal(ref mval), &VMKont::Halt) => mval.clone(),
      _ => unreachable!(),
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
