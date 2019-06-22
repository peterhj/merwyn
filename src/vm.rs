// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::cfg::{GlobalConfig};
use crate::ir::{LBuilder, LDef, LEnv, LEnvKey, LExpr, LPat, LTerm, LTermRef, LVar, LVMExt};
use crate::num_util::{Checked, checked};
use crate::rngs::{HwRng};

use rand::prelude::*;
use rand_chacha::{ChaChaRng};
use vertreap::{VertreapMap};

use std::any::{Any};
use std::cell::{RefCell};
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::iter::{FromIterator};
use std::rc::{Rc};

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
  NoExe,
  LCode(Vec<LVar>, LExpr),
  BCode(usize, VMBoxCode),
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

/*#[derive(Clone)]
pub enum VMAValue {
  Addr(VMAddr),
  Cons(VMAddr, VMAddr, VMAddr),
}*/

#[derive(Clone)]
pub struct VMAEnv {
  // FIXME: data structure reprs.
  pub free: HashMap<LVar, VMAddr>,
  pub bind: Vec<LVar>,
}

pub enum VMThunkState {
  Emp,
  Blk,
  Val,
  Rst,
}

pub enum VMThunkSlot {
  Emp,
  Blk,
  Val(VMValRef),
  Rst,
}

pub type VMThunkRef = Rc<VMThunk>;

pub struct VMThunk {
  //pub addr: VMAddr,
  pub lam:  VMLam,
  pub env:  VMEnvRef,
  //pub save: MSaveState,
  pub slot: RefCell<VMThunkSlot>,
}

impl VMThunk {
  pub fn new_empty_tmp(/*addr: VMAddr,*/ env: VMEnvRef) -> VMThunk {
    VMThunk{
      //addr,
      lam:  VMLam{code: VMLamCode::NoExe},
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
    }
  }

  pub fn new_empty(/*addr: VMAddr,*/ lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      //addr,
      lam,
      env,
      slot: RefCell::new(VMThunkSlot::Emp),
    }
  }

  pub fn new_blkhole_tmp(/*addr: VMAddr,*/ env: VMEnvRef) -> VMThunk {
    VMThunk{
      //addr,
      lam:  VMLam{code: VMLamCode::NoExe},
      env,
      slot: RefCell::new(VMThunkSlot::Blk),
    }
  }

  pub fn new_blkhole(/*addr: VMAddr,*/ lam: VMLam, env: VMEnvRef) -> VMThunk {
    VMThunk{
      //addr,
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
      &VMThunkSlot::Val(_) => VMThunkState::Val,
      &VMThunkSlot::Rst => VMThunkState::Rst,
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
  AEnv(VMAEnv),
  Clo(VMClosure),
  STup(Vec<VMValRef>),
  Tup(Vec<VMValRef>),
  Bit(bool),
  Int(Checked<i64>),
  Flo(f64),
  Box(VMBoxVal),
  Ref(RefCell<VMValRef>),
  RState,
  IOState,
}

impl fmt::Debug for VMVal {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    // TODO
    match self {
      &VMVal::AEnv(_) => write!(f, "AEnv(...)"),
      &VMVal::Clo(_) => write!(f, "Clo(...)"),
      &VMVal::STup(_) => write!(f, "STup(...)"),
      &VMVal::Tup(_) => write!(f, "STup(...)"),
      &VMVal::Bit(x) => write!(f, "Bit({:?})", x),
      &VMVal::Int(x) => {
        let u: i64 = x.into();
        write!(f, "Int({:?})", u)
      }
      &VMVal::Flo(x) => write!(f, "Flo({:?})", x),
      &VMVal::Box(_) => write!(f, "Box(...)"),
      &VMVal::Ref(_) => write!(f, "Ref(...)"),
      &VMVal::RState => write!(f, "RState"),
      &VMVal::IOState => write!(f, "IOState"),
    }
  }
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
      &VMVal::STup(ref elems) => {
        if elems.is_empty() {
          Some(())
        } else {
          None
        }
      }
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
      &VMVal::STup(ref elems) => {
        if elems.len() == 1 {
          elems[0].try_unpack().map(|v1| (v1,))
        } else {
          None
        }
      }
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
      &VMVal::STup(ref elems) => {
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
      &VMVal::STup(ref elems) => {
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
      &VMVal::AEnv(_) => "AEnv",
      &VMVal::Clo(_) => "Clo",
      &VMVal::STup(_) => "STup",
      &VMVal::Tup(_) => "Tup",
      &VMVal::Bit(_) => "Bit",
      &VMVal::Int(_) => "Int",
      &VMVal::Flo(_) => "Flo",
      &VMVal::Box(_) => "Box",
      &VMVal::Ref(_) => "Ref",
      &VMVal::RState => "RState",
      &VMVal::IOState => "IOState",
    }
  }

  fn _pattern_match_bind(this: VMValRef, pat: &LPat, pat_env: &mut Vec<(LVar, VMValRef)>) -> bool {
    match (&*this, pat) {
      (&VMVal::STup(ref es), &LPat::STuple(ref esp)) => {
        if es.len() == esp.len() {
          let mut pm = true;
          for (e, ep) in es.iter().zip(esp.iter()) {
            pm &= VMVal::_pattern_match_bind(e.clone(), &*ep, pat_env);
          }
          pm
        } else {
          false
        }
      }
      (_, &LPat::STuple(_)) => {
        panic!("vm: runtime error: tried to match a STup pattern, but mval is not a STup: {}", this._mval_name());
      }
      (&VMVal::Tup(ref es), &LPat::Tuple(ref esp)) => {
        if es.len() == esp.len() {
          let mut pm = true;
          for (e, ep) in es.iter().zip(esp.iter()) {
            pm &= VMVal::_pattern_match_bind(e.clone(), &*ep, pat_env);
          }
          pm
        } else {
          false
        }
      }
      (_, &LPat::Tuple(_)) => {
        panic!("vm: runtime error: tried to match a Tup pattern, but mval is not a Tup: {}", this._mval_name());
      }
      (&VMVal::Bit(x), &LPat::BitLit(xp)) => {
        if x == xp { true }
        else { false }
      }
      (_, &LPat::BitLit(_)) => {
        panic!("vm: runtime error: tried to match a Bit pattern, but mval is not a Bit: {}", this._mval_name());
      }
      (&VMVal::Int(x), &LPat::IntLit(xp)) => {
        let x: i64 = x.into();
        if x == xp { true }
        else { false }
      }
      (_, &LPat::IntLit(_)) => {
        panic!("vm: runtime error: tried to match a Int pattern, but mval is not a Int: {}", this._mval_name());
      }
      /*(&VMVal::Flo(x), &LPat::FloLit(xp)) => {
        if x == xp { true }
        else { false }
      }
      (_, &LPat::FloLit(_)) => {
        panic!("vm: runtime error: tried to match a Flo pattern, but mval is not a Flo: {}", this._mval_name());
      }*/
      (_, &LPat::Var(ref vp)) => {
        pat_env.push((vp.clone(), this));
        true
      }
      (_, &LPat::Place) => {
        true
      }
      _ => unimplemented!(),
    }
  }

  pub fn _pattern_match(this: VMValRef, pat: LPat) -> Option<Vec<(LVar, VMValRef)>> {
    let mut pat_env = vec![];
    if VMVal::_pattern_match_bind(this, &pat, &mut pat_env) {
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

pub type VMEnvRef = VMNamedEnvRef;

#[derive(Clone, Default)]
pub struct VMNamedEnvRef {
  // TODO
  //mval_map: HashMap<LVar, VMValRef>,
  //addr_map: HashMap<LVar, VMAddr>,
  addr_map: VertreapMap<LVar, Option<VMAddr>>,
}

impl VMNamedEnvRef {
  //pub fn lookup(&self, name: LVar) -> VMValRef {
  pub fn lookup(&self, name: LVar) -> VMAddr {
    //match self.mval_map.get(&name) {
    //match self.addr_map.get(&name) {
    match self.addr_map.find(&name) {
      None => {
        eprintln!("env: missing var: {:?}", name);
        for kv in self.addr_map.iter() {
          eprintln!("  kv: {:?}, _", kv.k);
        }
        panic!();
      }
      Some(kv) => {
        match &kv.v {
          None => panic!("env: tried to lookup a reclaimed var: {:?}", name),
          Some(v) => v.clone(),
        }
      }
    }
  }

  //pub fn insert(&self, name: LVar, mval: VMValRef) -> VMEnvRef {
  pub fn insert(&self, name: LVar, addr: VMAddr) -> VMNamedEnvRef {
    // TODO
    /*let mut new_env = self.clone();
    //new_env.mval_map.insert(name, mval);
    new_env.addr_map.insert(name, addr);
    new_env*/
    VMNamedEnvRef{
      addr_map: self.addr_map.append(name, Some(addr)),
    }
  }

  pub fn reclaim(&self, name: LVar) -> VMNamedEnvRef {
    VMNamedEnvRef{
      addr_map: self.addr_map.append(name, None),
    }
  }
}

pub type VMKontRef = Rc<VMKont>;

pub enum VMKont {
  Halt,
  Pause,
  Thk0(VMAddr, VMLam, VMEnvRef, VMKontRef),
  //App0(VMEnvRef, VMKontRef),
  App(Option<VMClosure>, Vec<VMValRef>, VecDeque<LExpr>, VMEnvRef, VMKontRef),
  Ret(VMEnvRef, VMKontRef),
  AThk(LVar, VMAddr, VMLam, VMEnvRef, VMKontRef),
  ACons(LVar, VMAddr, VMEnvRef, VMKontRef),
  AConcatL(LExpr, VMEnvRef, VMKontRef),
  AConcatR(VMValRef, VMEnvRef, VMKontRef),
  AApp(Vec<LVar>, Vec<LVar>, VMEnvRef, VMKontRef),
  ERet(Vec<LVar>, VMEnvRef, VMKontRef),
  ESel(LVar, VMLam, VMEnvRef, VMKontRef),
  EImp(LExpr, VMEnvRef, VMKontRef),
  Swch(LExpr, LExpr, VMEnvRef, VMKontRef),
  Mch(VecDeque<(LPat, LExpr)>, VMEnvRef, VMKontRef),
  STup(Vec<LExpr>, Vec<VMValRef>, VMEnvRef, VMKontRef),
  Tup(Vec<LExpr>, Vec<VMValRef>, VMEnvRef, VMKontRef),
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
      &VMKont::Pause => "Pause",
      &VMKont::Thk0(..) => "Thk0",
      //&VMKont::App0(..) => "App0",
      &VMKont::App(..) => "App",
      &VMKont::Ret(..) => "Ret",
      &VMKont::AThk(..) => "AThk",
      &VMKont::ACons(..) => "ACons",
      &VMKont::AConcatL(..) => "AConcatL",
      &VMKont::AConcatR(..) => "AConcatR",
      &VMKont::AApp(..) => "AApp",
      &VMKont::ERet(..) => "ERet",
      &VMKont::ESel(..) => "ESel",
      &VMKont::EImp(..) => "EImp",
      &VMKont::Swch(..) => "Swch",
      &VMKont::Mch(..) => "Mch",
      &VMKont::STup(..) => "STup",
      &VMKont::Tup(..) => "Tup",
    }
  }
}

//pub type VMAddr = VMDebugAddr;
//pub type VMStore = VMDebugStore;

pub type VMAddr = VMRcAddr;
pub type VMStore = VMRcStore;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VMDebugAddr {
  pub raw:  u64,
}

#[derive(Default)]
pub struct VMDebugStore {
  mthk_map: HashMap<VMDebugAddr, VMThunkRef>,
  addr_ctr: u64,
}

impl VMDebugStore {
  pub fn nil_addr(&mut self) -> VMDebugAddr {
    VMDebugAddr{raw: 0}
  }

  pub fn fresh_addr(&mut self) -> VMDebugAddr {
    let new_addr = self.addr_ctr + 1;
    assert!(new_addr != 0);
    self.addr_ctr += 1;
    VMDebugAddr{raw: new_addr}
  }

  pub fn insert(&mut self, mthk: VMThunkRef) -> VMDebugAddr {
    let thk_a = self.fresh_addr();
    assert!(self.mthk_map.insert(thk_a.clone(), mthk).is_none());
    thk_a
  }

  pub fn lookup(&self, addr: VMDebugAddr) -> VMThunkRef {
    match self.mthk_map.get(&addr) {
      None => panic!(),
      Some(mthk) => mthk.clone(),
    }
  }

  pub fn update(&mut self, addr: VMDebugAddr, mval: VMValRef) {
    match self.mthk_map.get(&addr) {
      None => panic!(),
      Some(mthk) => {
        match mthk.state() {
          VMThunkState::Emp => {
            panic!("vm: runtime error: updating an empty thunk");
          }
          VMThunkState::Blk => {
            let mut mslot = mthk.slot.borrow_mut();
            *mslot = VMThunkSlot::Val(mval);
          }
          VMThunkState::Val => {
            panic!("bug");
          }
          VMThunkState::Rst => {
            panic!("bug");
          }
        }
      }
    }
  }
}

#[derive(Clone)]
pub struct VMRcAddr {
  pub ptr:  VMThunkRef,
}

impl Drop for VMRcAddr {
  fn drop(&mut self) {
    match Rc::get_mut(&mut self.ptr) {
      None => {}
      Some(mthk) => {
        let mut mslot = mthk.slot.borrow_mut();
        *mslot = VMThunkSlot::Rst;
      }
    }
  }
}

#[derive(Default)]
pub struct VMRcStore {
}

impl VMRcStore {
  pub fn insert(&mut self, mthk: VMThunkRef) -> VMRcAddr {
    VMRcAddr{ptr: mthk}
  }

  pub fn lookup(&self, thk_a: VMRcAddr) -> VMThunkRef {
    thk_a.ptr.clone()
  }

  pub fn update(&mut self, thk_a: VMRcAddr, mval: VMValRef) {
    match thk_a.ptr.state() {
      VMThunkState::Emp => {
        panic!("vm: runtime error: updating an empty thunk");
      }
      VMThunkState::Blk => {
        let mut mslot = thk_a.ptr.slot.borrow_mut();
        *mslot = VMThunkSlot::Val(mval);
      }
      VMThunkState::Val => {
        panic!("bug");
      }
      VMThunkState::Rst => {
        panic!("bug");
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
  pub lbuilder: Option<LBuilder>,
  pub _step_ct: usize,
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
      lbuilder: None,
      _step_ct: 0,
    }
  }

  pub fn with_lbuilder(lbuilder: LBuilder) -> VMachine {
    VMachine{
      cfg:      GlobalConfig::default(),
      ctrl:     VMReg::Uninit,
      env:      VMEnvRef::default(),
      kont:     VMKontRef::default(),
      store:    VMStore::default(),
      initsave: MSaveState::default(),
      lbuilder: Some(lbuilder),
      _step_ct: 0,
    }
  }

  pub fn take_lbuilder(&mut self) -> Option<LBuilder> {
    self.lbuilder.take()
  }

  pub fn put_lbuilder(&mut self, lbuilder: LBuilder) {
    self.lbuilder = Some(lbuilder);
  }

  pub fn _debug_dump_ctrl(&self) {
    match &self.ctrl {
      &VMReg::Uninit => println!("DEBUG: vm: ctrl: uninit"),
      &VMReg::Code(_) => println!("DEBUG: vm: ctrl: code"),
      &VMReg::BCode(..) => println!("DEBUG: vm: ctrl: bcode"),
      &VMReg::MVal(ref mval) => {
        match &**mval {
          VMVal::Clo(_) => println!("DEBUG: vm: ctrl: mval: closure"),
          VMVal::STup(elems) => println!("DEBUG: vm: ctrl: mval: s-tuple (num elems: {})", elems.len()),
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
        &VMKont::Halt |
        &VMKont::Pause => break,
        /*&VMKont::Lkd(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }*/
        &VMKont::Thk0(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        /*&VMKont::App0(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }*/
        &VMKont::App(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::Ret(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::AThk(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::ACons(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::AConcatL(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::AConcatR(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::AApp(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::ERet(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::ESel(.., ref prev_kont) => {
          depth += 1;
          kont = prev_kont.clone();
        }
        &VMKont::EImp(.., ref prev_kont) => {
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
        &VMKont::STup(.., ref prev_kont) => {
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
    let thk_a = self.env.lookup(var);
    let mthk = self.store.lookup(thk_a.clone());
    (thk_a, mthk)
  }

  pub fn _lookup(&self, var: LVar) -> VMValRef {
    // TODO
    let addr = self.env.lookup(var);
    let mthk = self.store.lookup(addr);
    let mslot = mthk.slot.borrow();
    match &*mslot {
      &VMThunkSlot::Val(ref mval) => mval.clone(),
      _ => panic!(),
    }
  }

  pub fn _reset(&mut self, ltree: LExpr) {
    self.ctrl = VMReg::Code(ltree);
    self.env = VMEnvRef::default();
    self.kont = VMKontRef::default();
    self._step_ct = 0;
  }

  pub fn _reset_interactive(&mut self, ltree: LExpr) {
    self.ctrl = VMReg::Code(ltree);
    self.env = VMEnvRef::default();
    self.kont = VMKontRef::new(VMKont::Pause);
    self._step_ct = 0;
  }

  /*pub fn _reset(&mut self, lb: LBuilder, ltree: LExpr) {
    // FIXME
    unimplemented!();
  }*/

  pub fn _is_halted(&self) -> bool {
    match (&self.ctrl, &*self.kont) {
      (&VMReg::MVal(_), &VMKont::Halt) => true,
      _ => false,
    }
  }

  pub fn _is_paused(&self) -> bool {
    match (&self.ctrl, &*self.kont) {
      (&VMReg::Uninit, &VMKont::Pause) => true,
      _ => false,
    }
  }

  pub fn _step(&mut self) {
    // TODO
    println!("TRACE: vm: step");
    self._step_ct += 1;
    let ctrl = self.ctrl.clone();
    let env = self.env.clone();
    let kont = self.kont.clone();
    let (next_ctrl, next_env, next_kont) = match ctrl {
      VMReg::Uninit => {
        panic!();
      }
      VMReg::Code(ltree) => {
        match (&*ltree.term, &*kont) {
          (&LTerm::End, &VMKont::Pause) => {
            println!("TRACE: vm:   expr: end");
            let next_ctrl = VMReg::Uninit;
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Apply(ref head, ref args), &VMKont::Ret(ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   expr: apply (tail)");
            let next_ctrl = VMReg::Code(head.clone());
            let next_kont = VMKontRef::new(VMKont::App(None, Vec::new(), VecDeque::from_iter(args.iter().map(|a| a.clone())), saved_env.clone(), saved_kont.clone()));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Apply(ref head, ref args), _) => {
            println!("TRACE: vm:   expr: apply");
            let next_ctrl = VMReg::Code(head.clone());
            let next_kont = VMKontRef::new(VMKont::App(None, Vec::new(), VecDeque::from_iter(args.iter().map(|a| a.clone())), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::AEnv(ref kvs), _) => {
            println!("TRACE: vm:   expr: a-env");
            if kvs.is_empty() {
              let mval = VMValRef::new(VMVal::AEnv(VMAEnv{
                free: HashMap::new(),
                bind: Vec::new(),
              }));
              let next_ctrl = VMReg::MVal(mval);
              let next_env = env;
              let next_kont = kont;
              (next_ctrl, next_env, next_kont)
            } else {
              panic!();
            }
          }
          (&LTerm::AConcat(ref lhs, ref rhs), _) => {
            println!("TRACE: vm:   expr: a-env concat");
            match &*lhs.term {
              &LTerm::AEnv(ref lhs_kvs) => {
                if lhs_kvs.is_empty() {
                  let next_ctrl = VMReg::Code(rhs.clone());
                  let next_env = env;
                  let next_kont = kont;
                  (next_ctrl, next_env, next_kont)
                } else if lhs_kvs.len() == 1 {
                  let lhs_mlam = VMLam{
                    code: VMLamCode::LCode(Vec::new(), lhs_kvs[0].1.clone()),
                  };
                  let rhs_mlam = VMLam{
                    code: VMLamCode::LCode(Vec::new(), rhs.clone()),
                  };
                  let key_var = match lhs_kvs[0].0.clone() {
                    LEnvKey::Var(v) => v,
                    _ => panic!(),
                  };
                  let mthk = VMThunkRef::new(VMThunk::new_blkhole(lhs_mlam, env.clone()));
                  let thk_a = self.store.insert(mthk);
                  let next_ctrl = VMReg::Code(lhs_kvs[0].1.clone());
                  let next_kont = VMKontRef::new(VMKont::AThk(key_var, thk_a, rhs_mlam, env.clone(), kont));
                  let next_env = env;
                  (next_ctrl, next_env, next_kont)
                } else {
                  panic!();
                }
              }
              //_ => unimplemented!(),
              //_ => panic!("TRACE: vm: unimplemented code: {:?}", lhs.term),
              _ => {
                let next_ctrl = VMReg::Code(lhs.clone());
                let next_kont = VMKontRef::new(VMKont::AConcatL(rhs.clone(), env.clone(), kont));
                let next_env = env;
                (next_ctrl, next_env, next_kont)
              }
            }
          }
          (&LTerm::AApp(ref args, ref arg_adjs, ref target), _) => {
            println!("TRACE: vm:   expr: a-env apply");
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::AApp(args.clone(), arg_adjs.clone(), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::ERet(ref params, ref target), _) => {
            println!("TRACE: vm:   expr: env return");
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::ERet(params.clone(), env.clone(), kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::ESelect(ref target, ref name), _) => {
            println!("TRACE: vm:   expr: env select");
            let lookup_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), ltree.clone()),
            };
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::ESel(name.clone(), lookup_mlam, env.clone(), kont));
            let next_env = env.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::EImport(ref target, ref rest), _) => {
            println!("TRACE: vm:   expr: env import");
            let lookup_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), ltree.clone()),
            };
            let next_ctrl = VMReg::Code(target.clone());
            let next_kont = VMKontRef::new(VMKont::EImp(rest.clone(), env.clone(), kont));
            let next_env = env.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Lambda(ref params, ref body), _) => {
            // TODO
            println!("TRACE: vm:   capturing lambda...");
            for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              lam: VMLam{
                code: VMLamCode::LCode(params.clone(), body.clone()),
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
          (&LTerm::VMExt(LVMExt::BCLambda(ref _params, ref bcdef)), _) => {
            // TODO
            println!("TRACE: vm:   capturing bc lambda...");
            /*for kv in env.addr_map.iter() {
              println!("TRACE: vm:     kv: {:?}, _", kv.k);
            }*/
            let mval = VMValRef::new(VMVal::Clo(VMClosure{
              lam: VMLam{
                code: VMLamCode::BCode(bcdef.ar, match bcdef.cg {
                  None => panic!("vm: runtime error: bc lambda missing codegen"),
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
            let body_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), body.clone()),
            };
            let rest_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), rest.clone()),
            };
            // NB: The thunk will be immediately updated, so can directly
            // construct it in the "black hole" state.
            let mthk = VMThunkRef::new(VMThunk::new_blkhole(/*thk_a.clone(),*/ body_mlam, env.clone()));
            let thk_a = self.store.insert(mthk);
            // NB: The `Thk0` continuation does not create bind the var to the
            // thunk address, instead that happens here.
            let rest_env = env.insert(name.clone(), thk_a.clone());
            let next_ctrl = VMReg::Code(body.clone());
            let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, rest_mlam, rest_env, kont));
            let next_env = env;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Fix(ref fixname, ref fixbody), _) => {
            println!("TRACE: vm:   expr: fix");
            let fix_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), ltree.clone()),
            };
            // NB: The fixpoint thunk maybe delayed, so must construct it in
            // the "empty" state.
            // TODO: should `mthk` capture `env` or `fix_env`?
            //let thk_a = self.store.fresh_addr();
            let mthk = VMThunkRef::new(VMThunk::new_empty(/*thk_a.clone(),*/ fix_mlam, env.clone()));
            let thk_a = self.store.insert(mthk);
            // FIXME: this next part needs some reworking, as the current env is
            // basically overwritten with `fix_env`.
            /*let fixbody_mlam = VMLam{
              code: VMLamCode::LCode(Vec::new(), fixbody.clone()),
            };*/
            let fix_env = env.insert(fixname.clone(), thk_a);
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
          (&LTerm::STuple(ref args), _) => {
            println!("TRACE: vm:   expr: s-tuple");
            if args.is_empty() {
              let mval = VMValRef::new(VMVal::STup(vec![]));
              let next_ctrl = VMReg::MVal(mval);
              let next_env = env;
              let next_kont = kont;
              (next_ctrl, next_env, next_kont)
            } else {
              let next_ctrl = VMReg::Code(args[0].clone());
              let next_kont = VMKontRef::new(VMKont::STup(args.clone(), vec![], env.clone(), kont));
              let next_env = env;
              (next_ctrl, next_env, next_kont)
            }
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
          (&LTerm::FloLit(x), _) => {
            println!("TRACE: vm:   expr: flolit");
            let mval = VMValRef::new(VMVal::Flo(x));
            let next_ctrl = VMReg::MVal(mval);
            let next_env = env;
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          (&LTerm::Lookup(ref name), _) => {
            println!("TRACE: vm:   expr: lookup: {:?}", name);
            let thk_a = self.env.lookup(name.clone());
            let mthk = self.store.lookup(thk_a.clone());
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                let rest_mlam = VMLam{
                  code: VMLamCode::LCode(Vec::new(), ltree.clone()),
                };
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::NoExe => panic!("vm: runtime error"),
                  VMLamCode::LCode(_, e) => VMReg::Code(e),
                  VMLamCode::BCode(_, bc) => VMReg::BCode(bc, Vec::new()),
                };
                let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, rest_mlam, env.clone(), kont));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:     end emp");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Blk => {
                panic!("invalid thunk state (blkhole)");
              }
              VMThunkState::Val => {
                println!("TRACE: vm:   expr:   val...");
                let mslot = mthk.slot.borrow();
                let mval = match &*mslot {
                  &VMThunkSlot::Val(ref mval) => mval.clone(),
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
                println!("TRACE: vm:   expr:     end val");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Rst => {
                panic!("invalid thunk state (reset)");
              }
            }
          }
          (&LTerm::VMExt(LVMExt::Deref(ref thk_a)), _) => {
            println!("TRACE: vm:   expr: deref");
            let mthk = self.store.lookup(thk_a.clone());
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                let rest_mlam = VMLam{
                  code: VMLamCode::LCode(Vec::new(), ltree.clone()),
                };
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::NoExe => panic!("vm: runtime error"),
                  VMLamCode::LCode(_, e) => VMReg::Code(e),
                  VMLamCode::BCode(_, bc) => VMReg::BCode(bc, Vec::new()),
                };
                let next_kont = VMKontRef::new(VMKont::Thk0(thk_a.clone(), rest_mlam, env.clone(), kont));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:     end emp");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Blk => {
                panic!("invalid thunk state (blkhole)");
              }
              VMThunkState::Val => {
                println!("TRACE: vm:   expr:   val...");
                let mslot = mthk.slot.borrow();
                let mval = match &*mslot {
                  &VMThunkSlot::Val(ref mval) => mval.clone(),
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
                println!("TRACE: vm:   expr:     end val");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Rst => {
                panic!("invalid thunk state (reset)");
              }
            }
          }
          (&LTerm::Reclaim(ref var, ref rest), _) => {
            println!("TRACE: vm:   expr: reclaim: {:?}", var);
            let next_ctrl = VMReg::Code(rest.clone());
            let next_env = env.reclaim(var.clone());
            let next_kont = kont;
            (next_ctrl, next_env, next_kont)
          }
          _ => panic!("TRACE: unimplemented: code: {:?} kont: {}", &*ltree.term, kont._kont_name()),
        }
      }
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
          (_, &VMKont::AThk(ref key_var, ref thk_a, ref rest_mlam, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            self.store.update(thk_a.clone(), mval);
            let next_ctrl = match rest_mlam.code.clone() {
              VMLamCode::NoExe => panic!("vm: runtime error"),
              VMLamCode::LCode(_, e) => VMReg::Code(e),
              VMLamCode::BCode(_, bc) => VMReg::BCode(bc, Vec::new()),
            };
            let next_kont = VMKontRef::new(VMKont::ACons(key_var.clone(), thk_a.clone(), saved_env.clone(), saved_kont.clone()));
            let next_env = saved_env.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&VMVal::AEnv(ref tg_env), &VMKont::ACons(ref key_var, ref thk_a, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let mut new_tg_env = tg_env.clone();
            match new_tg_env.free.get(key_var) {
              None => {
                new_tg_env.free.insert(key_var.clone(), thk_a.clone());
              }
              Some(tg_thk_a) => {
                let tg_thk_a = tg_thk_a.clone();
                let join_code = self.lbuilder.as_mut().unwrap().apply_term(
                    // FIXME: hardcoded `add` (assumes standard prelude).
                    &mut |lb| lb.lookup_term(LVar(1)),
                    vec![
                      &mut |lb| lb.vm_deref_term(thk_a.clone()),
                      &mut |lb| lb.vm_deref_term(tg_thk_a.clone()),
                    ]
                );
                let join_mlam = VMLam{code: VMLamCode::LCode(Vec::new(), join_code)};
                let join_mthk = VMThunkRef::new(VMThunk::new_empty(join_mlam, env.clone()));
                let join_thk_a = self.store.insert(join_mthk);
                new_tg_env.free.insert(key_var.clone(), join_thk_a);
              }
            }
            let new_mval = VMValRef::new(VMVal::AEnv(new_tg_env));
            let next_ctrl = VMReg::MVal(new_mval);
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::ACons(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref lhs_env), &VMKont::AConcatL(ref rhs, ref saved_env, ref saved_kont)) => {
            let next_ctrl = VMReg::Code(rhs.clone());
            let next_kont = VMKontRef::new(VMKont::AConcatR(mval.clone(), saved_env.clone(), saved_kont.clone()));
            let next_env = saved_env.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::AConcatL(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref rhs_env), &VMKont::AConcatR(ref lhs_mval, ref saved_env, ref saved_kont)) => {
            let concat_env = match &**lhs_mval {
              &VMVal::AEnv(ref lhs_env) => {
                // FIXME: bind keys?
                let mut concat_env = rhs_env.clone();
                for (k, lv) in lhs_env.free.iter() {
                  if concat_env.free.contains_key(k) {
                    //println!("WARNING: vm: a-env concat impl unfinished");
                    let rv = concat_env.free.get(k).unwrap();
                    let (thk_a, tg_thk_a) = match (lv, rv) {
                      (thk_a, tg_thk_a) => (thk_a.clone(), tg_thk_a.clone())
                    };
                      /*(&VMAValue::Addr(ref thk_a), &VMAValue::Addr(ref tg_thk_a)) => (thk_a.clone(), tg_thk_a.clone()),
                      (&VMAValue::Addr(ref thk_a), &VMAValue::Cons(ref tg_thk_a, ..)) => (thk_a.clone(), tg_thk_a.clone()),
                      (&VMAValue::Cons(ref thk_a, ..), &VMAValue::Addr(ref tg_thk_a)) => (thk_a.clone(), tg_thk_a.clone()),
                      (&VMAValue::Cons(ref thk_a, ..), &VMAValue::Cons(ref tg_thk_a, ..)) => (thk_a.clone(), tg_thk_a.clone()),
                    };*/
                    let join_code = self.lbuilder.as_mut().unwrap().apply_term(
                        // FIXME: hardcoded `add` (assumes standard prelude).
                        &mut |lb| lb.lookup_term(LVar(1)),
                        vec![
                          &mut |lb| lb.vm_deref_term(thk_a.clone()),
                          &mut |lb| lb.vm_deref_term(tg_thk_a.clone()),
                        ]
                    );
                    let join_mlam = VMLam{code: VMLamCode::LCode(Vec::new(), join_code)};
                    let join_mthk = VMThunkRef::new(VMThunk::new_empty(join_mlam, env.clone()));
                    let join_thk_a = self.store.insert(join_mthk);
                    concat_env.free.insert(k.clone(), join_thk_a);
                  } else {
                    concat_env.free.insert(k.clone(), lv.clone());
                  }
                }
                concat_env
              }
              _ => panic!("vm: runtime error"),
            };
            let next_ctrl = VMReg::MVal(VMValRef::new(VMVal::AEnv(concat_env)));
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::AConcatR(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref tg_env), &VMKont::AApp(ref args, ref _arg_adjs, ref saved_env, ref saved_kont)) => {
            // FIXME: concat with arg adjs.
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let mut new_tg_env = tg_env.clone();
            assert_eq!(args.len(), new_tg_env.bind.len());
            for (a, b) in args.iter().zip(new_tg_env.bind.iter()) {
              match new_tg_env.free.remove(b) {
                None => {}
                Some(v) => {
                  match new_tg_env.free.get(a) {
                    None => {
                      new_tg_env.free.insert(a.clone(), v);
                    }
                    Some(tg_thk_a) => {
                      let thk_a = v;
                        /*VMAValue::Addr(thk_a) => thk_a,
                        VMAValue::Cons(thk_a, ..) => thk_a,
                      };*/
                      let tg_thk_a = tg_thk_a.clone();
                      let join_code = self.lbuilder.as_mut().unwrap().apply_term(
                          // FIXME: hardcoded `add` (assumes standard prelude).
                          &mut |lb| lb.lookup_term(LVar(1)),
                          vec![
                            &mut |lb| lb.vm_deref_term(thk_a.clone()),
                            &mut |lb| lb.vm_deref_term(tg_thk_a.clone()),
                          ]
                      );
                      let join_mlam = VMLam{code: VMLamCode::LCode(Vec::new(), join_code)};
                      let join_mthk = VMThunkRef::new(VMThunk::new_empty(join_mlam, env.clone()));
                      let join_thk_a = self.store.insert(join_mthk);
                      new_tg_env.free.insert(a.clone(), join_thk_a);
                    }
                  }
                }
              }
            }
            new_tg_env.bind.clear();
            let new_mval = VMValRef::new(VMVal::AEnv(new_tg_env));
            let next_ctrl = VMReg::MVal(new_mval);
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::AApp(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref tg_env), &VMKont::ERet(ref params, ref saved_env, ref saved_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let mut new_tg_env = tg_env.clone();
            assert_eq!(new_tg_env.bind.len(), 0);
            for p in params.iter() {
              new_tg_env.bind.push(p.clone());
            }
            let new_mval = VMValRef::new(VMVal::AEnv(new_tg_env));
            let next_ctrl = VMReg::MVal(new_mval);
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::ERet(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref tg_env), &VMKont::ESel(ref name, ref lookup_mlam, ref saved_env, ref saved_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let thk_a = match tg_env.free.get(name) {
              None => panic!(),
              Some(a) => a.clone(),
            };
            let mthk = self.store.lookup(thk_a.clone());
            match mthk.state() {
              VMThunkState::Emp => {
                println!("TRACE: vm:   expr:   emp...");
                // NB: Must explicitly transition the thunk to a "black hole"
                // state using `_prep_update`.
                mthk._prep_update();
                let next_ctrl = match mthk.lam.code.clone() {
                  VMLamCode::NoExe => panic!("vm: runtime error"),
                  VMLamCode::LCode(_, e) => VMReg::Code(e),
                  VMLamCode::BCode(_, bc) => VMReg::BCode(bc, Vec::new()),
                };
                let next_kont = VMKontRef::new(VMKont::Thk0(thk_a, lookup_mlam.clone(), saved_env.clone(), saved_kont.clone()));
                let next_env = mthk.env.clone();
                println!("TRACE: vm:   expr:     end emp");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Blk => {
                panic!("invalid thunk state (blkhole)");
              }
              VMThunkState::Val => {
                println!("TRACE: vm:   kont:   val...");
                let mval = match &*mthk.slot.borrow() {
                  &VMThunkSlot::Val(ref mval) => mval.clone(),
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
                println!("TRACE: vm:   kont:     end val");
                (next_ctrl, next_env, next_kont)
              }
              VMThunkState::Rst => {
                panic!("invalid thunk state (reset)");
              }
            }
          }
          (_, &VMKont::ESel(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (&VMVal::AEnv(ref tg_env), &VMKont::EImp(ref rest, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let next_ctrl = VMReg::Code(rest.clone());
            let next_kont = VMKontRef::new(VMKont::Ret(saved_env.clone(), saved_kont.clone()));
            let next_env = {
              // FIXME
              let mut next_env = VMNamedEnvRef::default();
              for (k, v) in tg_env.free.iter() {
                next_env = next_env.insert(k.clone(), v.clone());
              }
              next_env
            };
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::EImp(..)) => {
            panic!("bug: mval: {} kont: {}", mval._mval_name(), kont._kont_name());
          }
          (_, &VMKont::Thk0(ref thk_a, ref rest_mlam, ref saved_env, ref saved_kont)) => {
            // TODO
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            self.store.update(thk_a.clone(), mval);
            let next_ctrl = match rest_mlam.code.clone() {
              VMLamCode::NoExe => panic!("vm: runtime error"),
              VMLamCode::LCode(_, e) => VMReg::Code(e),
              VMLamCode::BCode(_, bc) => VMReg::BCode(bc, Vec::new()),
            };
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&VMVal::Clo(ref closure), &VMKont::App(None, ref arg_mvals, ref arg_codes, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {} (closure)", kont._kont_name());
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
                  VMLamCode::NoExe => panic!("vm: runtime error"),
                  VMLamCode::LCode(params, body) => {
                    assert!(params.is_empty());
                    VMReg::Code(body)
                  }
                  VMLamCode::BCode(_, bc) => {
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
            println!("TRACE: vm:   kont: {} (arg)", kont._kont_name());
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
                  VMLamCode::NoExe => panic!("vm: runtime error"),
                  VMLamCode::LCode(params, body) => {
                    let arg_mvals = next_arg_mvals;
                    assert_eq!(params.len(), arg_mvals.len());
                    let mut next_env = closure.env.clone();
                    for (pv, p_mval) in params.into_iter().zip(arg_mvals.iter()) {
                      let mthk = VMThunkRef::new(VMThunk::new_blkhole_tmp(/*thk_a.clone(),*/ env.clone()));
                      let thk_a = self.store.insert(mthk);
                      self.store.update(thk_a.clone(), p_mval.clone());
                      next_env = next_env.insert(pv, thk_a);
                    }
                    let next_ctrl = VMReg::Code(body);
                    let next_kont = VMKontRef::new(VMKont::Ret(saved_env.clone(), saved_kont.clone()));
                    (next_ctrl, next_env, next_kont)
                  }
                  VMLamCode::BCode(arity, bc) => {
                    assert_eq!(arity, next_arg_mvals.len());
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
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let next_ctrl = VMReg::MVal(mval);
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (&VMVal::Bit(x), &VMKont::Swch(ref top_code, ref bot_code, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let next_ctrl = VMReg::Code(match x {
              true  => top_code.clone(),
              false => bot_code.clone(),
            });
            let next_env = saved_env.clone();
            let next_kont = saved_kont.clone();
            (next_ctrl, next_env, next_kont)
          }
          (_, &VMKont::Swch(..)) => {
            panic!("vm: runtime error: switch expected bit value");
          }
          (_, &VMKont::Mch(ref pat_arms, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
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
                      let mthk = VMThunkRef::new(VMThunk::new_blkhole_tmp(/*thk_a.clone(),*/ env.clone()));
                      let thk_a = self.store.insert(mthk);
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
          (_, &VMKont::STup(ref elem_codes, ref elem_mvals, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
            let mut elem_mvals = elem_mvals.clone();
            elem_mvals.push(mval);
            if elem_codes.len() < elem_mvals.len() {
              panic!();
            } else if elem_codes.len() == elem_mvals.len() {
              let next_ctrl = VMReg::MVal(VMValRef::new(VMVal::STup(elem_mvals)));
              let next_env = saved_env.clone();
              let next_kont = saved_kont.clone();
              (next_ctrl, next_env, next_kont)
            } else if elem_codes.len() > elem_mvals.len() {
              let next_ctrl = VMReg::Code(elem_codes[elem_mvals.len()].clone());
              let next_kont = VMKontRef::new(VMKont::STup(elem_codes.clone(), elem_mvals, saved_env.clone(), saved_kont.clone()));
              let next_env = env.clone();
              (next_ctrl, next_env, next_kont)
            } else {
              unreachable!();
            }
          }
          (_, &VMKont::Tup(ref elem_codes, ref elem_mvals, ref saved_env, ref saved_kont)) => {
            println!("TRACE: vm:   kont: {}", kont._kont_name());
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
    while !self._is_halted() {
      self._step()
    }
  }

  pub fn eval(&mut self, ltree: LExpr) -> VMValRef {
    self._reset(ltree);
    self._eval();
    match (&self.ctrl, &*self.kont) {
      (&VMReg::MVal(ref mval), &VMKont::Halt) => mval.clone(),
      _ => unreachable!(),
    }
  }

  pub fn load_interactive(&mut self, ltree: LExpr) {
    self._reset_interactive(ltree);
    while !self._is_paused() {
      self._step();
    }
  }

  pub fn eval_interactive(&mut self, ltree: LExpr) {
    // TODO
    match (&self.ctrl, &*self.kont) {
      (_, &VMKont::Pause) => {}
      _ => panic!(),
    }
    self.ctrl = VMReg::Code(ltree);
    while !self._is_paused() {
      self._step();
    }
  }

  pub fn _debug_eval(&mut self, ltree: Option<LExpr>, nsteps: usize) {
    if let Some(ltree) = ltree {
      self._reset(ltree);
    }
    for _ in 0 .. nsteps {
      if self._is_halted() {
        break;
      }
      self._step()
    }
  }

  pub fn _step_count(&self) -> usize {
    self._step_ct
  }
}
