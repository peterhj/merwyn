use std::cell::{RefCell, RefMut};
use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, Default)]
pub struct MStack {
  pub vals: Vec<MValue>,
}

#[derive(Clone, Default)]
pub struct MTmpStack {
  pub vals: Vec<MUnboxedValue>,
}

#[derive(Clone)]
pub struct MProgramAddr {
  pub seg:  usize,
  pub pos:  usize,
}

impl MProgramAddr {
  pub fn inc(&mut self) {
    self.pos += 1;
  }

  pub fn next(&self) -> MProgramAddr {
    MProgramAddr{seg: self.seg, pos: self.pos + 1}
  }
}

#[derive(Clone, Default)]
pub struct MProgramSegment {
  pub insts:    Vec<MInst>,
}

#[derive(Clone, Default)]
pub struct MProgram {
  pub insts:    Vec<MInst>,
  pub segments: Vec<MProgramSegment>,
}

#[derive(Clone)]
pub enum MBoxedValue {
  Closure(MClosureRef),
  Thunk(MThunkRef),
}

impl MBoxedValue {
  pub fn into_unboxed(self) -> MUnboxedValue {
    match self {
      MBoxedValue::Closure(closure) => MUnboxedValue::Closure(closure),
      MBoxedValue::Thunk(thunk) => MUnboxedValue::Thunk(thunk),
    }
  }
}

#[derive(Clone)]
pub enum MUnboxedValue {
  Addr(MProgramAddr),
  Data(MData),
  IndexEnv(MIndexEnv),
  Closure(MClosureRef),
  //RClosure(MRClosure),
  Thunk(MThunkRef),
}

impl MUnboxedValue {
  pub fn into_boxed(self) -> MBoxedValue {
    match self {
      MUnboxedValue::Closure(closure) => MBoxedValue::Closure(closure),
      MUnboxedValue::Thunk(thunk) => MBoxedValue::Thunk(thunk),
      _ => panic!("cannot box this unboxed value"),
    }
  }
}

#[derive(Clone)]
pub enum MValue {
  Data(MData),
  Thunk(MThunk),
  Env(MEnv),
  Index(usize),
  Closure(MClosure),
  ClosureRef(MClosureRef),
  ThunkRef(MThunkRef),
  IndexEnv(MIndexEnv),
  CodeAddr(MProgramAddr),
}

impl MValue {
  pub fn data(&self) -> MData {
    match self {
      MValue::Data(ref data) => {
        data.clone()
      }
      MValue::Thunk(ref thunk) => {
        match thunk.retval {
          Some(ref val) => {
            match (**val).clone() {
              MValue::Data(ref data) => {
                data.clone()
              }
              _ => {
                panic!("FATAL: attempting to unbox a non data-valued thunk");
              }
            }
          }
          None => {
            panic!("FATAL: attempting to unbox an empty thunk");
          }
        }
      }
      MValue::Env(_) => {
        panic!("FATAL: attempting to unbox an env");
      }
      _ => panic!(),
    }
  }
}

#[derive(Clone)]
pub enum MUnboxedData {
  U32(u32),
  F32(f32),
  //Blackbox(Rc<()>),
}

#[derive(Clone)]
pub struct MData {
  pub inner:    f32,
  //pub inner:    MUnboxedData,
}

#[derive(Clone)]
pub enum MClosureCode {
  Addr(MProgramAddr),
  OpDef(MOpDef),
}

#[derive(Clone)]
pub struct MClosure {
  pub env:  MEnv,
  pub ienv: MIndexEnv,
  pub code: MClosureCode,
}

#[derive(Clone)]
pub struct MClosureRef {
  pub code: MClosureCode,
  pub env:  MIndexEnv,
}

//#[derive(Clone, Copy)]
pub enum MThunkStatus {
  Empty,
  BlackHole,
  Unbox,
}

pub enum MThunkPayload {
  Empty,
  BlackHole,
  Unbox(MUnboxedValue),
}

#[derive(Clone)]
pub struct MThunkRef {
  pub code: MClosureCode,
  pub env:  MIndexEnv,
  pub ret:  Rc<RefCell<MThunkPayload>>,
}

impl MThunkRef {
  pub fn status(&self) -> MThunkStatus {
    match &*self.ret.borrow() {
      &MThunkPayload::Empty => MThunkStatus::Empty,
      &MThunkPayload::BlackHole => MThunkStatus::BlackHole,
      &MThunkPayload::Unbox(_) => MThunkStatus::Unbox,
    }
  }

  pub fn force_reset(&self) {
    RefMut::map(self.ret.borrow_mut(), |payload| {
      match payload {
        &mut MThunkPayload::Empty => {}
        &mut MThunkPayload::BlackHole => {
          panic!();
        }
        &mut MThunkPayload::Unbox(_) => {
          *payload = MThunkPayload::Empty;
        }
      }
      payload
    });
  }

  pub fn force_blackhole(&self) {
    RefMut::map(self.ret.borrow_mut(), |payload| {
      match payload {
        &mut MThunkPayload::Empty => {
          *payload = MThunkPayload::BlackHole;
        }
        &mut MThunkPayload::BlackHole => {
          panic!("thunk already in blackhole state");
        }
        &mut MThunkPayload::Unbox(_) => {
          panic!();
        }
      }
      payload
    });
  }

  pub fn force_update(&self, new_value: MUnboxedValue) {
    RefMut::map(self.ret.borrow_mut(), |payload| {
      match payload {
        &mut MThunkPayload::Empty => {
          panic!("attempting to force update an empty thunk");
        }
        &mut MThunkPayload::BlackHole => {
          *payload = MThunkPayload::Unbox(new_value);
        }
        &mut MThunkPayload::Unbox(_) => {
          panic!("attempting to force update a full thunk");
        }
      }
      payload
    });
  }
}

#[derive(Clone)]
pub struct MThunk {
  // TODO
  pub closure:  MClosure,
  pub retval:   Option<Rc<MValue>>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MIdent {
  pub uniq:     u64,
  //pub name:     String,
}

#[derive(Clone, Default)]
pub struct MEnv {
  pub id_to_val:    HashMap<MIdent, MValue>,
}

#[derive(Clone, Default)]
pub struct MIndexEnv {
  pub vals: Vec<MBoxedValue>,
}

#[derive(Clone)]
pub enum MOpDef {
  Add,
  Mul,
  Div,
}

#[derive(Clone)]
pub enum MInst {
  Get(MIdent),
  Put(MIdent),
  Push,
  Swap,
  Lookup(usize),
  Bind,
  Unbind,
  Quote(f32),
  Close(MProgramAddr),
  CloseOp(MOpDef),
  Closure(MProgramAddr),
  RClosure(MProgramAddr),
  Thunk(MProgramAddr),
  Update0,
  Eval0,
  Apply0,
  Apply1,
  Apply2,
  ApplyBuiltin(MOpDef),
  Return,
  Eval,
  Breakpt,
  Halt,
}

#[derive(Clone, Default)]
pub struct MStepFlags {
  pub done:     bool,
  pub breakpt:  bool,
}

pub struct Machine {
  pub register: MValue,
  pub env:      MEnv,
  pub ienv:     MIndexEnv,
  pub stack:    MStack,
  pub tmpstack: MTmpStack,
  pub program:  MProgram,
  pub pc:       MProgramAddr,
  pub done:     bool,
}

#[no_mangle]
pub extern "C" fn hebb_machine_new() -> *mut Machine {
  Box::into_raw(Box::new(Machine::new()))
}

#[no_mangle]
pub unsafe extern "C" fn hebb_machine_drop(mach: *mut Machine) {
  let _mach = Box::from_raw(mach);
}

impl Machine {
  pub fn new() -> Machine {
    Machine{
      register: MValue::Env(MEnv::default()),
      env:      MEnv::default(),
      ienv:     MIndexEnv::default(),
      stack:    MStack::default(),
      tmpstack: MTmpStack::default(),
      program:  MProgram::default(),
      pc:       MProgramAddr{seg: 0, pos: 0},
      done:     false,
    }
  }

  pub fn reset(&mut self) {
    // TODO
  }

  pub fn set_env(&mut self, id: MIdent, val: MValue) {
    match self.register {
      MValue::Env(ref mut env) => {
        env.id_to_val.insert(id, val);
      }
      _ => panic!(),
    }
  }

  pub fn push_inst(&mut self, inst: MInst) -> MProgramAddr {
    let addr = MProgramAddr{seg: 0, pos: self.program.insts.len()};
    self.program.insts.push(inst);
    addr
  }

  pub fn push_segment(&mut self, segment: MProgramSegment) -> usize {
    let seg = self.program.segments.len();
    self.program.segments.push(segment);
    seg
  }

  pub fn inspect_reg(&self) {
    match self.register {
      MValue::Data(ref data) => {
        println!("DEBUG: Machine: inspect_reg: data: {:?}", data.inner);
      }
      MValue::Thunk(ref thunk) => {
        match thunk.retval {
          Some(ref val) => {
            match (**val).clone() {
              MValue::Data(ref data) => {
                println!("DEBUG: Machine: inspect_reg: thunk: retval: {:?}", data.inner);
              }
              _ => {
                println!("DEBUG: Machine: inspect_reg: thunk: retval: (some)");
              }
            }
          }
          None => {
            println!("DEBUG: Machine: inspect_reg: thunk: retval: (none)");
          }
        }
      }
      _ => {
        println!("DEBUG: Machine: inspect_reg: other");
      }
    }
  }

  pub fn _builtin_opdef_info(&self, opdef: MOpDef) -> (usize, MProgramAddr) {
    let (arity, seg) = match opdef {
      MOpDef::Add => (2, 1),
      MOpDef::Mul => (2, 2),
      MOpDef::Div => (2, 3),
    };
    (arity, MProgramAddr{seg, pos: 0})
  }

  pub fn run_v2(&mut self) {
    loop {
      let flags = self.step_v2();
      if flags.done || flags.breakpt {
        return;
      }
    }
  }

  pub fn step_v2(&mut self) -> MStepFlags {
    let mut flags = MStepFlags::default();
    match self.program.insts[self.pc.pos].clone() {
      MInst::Lookup(idx) => {
        let envlen = self.ienv.vals.len();
        let val = self.ienv.vals[envlen - idx].clone();
        self.tmpstack.vals.push(val.into_unboxed());
        self.pc.inc();
      }
      MInst::Bind => {
        let val = self.tmpstack.vals.pop().unwrap();
        self.ienv.vals.push(val.into_boxed());
        self.pc.inc();
      }
      MInst::Unbind => {
        let _val = self.ienv.vals.pop().unwrap();
        self.pc.inc();
      }
      MInst::Quote(rawdata) => {
        // TODO
      }
      /*MInst::Close(addr) => {
        let close_env = self.ienv.clone();
        let closure_v = MValue::Closure(MClosure{
          code: MClosureCode::Addr(addr),
          env:  MEnv::default(),
          ienv: close_env,
        });
        self.tmpstack.vals.push(closure_v);
        self.pc.inc();
      }*/
      MInst::Closure(addr) => {
        // TODO
        let close_env = self.ienv.clone();
        let closure_v = MUnboxedValue::Closure(MClosureRef{
          code: MClosureCode::Addr(addr),
          env:  close_env,
        });
        self.tmpstack.vals.push(closure_v);
        self.pc.inc();
      }
      /*MInst::RClosure(addr) => {
        // TODO
      }*/
      MInst::Thunk(addr) => {
        // TODO
        let close_env = self.ienv.clone();
        let thunk_v = MUnboxedValue::Thunk(MThunkRef{
          code: MClosureCode::Addr(addr),
          env:  close_env,
          ret:  Rc::new(RefCell::new(MThunkPayload::Empty)),
        });
        self.tmpstack.vals.push(thunk_v);
        self.pc.inc();
      }
      MInst::Update0 => {
        // TODO
        let ret_v = self.tmpstack.vals.pop().unwrap();
        let thunk_v = self.tmpstack.vals.pop().unwrap();
        match thunk_v {
          MUnboxedValue::Thunk(ref thunk) => {
            thunk.force_update(ret_v);
          }
          _ => panic!(),
        }
      }
      MInst::Eval0 => {
        let closurelike_v = self.tmpstack.vals.pop().unwrap();
        match closurelike_v {
          MUnboxedValue::Closure(ref closure) => {
            let addr = match closure.code {
              MClosureCode::Addr(ref addr) => addr.clone(),
              MClosureCode::OpDef(ref opdef) => unimplemented!(),
            };
            let (jmp_addr, close_env) = (addr, closure.env.clone());
            let ret_addr_v = MUnboxedValue::Addr(self.pc.next());
            let ret_env_v = MUnboxedValue::IndexEnv(self.ienv.clone());
            self.tmpstack.vals.push(ret_env_v);
            self.tmpstack.vals.push(ret_addr_v);
            self.ienv = close_env;
            self.pc = jmp_addr;
          }
          /*MUnboxedValue::RClosure(ref closure) => {
            // TODO
            unimplemented!();
          }*/
          MUnboxedValue::Thunk(ref thunk) => {
            match thunk.status() {
              MThunkStatus::Empty => {
                // TODO
                let addr = match thunk.code {
                  MClosureCode::Addr(ref addr) => addr.clone(),
                  MClosureCode::OpDef(ref opdef) => unimplemented!(),
                };
                let (jmp_addr, close_env) = (addr, thunk.env.clone());
                thunk.force_blackhole();
                let ret_addr_v = MUnboxedValue::Addr(self.pc.next());
                let ret_env_v = MUnboxedValue::IndexEnv(self.ienv.clone());
                self.tmpstack.vals.push(ret_env_v);
                self.tmpstack.vals.push(ret_addr_v);
                self.ienv = close_env;
                self.pc = jmp_addr;
              }
              MThunkStatus::BlackHole => {
                panic!();
              }
              MThunkStatus::Unbox => {
                // TODO
                self.pc.inc();
              }
            }
          }
          _ => panic!(),
        }
      }
      MInst::Apply0 => {
        let closure_v = self.tmpstack.vals.pop().unwrap();
        let (jmp_addr, close_env) = match closure_v {
          MUnboxedValue::Closure(ref closure) => {
            let addr = match closure.code {
              MClosureCode::Addr(ref addr) => addr.clone(),
              MClosureCode::OpDef(ref opdef) => unimplemented!(),
            };
            (addr, closure.env.clone())
          }
          _ => panic!(),
        };
        let ret_addr_v = MUnboxedValue::Addr(self.pc.next());
        let ret_env_v = MUnboxedValue::IndexEnv(self.ienv.clone());
        self.tmpstack.vals.push(ret_env_v);
        self.tmpstack.vals.push(ret_addr_v);
        self.ienv = close_env;
        self.pc = jmp_addr;
      }
      MInst::Apply1 => {
        let arg1_v = self.tmpstack.vals.pop().unwrap();
        let closure_v = self.tmpstack.vals.pop().unwrap();
        let (jmp_addr, close_env) = match closure_v {
          MUnboxedValue::Closure(ref closure) => {
            let addr = match closure.code {
              MClosureCode::Addr(ref addr) => addr.clone(),
              MClosureCode::OpDef(ref opdef) => unimplemented!(),
            };
            (addr, closure.env.clone())
          }
          _ => panic!(),
        };
        let ret_addr_v = MUnboxedValue::Addr(self.pc.next());
        let ret_env_v = MUnboxedValue::IndexEnv(self.ienv.clone());
        self.tmpstack.vals.push(ret_env_v);
        self.tmpstack.vals.push(ret_addr_v);
        self.ienv = close_env;
        self.ienv.vals.push(arg1_v.into_boxed());
        self.pc = jmp_addr;
      }
      MInst::Apply2 => {
        // TODO
        let arg2_v = self.tmpstack.vals.pop().unwrap();
        let arg1_v = self.tmpstack.vals.pop().unwrap();
        let closure_v = self.tmpstack.vals.pop().unwrap();
      }
      MInst::ApplyBuiltin(opdef) => {
        let (op_arity, op_addr) = self._builtin_opdef_info(opdef);
        for _ in 0 .. op_arity {
          let arg_v = self.tmpstack.vals.pop().unwrap();
          self.ienv.vals.push(arg_v.into_boxed());
        }
        let ret_addr_v = MUnboxedValue::Addr(self.pc.next());
        self.tmpstack.vals.push(ret_addr_v);
        self.pc = op_addr;
      }
      MInst::Return => {
        let retval_v = self.tmpstack.vals.pop().unwrap();
        let ret_addr_v = self.tmpstack.vals.pop().unwrap();
        let ret_env_v = self.tmpstack.vals.pop().unwrap();
        self.ienv = match ret_env_v {
          MUnboxedValue::IndexEnv(env) => env,
          _ => panic!(),
        };
        self.pc = match ret_addr_v {
          MUnboxedValue::Addr(addr) => addr,
          _ => panic!(),
        };
      }
      MInst::Breakpt => {
        flags.breakpt = true;
        self.pc.inc();
      }
      MInst::Halt => {
        self.done = true;
      }
      _ => unimplemented!(),
    }
    flags.done = self.done;
    flags
  }

  pub fn run(&mut self) {
    loop {
      match self.program.insts[self.pc.pos].clone() {
        MInst::Get(id) => {
          match self.register.clone() {
            MValue::Env(env) => {
              self.register = env.id_to_val.get(&id).unwrap().clone();
              self.pc.inc();
            }
            _ => panic!(),
          }
        }
        MInst::Put(id) => {
          // TODO
          match self.register {
            MValue::Env(ref mut env) => {
              let topidx = self.stack.vals.len() - 1;
              let val = self.stack.vals[topidx].clone();
              env.id_to_val.insert(id, val);
              self.pc.inc();
            }
            _ => panic!(),
          }
        }
        MInst::Push => {
          self.stack.vals.push(self.register.clone());
          self.pc.inc();
        }
        MInst::Swap => {
          let topidx = self.stack.vals.len() - 1;
          let val = self.stack.vals[topidx].clone();
          self.stack.vals[topidx] = self.register.clone();
          self.register = val;
          self.pc.inc();
        }
        MInst::Quote(rawdata) => {
          self.register = MValue::Data(MData{inner: rawdata});
          self.pc.inc();
        }
        MInst::CloseOp(opdef) => {
          // TODO
          let env = match self.register {
            MValue::Env(ref env) => env.clone(),
            MValue::Data(ref data) => panic!("FATAL: closeop: expected env, got data: {:?}", data.inner),
            MValue::Thunk(_) => panic!("FATAL: closeop: expected env, got thunk"),
            _ => panic!(),
          };
          let thunk = MThunk{
            closure:    MClosure{
              env,
              ienv: MIndexEnv::default(),
              code: MClosureCode::OpDef(opdef),
            },
            retval:     None,
          };
          self.register = MValue::Thunk(thunk);
          self.pc.inc();
        }
        MInst::Eval => {
          match self.register.clone() {
            MValue::Thunk(thunk) => {
              if thunk.retval.is_none() {
                let retval = match thunk.closure.code.clone() {
                  MClosureCode::Addr(_) => unimplemented!(),
                  MClosureCode::OpDef(opdef) => {
                    match opdef {
                      MOpDef::Add => {
                        let topidx = self.stack.vals.len() - 1;
                        let lhs = self.stack.vals[topidx - 1].data().inner;
                        let rhs = self.stack.vals[topidx].data().inner;
                        let result = lhs + rhs;
                        MValue::Data(MData{inner: result})
                      }
                      MOpDef::Mul => {
                        let topidx = self.stack.vals.len() - 1;
                        let lhs = self.stack.vals[topidx - 1].data().inner;
                        let rhs = self.stack.vals[topidx].data().inner;
                        let result = lhs * rhs;
                        MValue::Data(MData{inner: result})
                      }
                      MOpDef::Div => {
                        let topidx = self.stack.vals.len() - 1;
                        let lhs = self.stack.vals[topidx - 1].data().inner;
                        let rhs = self.stack.vals[topidx].data().inner;
                        let result = lhs / rhs;
                        MValue::Data(MData{inner: result})
                      }
                    }
                  }
                };
                self.register = MValue::Thunk(MThunk{
                  closure:  thunk.closure,
                  retval:   Some(Rc::new(retval)),
                });
              }
              self.pc.inc();
            }
            _ => panic!(),
          }
        }
        MInst::Breakpt => {
          self.pc.inc();
          return;
        }
        _ => unimplemented!(),
      }
    }
  }
}
