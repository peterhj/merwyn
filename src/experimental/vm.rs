use std::collections::{HashMap};
use std::rc::{Rc};

#[derive(Clone, Default)]
pub struct MStack {
  pub vals: Vec<MValue>,
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
pub enum MValue {
  Data(MData),
  Thunk(MThunk),
  Env(MEnv),
  Index(usize),
  Closure(MClosure),
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
  pub vals: Vec<MValue>,
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
  Fetch(usize),
  Bind,
  Unbind,
  Quote(f32),
  Close(MProgramAddr),
  CloseOp(MOpDef),
  //EvalThunk(usize),
  //RetcThunk,
  //UpdateThunk,
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
  pub env:      MIndexEnv,
  pub stack:    MStack,
  pub program:  MProgram,
  pub pc:       MProgramAddr,
  pub done:     bool,
}

impl Machine {
  pub fn new() -> Machine {
    Machine{
      register: MValue::Env(MEnv::default()),
      env:      MIndexEnv::default(),
      stack:    MStack::default(),
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
      MInst::Fetch(idx) => {
        let envlen = self.env.vals.len();
        let val = self.env.vals[envlen - idx].clone();
        self.stack.vals.push(val);
        self.pc.inc();
      }
      MInst::Bind => {
        let val = self.stack.vals.pop().unwrap();
        self.env.vals.push(val);
        self.pc.inc();
      }
      MInst::Unbind => {
        let _val = self.env.vals.pop().unwrap();
        self.pc.inc();
      }
      MInst::Quote(rawdata) => {
        // TODO
      }
      MInst::Close(addr) => {
        let close_env = self.env.clone();
        let closure_v = MValue::Closure(MClosure{
          code: MClosureCode::Addr(addr),
          env:  MEnv::default(),
          ienv: close_env,
        });
        self.stack.vals.push(closure_v);
        self.pc.inc();
      }
      /*MInst::EvalThunk(idx) => {
        // TODO
        self.stack.vals.push(MValue::Index(idx));
      }*/
      MInst::Apply0 => {
        let closure_v = self.stack.vals.pop().unwrap();
        let (jmp_addr, close_env) = match closure_v {
          MValue::Closure(ref closure) => {
            let addr = match closure.code {
              MClosureCode::Addr(ref addr) => addr.clone(),
              MClosureCode::OpDef(ref opdef) => unimplemented!(),
            };
            (addr, closure.ienv.clone())
          }
          _ => panic!(),
        };
        let ret_addr_v = MValue::CodeAddr(self.pc.next());
        let ret_env_v = MValue::IndexEnv(self.env.clone());
        self.stack.vals.push(ret_env_v);
        self.stack.vals.push(ret_addr_v);
        self.env = close_env;
        self.pc = jmp_addr;
      }
      MInst::Apply1 => {
        let arg1_v = self.stack.vals.pop().unwrap();
        let closure_v = self.stack.vals.pop().unwrap();
        let (jmp_addr, close_env) = match closure_v {
          MValue::Closure(ref closure) => {
            let addr = match closure.code {
              MClosureCode::Addr(ref addr) => addr.clone(),
              MClosureCode::OpDef(ref opdef) => unimplemented!(),
            };
            (addr, closure.ienv.clone())
          }
          _ => panic!(),
        };
        let ret_addr_v = MValue::CodeAddr(self.pc.next());
        let ret_env_v = MValue::IndexEnv(self.env.clone());
        self.stack.vals.push(ret_env_v);
        self.stack.vals.push(ret_addr_v);
        self.env = close_env;
        self.env.vals.push(arg1_v);
        self.pc = jmp_addr;
      }
      MInst::Apply2 => {
        // TODO
        let arg2_v = self.stack.vals.pop().unwrap();
        let arg1_v = self.stack.vals.pop().unwrap();
        let closure_v = self.stack.vals.pop().unwrap();
      }
      MInst::ApplyBuiltin(opdef) => {
        let (op_arity, op_addr) = self._builtin_opdef_info(opdef);
        let mut arg_vs = Vec::with_capacity(op_arity);
        for _ in 0 .. op_arity {
          arg_vs.push(self.stack.vals.pop().unwrap());
        }
        let ret_addr_v = MValue::CodeAddr(self.pc.next());
        self.stack.vals.push(ret_addr_v);
        for _ in 0 .. op_arity {
          self.env.vals.push(arg_vs.pop().unwrap());
        }
        self.pc = op_addr;
      }
      MInst::Return => {
        let retval_v = self.stack.vals.pop().unwrap();
        let ret_addr_v = self.stack.vals.pop().unwrap();
        let ret_env_v = self.stack.vals.pop().unwrap();
        self.env = match ret_env_v {
          MValue::IndexEnv(env) => env,
          _ => panic!(),
        };
        self.pc = match ret_addr_v {
          MValue::CodeAddr(addr) => addr,
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
