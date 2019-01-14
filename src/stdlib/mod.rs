use crate::vm::{VMBoxCode, VMLam, VMLamCode, VMVal, VMValRef};

use std::rc::{Rc};

pub fn make_bc_pi100() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args, _env| {
      assert_eq!(0, args.len());
      let mval = VMValRef::new(VMVal::Int(314));
      mval
    }),
  };
  bc
}

pub fn make_bc_neg() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args, _env| {
      // TODO
      assert_eq!(1, args.len());
      match &*args[0] {
        &VMVal::Int(x) => {
          let r = -x;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        _ => panic!("neg: unsupported operand type"),
      }
    }),
  };
  bc
}

pub fn make_bc_add() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args, _env| {
      // TODO
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 + x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        _ => panic!("add: unsupported operand types"),
      }
    }),
  };
  bc
}

pub fn make_bc_mul() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args, _env| {
      // TODO
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 * x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        _ => panic!("mul: unsupported operand types"),
      }
    }),
  };
  bc
}
