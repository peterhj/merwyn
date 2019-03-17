// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::num_util::*;
use crate::vm::{VMBoxCode, VMLam, VMLamCode, VMVal, VMValRef};

use std::rc::{Rc};

pub fn make_bc_pi100() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(0, args.len());
      let mval = VMValRef::new(VMVal::Int(Checked(314)));
      mval
    }),
    ladj: None,
  };
  bc
}

pub fn make_bc_neg() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
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
    ladj: None,
  };
  bc
}

pub fn make_bc_eq() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      // TODO
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 == x1;
          let mval = VMValRef::new(VMVal::Bit(r));
          mval
        }
        _ => panic!("eq: unsupported operand types"),
      }
    }),
    ladj: None,
  };
  bc
}

pub fn make_bc_add() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
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
    ladj: None,
  };
  bc
}

pub fn make_bc_mul() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
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
    ladj: None,
  };
  bc
}
