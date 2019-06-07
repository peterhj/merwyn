// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ir::{LBuilder, LEnvKey, LExpr, LTerm, LTermRef, LVar};
use crate::num_util::{checked};
use crate::vm::{VMBoxCode, VMLam, VMLamCode, VMVal, VMValRef};

use std::rc::{Rc};

pub fn make_bc_pi100() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(0, args.len());
      let mval = VMValRef::new(VMVal::Int(checked(314)));
      mval
    }),
    //ladj: None,
  };
  bc
}

pub fn make_bc_neg() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(1, args.len());
      match &*args[0] {
        &VMVal::Int(x) => {
          let r = -x;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        &VMVal::Flo(x) => {
          let r = -x;
          let mval = VMValRef::new(VMVal::Flo(r));
          mval
        }
        _ => panic!("neg: unsupported operand type"),
      }
    }),
    //ladj: None,
  };
  bc
}

pub fn make_bc_eq() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
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
    //ladj: None,
  };
  bc
}

pub fn make_bc_add() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 + x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        (&VMVal::Flo(x0), &VMVal::Flo(x1)) => {
          let r = x0 + x1;
          let mval = VMValRef::new(VMVal::Flo(r));
          mval
        }
        _ => panic!("add: unsupported operand types"),
      }
    }),
    //ladj: None,
  };
  bc
}

pub fn make_adj_add(builder: &mut LBuilder, params: Vec<LVar>, adj_sink: LVar) -> LExpr {
  /*let adj0 = {
    /*let v = builder.vars.fresh();
    builder.lambda_term(
        vec![v.clone()],
        &mut |builder| builder.lookup_term(v.clone()),
    )*/
    builder.lookup_term(adj_sink.clone())
  };
  let adj1 = {
    /*let v = builder.vars.fresh();
    builder.lambda_term(
        vec![v.clone()],
        &mut |builder| builder.lookup_term(v.clone()),
    )*/
    builder.lookup_term(adj_sink.clone())
  };
  vec![adj0, adj1]*/
  LExpr{
    label:  builder.labels.fresh(),
    term:   LTermRef::new(LTerm::AConcat(
        LExpr{
          label:  builder.labels.fresh(),
          term:   LTermRef::new(LTerm::AEnv(
              vec![(
                LEnvKey::Var(params[0].clone()),
                LExpr{
                  label:  builder.labels.fresh(),
                  term:   LTermRef::new(LTerm::Lookup(adj_sink.clone()))
                }
              )],
          ))
        },
        LExpr{
          label:  builder.labels.fresh(),
          term:   LTermRef::new(LTerm::AConcat(
              LExpr{
                label:  builder.labels.fresh(),
                term:   LTermRef::new(LTerm::AEnv(
                    vec![(
                      LEnvKey::Var(params[1].clone()),
                      LExpr{
                        label:  builder.labels.fresh(),
                        term:   LTermRef::new(LTerm::Lookup(adj_sink.clone()))
                      }
                    )],
                ))
              },
              LExpr{
                label:  builder.labels.fresh(),
                term:   LTermRef::new(LTerm::AEnv(vec![]))
              },
          ))
        },
    ))
  }
}

pub fn make_bc_sub() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 - x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        (&VMVal::Flo(x0), &VMVal::Flo(x1)) => {
          let r = x0 - x1;
          let mval = VMValRef::new(VMVal::Flo(r));
          mval
        }
        _ => panic!("sub: unsupported operand types"),
      }
    }),
    //ladj: None,
  };
  bc
}

pub fn make_bc_mul() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 * x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        (&VMVal::Flo(x0), &VMVal::Flo(x1)) => {
          let r = x0 * x1;
          let mval = VMValRef::new(VMVal::Flo(r));
          mval
        }
        _ => panic!("mul: unsupported operand types"),
      }
    }),
    //ladj: None,
  };
  bc
}

/*pub fn make_adj_mul(builder: &mut LBuilder, params: Vec<LVar>, adj_sink: LVar) -> Vec<LExpr> {
  let op_hash = builder.hashes.lookup("mul".to_owned());
  let op = builder.vars.lookup(op_hash);
  let adj0 = {
    builder.apply_term(
        &mut |builder| builder.lookup_term(op.clone()),
        vec![
          &mut |builder| builder.lookup_term(params[1].clone()),
          &mut |builder| builder.lookup_term(adj_sink.clone()),
        ]
    )
  };
  let adj1 = {
    builder.apply_term(
        &mut |builder| builder.lookup_term(op.clone()),
        vec![
          &mut |builder| builder.lookup_term(params[0].clone()),
          &mut |builder| builder.lookup_term(adj_sink.clone()),
        ]
    )
  };
  vec![adj0, adj1]
}*/

pub fn make_bc_div() -> VMBoxCode {
  let bc = VMBoxCode{
    ifun: Rc::new(|args| {
      assert_eq!(2, args.len());
      match (&*args[0], &*args[1]) {
        (&VMVal::Int(x0), &VMVal::Int(x1)) => {
          let r = x0 / x1;
          let mval = VMValRef::new(VMVal::Int(r));
          mval
        }
        (&VMVal::Flo(x0), &VMVal::Flo(x1)) => {
          let r = x0 / x1;
          let mval = VMValRef::new(VMVal::Flo(r));
          mval
        }
        _ => panic!("div: unsupported operand types"),
      }
    }),
    //ladj: None,
  };
  bc
}
