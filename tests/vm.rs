extern crate hebb;

use hebb::experimental::vm::*;

#[test]
fn test_hello() {
  let mut mach = Machine::new();
  mach.reset();
  mach.set_env(MIdent{uniq: 1}, MValue::Data(MData{inner: 1.0}));
  mach.set_env(MIdent{uniq: 2}, MValue::Data(MData{inner: 2.0}));
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Get(MIdent{uniq: 1}));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Get(MIdent{uniq: 2}));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::CloseOp(MOpDef::Add));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Eval);
  mach.push_inst(MInst::Breakpt);
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  panic!();
}

#[test]
fn test_hello2() {
  let mut mach = Machine::new();
  mach.reset();
  //mach.set_env(MIdent{uniq: 1}, MValue::Data(MData{inner: 1.0}));
  //mach.set_env(MIdent{uniq: 2}, MValue::Data(MData{inner: 2.0}));
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Quote(1.0));
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::Put(MIdent{uniq: 1}));
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Quote(2.0));
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::Put(MIdent{uniq: 2}));
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Get(MIdent{uniq: 1}));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::Push);
  mach.push_inst(MInst::Get(MIdent{uniq: 2}));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Swap);
  mach.push_inst(MInst::CloseOp(MOpDef::Div));
  mach.push_inst(MInst::Breakpt);
  mach.push_inst(MInst::Eval);
  mach.push_inst(MInst::Breakpt);
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  mach.run();
  mach.inspect_reg();
  panic!();
}
