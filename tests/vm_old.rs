extern crate hebb;

use hebb::vm::*;

#[test]
fn test_hello() {
  let mut vm = VM::new();
  vm.reset();
  vm.set_env(MIdent{uniq: 1}, MValue::Data(MData{inner: 1.0}));
  vm.set_env(MIdent{uniq: 2}, MValue::Data(MData{inner: 2.0}));
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Get(MIdent{uniq: 1}));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Get(MIdent{uniq: 2}));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::CloseOp(MOpDef::Add));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Eval);
  vm.push_inst(MInst::Breakpt);
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  panic!();
}

#[test]
fn test_hello2() {
  let mut vm = VM::new();
  vm.reset();
  //vm.set_env(MIdent{uniq: 1}, MValue::Data(MData{inner: 1.0}));
  //vm.set_env(MIdent{uniq: 2}, MValue::Data(MData{inner: 2.0}));
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Quote(1.0));
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::Put(MIdent{uniq: 1}));
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Quote(2.0));
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::Put(MIdent{uniq: 2}));
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Get(MIdent{uniq: 1}));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::Push);
  vm.push_inst(MInst::Get(MIdent{uniq: 2}));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Swap);
  vm.push_inst(MInst::CloseOp(MOpDef::Div));
  vm.push_inst(MInst::Breakpt);
  vm.push_inst(MInst::Eval);
  vm.push_inst(MInst::Breakpt);
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  vm.run();
  vm.inspect_reg();
  panic!();
}
