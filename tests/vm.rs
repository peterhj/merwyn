extern crate hebb;

use hebb::ir::{LBuilder, LVar};
use hebb::lang::{HLexer, HParser};
use hebb::vm::{VMachine};

#[test]
fn test_vm_1() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; y");
  let lexer = HLexer::new("let x = 1; let y = 2; let x = bot; let t = tee; x");
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  let ltree = builder.lower(htree);
  let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let letree = builder._ltree_env_pass(ltree);
  //println!("DEBUG: letree: {:?}", letree);
  let mut vm = VMachine::new();
  //vm.eval(ltree);
  vm._debug_eval(Some(ltree), 9);
  let (_, mthk) = vm._lookup_thunk(LVar(3));
  mthk._kill();
  vm._debug_eval(None, 100);
  vm._debug_dump_ctrl();
}

#[test]
fn test_vm_2() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; y");
  let lexer = HLexer::new("let x = 1; let y = 2; let x = \\. 3; let t = tee; x[]");
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  let ltree = builder.lower(htree);
  //let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let letree = builder._ltree_env_pass(ltree);
  //println!("DEBUG: letree: {:?}", letree);
  let mut vm = VMachine::new();
  vm.eval(ltree);
  /*vm._debug_eval(Some(ltree), 9);
  let (_, mthk) = vm._lookup_thunk(LVar(3));
  mthk._kill();
  vm._debug_eval(None, 100);*/
  vm._debug_dump_ctrl();
}

#[test]
fn test_vm_3() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let x = \\. pi100[]; let t = tee; x[]");
  //let lexer = HLexer::new("let x = 1; let y = 2; let t = tee; pi100[]");
  let lexer = HLexer::new("let f = pi100; f[]");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  //let ltree = builder.lower(htree);
  let ltree = builder.lower_with_stdlib(htree);
  //let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let letree = builder._ltree_env_pass(ltree);
  //println!("DEBUG: letree: {:?}", letree);
  let mut vm = VMachine::new();
  vm._reset(ltree);
  vm._eval();
  /*vm._debug_eval(Some(ltree), 9);
  let (_, mthk) = vm._lookup_thunk(LVar(3));
  mthk._kill();
  vm._debug_eval(None, 100);*/
  vm._debug_dump_ctrl();
}

#[test]
fn test_vm_4() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let x = \\. pi100[]; let t = tee; x[]");
  //let lexer = HLexer::new("let x = 1; let y = 2; let t = tee; pi100[]");
  let lexer = HLexer::new("let x = 1; -x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  //let ltree = builder.lower(htree);
  let ltree = builder.lower_with_stdlib(htree);
  let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let letree = builder._ltree_env_pass(ltree);
  //println!("DEBUG: letree: {:?}", letree);
  let mut vm = VMachine::new();
  vm._reset(ltree);
  vm._eval();
  /*vm._debug_eval(Some(ltree), 9);
  let (_, mthk) = vm._lookup_thunk(LVar(3));
  mthk._kill();
  vm._debug_eval(None, 100);*/
  vm._debug_dump_ctrl();
}

#[test]
fn test_vm_5() {
  println!();
  let lexer = HLexer::new("let x = switch bot -: 1 | -2; -x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  //let ltree = builder.lower(htree);
  let ltree = builder.lower_with_stdlib(htree);
  let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let letree = builder._ltree_env_pass(ltree);
  //println!("DEBUG: letree: {:?}", letree);
  let mut vm = VMachine::new();
  vm._reset(ltree);
  vm._eval();
  vm._debug_dump_ctrl();
}

#[test]
fn test_vm_6() {
  println!();
  let lexer = HLexer::new("let x = switch bot -: 1 | -2; (0, x, -x)");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_stdlib(htree);
  let ltree = builder.normalize(ltree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  let mut vm = VMachine::new();
  vm._reset(ltree);
  vm._eval();
  vm._debug_dump_ctrl();
}
