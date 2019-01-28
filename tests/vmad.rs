extern crate hebb;

use hebb::ir::{LBuilder};
use hebb::lang::{HLexer, HParser};
use hebb::vm::{VMachine};

#[test]
fn test_vmad_1() {
  // TODO
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 2; let y = x; let adj_y = adj dyn y; adj_y.x");
  //let lexer = HLexer::new("let x = 2; let y = x; let adj_y = adj dyn y; adj_y.y");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  let ltree = builder._ltree_env_info_pass(ltree);
  builder._debug_dump_vars();
  //println!("DEBUG: ltree + env info: {:?}", ltree);
  let ltree = builder._ltree_dyn_adjoint_pass(ltree);
  builder._debug_dump_vars();
  //println!("DEBUG: ltree + adjoint: {:?}", ltree);
  let mut vm = VMachine::new();
  vm.eval(ltree);
  vm._debug_dump_ctrl();
}
