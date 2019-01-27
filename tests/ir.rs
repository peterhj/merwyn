extern crate hebb;

use hebb::ir::{LBuilder};
use hebb::lang::{HLexer, HParser};

#[test]
fn test_ir_1() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 1; let y = 2; let z = x; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  let ltree = builder.lower(htree);
  builder._debug_dump_vars();
  println!("DEBUG: ltree: {:?}", ltree);
  let ltree = builder._ltree_env_info_pass(ltree);
  println!("DEBUG: ltree + env info: {:?}", ltree);
  let ltree = builder._ltree_freeuse_info_pass(ltree);
  println!("DEBUG: ltree + env + freeuse info: {:?}", ltree);
}
