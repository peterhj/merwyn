extern crate merwyn;

use merwyn::ir::{LBuilder, SimpleTyInferenceMachine};
use merwyn::lang::{HLexer, HParser};

#[test]
fn test_ty_1() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 1; let y = 2; let z = x; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree pretty printed:");
  builder.pretty_print(ltree.clone());
  let mut ty_inf = SimpleTyInferenceMachine::default();
  ty_inf.gen(ltree.root.clone());
  let ty_res = ty_inf.solve();
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
}
