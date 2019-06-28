extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine};

#[test]
fn test_ty2_example_0() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let y = f[x1]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = builder.compile(htree, LCtxRef::default());
  //println!("DEBUG: ltree: {:?}", ltree.root);
  //println!("DEBUG: ltree pretty printed:");
  //builder.pretty_print(ltree.clone());
  //let mut ty_inf = SimpleTyInferenceMachine::default();
  //ty_inf.gen(ltree.root.clone());
  //let ty_res = ty_inf.solve(&mut builder);
  //println!("DEBUG: ltree type inference result: {:?}", ty_res);
  //ty_inf._debug_dump();
  //assert!(ty_res.is_ok());
}

#[test]
fn test_ty2_example_1() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let df = d[f]; let dy = df[x1]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = builder.compile(htree, LCtxRef::default());
}

#[test]
fn test_ty2_example_2_fails() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = builder.compile(htree, LCtxRef::default());
}
