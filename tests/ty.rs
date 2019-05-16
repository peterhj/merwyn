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
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
fn test_ty_2() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 1; let y = 2; let z = x; {x, y, z}");
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
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
fn test_ty_monomorphic_id() {
  println!();
  //let lexer = HLexer::new("let id = \\t. t; let x = 1; let y = 3.14; let z = id[x]; let z' = id[y]; z'");
  let lexer = HLexer::new("let id = \\t. t; let x = 1; let y = 3.14; let z = id[x]; z");
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
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
#[should_panic]
fn test_ty_monomorphic_id_fails() {
  println!();
  let lexer = HLexer::new("let id = \\t. t; let x = 1; let y = 3.14; let z = id[x]; let z' = id[y]; z'");
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
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
fn test_ty_adj_1() {
  println!();
  //let lexer = HLexer::new("let x = 3.14; let y = let w = x in w; let z = adj y; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. 3.14; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. t; let y' = y[x]; let z = adj y'; z");
  let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let y' = y[x]; let z = adj y'; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  //let ltree = builder.lower_with_stdlib(htree);
  let ltree = ltree.with_env_info();
  let ltree = ltree.with_free_env_info();
  //println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: adj-expanded ltree: {:?}", ltree.root);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let mut ty_inf = SimpleTyInferenceMachine::default();
  ty_inf.gen(ltree.root.clone());
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
fn test_ty_adj_2() {
  println!();
  //let lexer = HLexer::new("let x = 3.14; let y = let w = x in w; let z = adj y; z");
  //let lexer = HLexer::new("let x = 3.14; let y = x; let dy = (adj y)[1.0]; dy.x");
  let lexer = HLexer::new("let x = 3.14; let y = x; let z = y; let dz = (adj z)[1.0]; {dz.x, dz.y}");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. 3.14; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. t; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let y' = y[x]; let z = adj y'; let dy = z[1.0]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  //let ltree = builder.lower_with_stdlib(htree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: adj-expanded ltree: {:?}", ltree.root);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let mut ty_inf = SimpleTyInferenceMachine::default();
  ty_inf.gen(ltree.root.clone());
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());
}

#[test]
fn test_ty_adj_3() {
  println!();
  //let lexer = HLexer::new("let x = 3.14; let y = let w = x in w; let z = adj y; z");
  //let lexer = HLexer::new("let x = 3.14; let y = x; let dy = (adj y)[1.0]; dy.x");
  let lexer = HLexer::new("let x = 3.14; let y = x; let z = y; let dz = (adj z)[1.0]; {dz.x, dz.y}");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. 3.14; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. t; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let y' = y[x]; let z = adj y'; let dy = z[1.0]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  //let ltree = builder.lower_with_stdlib(htree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: adj-expanded ltree: {:?}", ltree.root);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  /*let mut ty_inf = SimpleTyInferenceMachine::default();
  ty_inf.gen(ltree.root.clone());
  let ty_res = ty_inf.solve(&mut builder);
  println!("DEBUG: ltree type inference result: {:?}", ty_res);
  ty_inf._debug_dump();
  assert!(ty_res.is_ok());*/
  let ltree = builder.resolve_env_select(ltree);
  println!("DEBUG: env-select-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
}
