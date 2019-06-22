extern crate merwyn;

use merwyn::ir::{LBuilder, SimpleTyInferenceMachine};
use merwyn::lang::{HLexer, HParser};
use merwyn::vm::{VMachine, VMUnpack};

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
  //let ltree = builder.lower_with_toplevel(htree);
  let ltree = ltree.with_env_info();
  let ltree = ltree.with_free_env_info();
  //println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
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
  //let lexer = HLexer::new("let x = 3.14; let y = x; let z = y; let dz = D[z]; {dz.x, dz.y}");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. 3.14; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. t; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let y' = y[x]; let z = adj y'; let dy = z[1.0]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  //let ltree = builder.lower_with_toplevel(htree);
  //let ltree = ltree.with_env_info();
  //let ltree = ltree.with_free_env_info();
  //println!("DEBUG: ltree: {:?}", ltree.root);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
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
  //let ltree = builder.lower(htree);
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  let mut vm = VMachine::new();
  let halt_mval = vm.eval(ltree);
  let v: Option<(f64, f64)> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
}

#[test]
fn test_ty_adj_4() {
  println!();
  //let lexer = HLexer::new("let x = 3.14; let y = let w = x in w; let z = adj y; z");
  //let lexer = HLexer::new("let x = 3.14; let y = x; let dy = (adj y)[1.0]; dy.x");
  //let lexer = HLexer::new("let x = 3.14; let y = x; let z = y; let dz = (adj z)[1.0]; {dz.x, dz.y}");
  let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let z = y[x]; let dz = (adj z)[1.0]; dz.x");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. 3.14; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. t; let y' = y[x]; let z = adj y'; z");
  //let lexer = HLexer::new("let x = 3.14; let y = \\t. x; let y' = y[x]; let z = adj y'; let dy = z[1.0]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder.lower(htree);
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  let mut vm = VMachine::new();
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
}

#[test]
fn test_ty_adj_add_1() {
  println!();
  let lexer = HLexer::new("let x = 3.14; let y = x + x; (adj y)[1.0].x");
  //let lexer = HLexer::new("let x = 3.14; let y = x + x; D[y].x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
  println!("DEBUG: step count: {:?}", vm._step_count());
  assert_eq!(v, Some(2.0));
}

#[test]
fn test_ty_adj_add_2() {
  println!();
  let lexer = HLexer::new("let x = 3.14; let y = x + x; let z = x + y; let dz = (adj z)[1.0]; dz.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
  println!("DEBUG: step count: {:?}", vm._step_count());
  assert_eq!(v, Some(3.0));
}

#[test]
fn test_ty_adj_add_3() {
  println!();
  let lexer = HLexer::new("let x = 3.14; let y1 = x + x; let y2 = y1 + y1; let y3 = y2 + y2; let y4 = y3 + y3; let y5 = y4 + y4; let z = y5 + y3 + y1; let dz = (adj z)[1.0]; dz.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
  println!("DEBUG: step count: {:?}", vm._step_count());
  assert_eq!(v, Some(42.0));
}

#[test]
fn test_ty_adj_add_3_1() {
  println!();
  let lexer = HLexer::new("let x = 3.14; let y1 = x + x; let y2 = y1 + y1; let y3 = y2 + y2; let y4 = y3 + y3; let y5 = y4 + y4; let z = y5 + y3 + y1; let dz = adj z; dz");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  println!("DEBUG: step count: {:?}", vm._step_count());
}

#[test]
fn test_ty_adj_mul_1() {
  println!();
  let lexer = HLexer::new("let x = 3.14; let y = x * x; (adj y)[1.0].x");
  //let lexer = HLexer::new("let x = 3.14; let y = x * x; D[y].x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
  println!("DEBUG: step count: {:?}", vm._step_count());
  assert_eq!(v, Some(3.14 + 3.14));
}

#[test]
fn test_ty_example_1() {
  println!();
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; (adj y)[1.0].x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; D[y].x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; D[y].x2");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; D[y].x3");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  println!("DEBUG: ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.rewrite_differential(ltree);
  println!("DEBUG: D-rewritten ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.expand_adj(ltree);
  println!("DEBUG: adj-expanded ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.normalize(ltree);
  println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = builder.resolve_ty_inf(ltree);
  println!("DEBUG: ty-inf-resolved, pretty printed:");
  builder.pretty_print(ltree.clone());
  let ltree = ltree.root;
  //let mut vm = VMachine::new();
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  let v: Option<f64> = halt_mval.try_unpack();
  println!("DEBUG: halt value: {:?}", v);
  println!("DEBUG: step count: {:?}", vm._step_count());
  //assert_eq!(v, Some(3.14 + 3.14));
}
