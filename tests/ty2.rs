extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine, MValUnpack};

#[test]
fn test_ty2_anno_0() {
  println!();
  let lexer = HLexer::new(r"let x: Flp = 1.0; x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some(1.0));
}

#[should_panic]
#[test]
fn test_ty2_anno_0_fails() {
  println!();
  let lexer = HLexer::new(r"let x: Int = 1.0; x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let _module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
}

#[test]
fn test_ty2_anno_1() {
  println!();
  let lexer = HLexer::new(r"alt x; let alt x: Int = 3; let alt x: Flp = 3.14; 42");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<i64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some(42));
}

#[test]
fn test_ty2_anno_2_a() {
  println!();
  let lexer = HLexer::new(r"alt x; let alt x: Int = 3; let alt x: Flp = 3.14; let f_mono: [Int] -> Int = \z -> z in f_mono[x]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<i64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some(3));
}

#[test]
fn test_ty2_anno_2_b() {
  println!();
  let lexer = HLexer::new(r"alt x; let alt x: Int = 3; let alt x: Flp = 3.14; let f_mono: [Flp] -> Flp = \z -> z in f_mono[x]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some(3.14));
}

#[test]
fn test_ty2_deriv_0() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \t -> x2; let y = f[x1]; let dy = d[y]; dy");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_deriv_1() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let df = d[f]; let dy = df[x1]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = x1; let x3 = 3.0; let f = \t -> x2; let y = f[x1]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[test]
fn test_ty2_deriv_2() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let df = d[f]; let dy = df[x1]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = x1; let x3 = 3.0; let f = \t -> t; let y = f[x2]; let dy = d[y]; dy.x2");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[test]
fn test_ty2_deriv_3() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \t -> x2; let y = f[x1]; let dy = d[y]; dy.x2");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[should_panic]
#[test]
fn test_ty2_deriv_3_fails() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \t -> x2; let y = f[x1]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[test]
fn test_ty2_deriv_4() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \t, k -> t; let y = f[x1, 5]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[test]
fn test_ty2_deriv_5() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 5; let f = \t, k -> t; let y = f[x1, x3]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

#[test]
fn test_ty2_deriv_6() {
  println!();
  let lexer = HLexer::new(r"let x = 3.0; let n = 5; let f = \t, k -> match k with | 0 => t | _ => t; let y = f[x, n]; let dy = d[y]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}

/*// TODO
#[test]
fn test_ty2_deriv_7() {
  println!();
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let n = 5; let f = \t, k -> match k with | 0 => t | _ => x2; let y = f[x1, n]; let dy = d[y]; dy.x2");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
}*/
