extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine};

#[test]
fn test_ty2_example_0() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let y = f[x1]; let dy = d[y]; dy");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_1() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let df = d[f]; let dy = df[x1]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = x1; let x3 = 3.0; let f = \\t. x2; let y = f[x1]; let dy = d[y]; dy");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_2() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let df = d[f]; let dy = df[x1]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = x1; let x3 = 3.0; let f = \\t. t; let y = f[x2]; let dy = d[y]; dy");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_3() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let y = f[x1]; let dy = d[y]; dy.x2");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[should_panic]
#[test]
fn test_ty2_example_3_fails() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. x2; let y = f[x1]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_4() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t, k. t; let y = f[x1, 5]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_5() {
  println!();
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = (adj y)[1.0]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. t + x2; let y = x1 + f[x1]; let dy = d[y]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let df = d[f]; let dy = df[x1]; dy.x1");
  //let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \\t. bot; let y = f[x1]; let dy = d[y]; dy.x1");
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let x3 = 5; let f = \\t, k. t; let y = f[x1, x3]; let dy = d[y]; dy.x1");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

#[test]
fn test_ty2_example_6() {
  println!();
  let lexer = HLexer::new("let x = 1.0; let n = 5; let f = \\t, k. match k | 0 => t | _ => t; let y = f[x, n]; let dy = d[y]; dy.x");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}

/*// TODO
#[test]
fn test_ty2_example_7() {
  println!();
  let lexer = HLexer::new("let x1 = 1.0; let x2 = 2.0; let n = 5; let f = \\t, k. match k | 0 => t | _ => x2; let y = f[x1, n]; let dy = d[y]; dy.x2");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
}*/
