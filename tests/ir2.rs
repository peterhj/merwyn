extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine, MValUnpack};

#[test]
fn test_ir2_example_0() {
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let y = x2; y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  builder._print(module.tree);
}

#[test]
fn test_ir2_example_1() {
  let lexer = HLexer::new(r"let f = \x, k -> match k with | 0 => x | _ => x; let x = 1.0; let k = 5; f[x, k]");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  builder._print(module.tree);
}

#[test]
fn test_ir2_let_pat() {
  let lexer = HLexer::new(r"let (x, y) = (1f, 2f) in x + y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("DEBUG: htree: {:?}", htree);
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
fn test_ir2_quote() {
  let lexer = HLexer::new(r"'x");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::default();
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  //builder._print(module.tree);
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r = val.as_quote();
  println!("DEBUG: result: {:?}", r);
}
