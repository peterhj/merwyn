extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine, MValUnpack};

#[test]
fn test_mach_example_0() {
  println!();
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let x3 = 3.0; let f = \t -> x2; let y = f[x1]; y");
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
  assert_eq!(r, Some(2.0));
}

#[test]
fn test_mach_example_1() {
  println!();
  let lexer = HLexer::new(r"let x1 = 1.0; let x2 = 2.0; let y = x1 + x2; y");
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
  assert_eq!(r, Some(3.0));
}

#[test]
fn test_mach_stage_1() {
  println!();
  let lexer = HLexer::new(r"let x = ?x; let y = 1.0; x + y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  builder._stage_val("x", 2.0);
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<f64> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some(3.0));
}

#[test]
fn test_mach_undef() {
  println!();
  let lexer = HLexer::new(r"1.0 / 0.0");
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
  assert_eq!(r, None);
}
