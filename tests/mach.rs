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
