// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

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
fn test_mach_stage_2_1() {
  println!();
  let lexer = HLexer::new(r"let x = ?x; let y = ?y; x + y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  builder._stage_val("x", (1.0, 3.14));
  builder._stage_val("y", (2.0, 42.0));
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<(f64, f64)> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some((3.0, 45.14)));
  let r2: Option<[f64; 2]> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r2);
  assert_eq!(r2, Some([3.0, 45.14]));
}

#[test]
fn test_mach_stage_2_2() {
  println!();
  let lexer = HLexer::new(r"let x: V2Flp = ?x; let y: V2Flp = ?y; x + y");
  let parser = HParser::new(lexer);
  let htree = parser.parse().unwrap();
  let mut builder = LBuilder::default();
  builder._stage_val("x", (1.0, 3.14));
  builder._stage_val("y", (2.0, 42.0));
  let module = match builder._compile(htree, LCtxRef::default(), LTyctxRef::default()) {
    Err(_) => panic!(),
    Ok(module) => module,
  };
  // TODO
  let mut machine = Machine::default();
  let val = machine.reset_eval(module.tree.root());
  let r: Option<(f64, f64)> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  assert_eq!(r, Some((3.0, 45.14)));
  let r2: Option<[f64; 2]> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r2);
  assert_eq!(r2, Some([3.0, 45.14]));
}

#[test]
fn test_mach_undef_1() {
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

#[test]
fn test_mach_undef_2() {
  println!();
  let lexer = HLexer::new(r"let x = 1.0 / 0.0; (x, x!)");
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
  let r: Option<(Option<f64>, Option<bool>)> = val.clone().try_unpack();
  println!("DEBUG: result: {:?}", r);
  match r {
    None => panic!(),
    Some((x, d)) => {
      assert_eq!(x, None);
      assert_eq!(d, Some(false));
    }
  }
}
