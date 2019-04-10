extern crate hebb;

use hebb::ir::{LBuilder};
use hebb::lang::{HLexer, HParser};

#[test]
fn test_ir_1() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 1; let y = 2; let z = x; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  //let ltree = builder._htree_to_ltree_lower_pass(htree);
  let ltree = builder.lower(htree);
  //builder._debug_dump_vars();
  //println!("DEBUG: ltree: {:?}", ltree);
  //let ltree = builder._ltree_env_info_pass(ltree);
  //println!("DEBUG: ltree + env info: {:?}", ltree);
  let ltree = ltree.with_env_info();
  //let ltree = builder._ltree_freeuse_info_pass(ltree);
  //println!("DEBUG: ltree + env + freeuse info: {:?}", ltree);
  let ltree = ltree.with_freeuses_info();
  println!("DEBUG: ltree pretty printed:");
  ltree._pretty_print();
}

#[test]
fn test_ir_2() {
  println!();
  //let lexer = HLexer::new("let x = 1; let y = 2; let z = x + y; z");
  let lexer = HLexer::new("let x = 1; let y = let w = 2 in w; let z = x[y[y]]; y");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  let ltree = ltree.root;
  println!("DEBUG: ltree: {:?}", ltree);
  println!("DEBUG: ltree, pretty printed:");
  ltree._pretty_print();
  /*let ltree = builder._ltree_env_info_pass(ltree);
  println!("DEBUG: ltree + env info: {:?}", ltree);
  let ltree = builder._ltree_freeuse_info_pass(ltree);
  println!("DEBUG: ltree + env + freeuse info: {:?}", ltree);*/
  let ltree = builder.normalize(ltree);
  println!("DEBUG: a-normalized ltree: {:?}", ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  ltree._pretty_print();
}

#[test]
fn test_ir_adj() {
  println!();
  let lexer = HLexer::new("let x = 1; let y = let w = x in w; let z = adj y; z");
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  println!("DEBUG: htree: {:?}", htree);
  let mut builder = LBuilder::new();
  let ltree = builder.lower(htree);
  //let ltree = builder.lower_with_stdlib(htree);
  let ltree = ltree.root;
  let ltree = builder._ltree_env_info_pass(ltree);
  let ltree = builder._ltree_freeuse_info_pass(ltree);
  //println!("DEBUG: ltree: {:?}", ltree);
  println!("DEBUG: ltree, pretty printed:");
  ltree._pretty_print();
  let ltree = builder.normalize(ltree);
  let ltree = builder._ltree_env_info_pass(ltree);
  let ltree = builder._ltree_freeuse_info_pass(ltree);
  //println!("DEBUG: a-normalized ltree: {:?}", ltree);
  println!("DEBUG: a-normalized ltree, pretty printed:");
  ltree._pretty_print();
}
