extern crate merwyn;

use merwyn::ir::{LBuilder};
use merwyn::lang::{HLexer, HParser};
use merwyn::vm::{VMachine};

use std::env::{args};
use std::fs::{File};
use std::io::{Read};
use std::path::{PathBuf};
use std::str::{from_utf8};

fn main() {
  let args: Vec<_> = args().collect();
  let (verbose, file_path) = if args.len() <= 1 {
    println!("usage: merwyni [-v] <file>");
    return;
  } else if args.len() == 2 {
    if args[1] == "-v" {
      println!("usage: merwyni [-v] <file>");
      return;
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, file_path)
    }
  } else if args.len() >= 3 {
    if args[1] == "-v" {
      let file_path = PathBuf::from(&args[2]);
      (true, file_path)
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, file_path)
    }
  } else {
    unreachable!();
  };
  let mut file = match File::open(file_path) {
    Err(_) => {
      println!("error opening file");
      return;
    }
    Ok(f) => f,
  };
  let mut buf = Vec::new();
  match file.read_to_end(&mut buf) {
    Err(_) => {
      println!("error reading file");
      return;
    }
    Ok(_) => {}
  }
  let text = match from_utf8(&buf) {
    Err(_) => {
      println!("invalid utf8");
      return;
    }
    Ok(s) => s,
  };
  let lexer = HLexer::new(text);
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let mut builder = LBuilder::new();
  let ltree = builder.lower_with_toplevel(htree);
  if verbose {
    println!("DEBUG: ltree, pretty printed:");
    builder.pretty_print(ltree.clone());
  }
  let ltree = builder.normalize(ltree);
  if verbose {
    println!("DEBUG: a-normalized ltree, pretty printed:");
    builder.pretty_print(ltree.clone());
  }
  let ltree = builder.expand_adj(ltree);
  if verbose {
    println!("DEBUG: adj-expanded ltree, pretty printed:");
    builder.pretty_print(ltree.clone());
  }
  let ltree = builder.normalize(ltree);
  if verbose {
    println!("DEBUG: adj-expanded, a-normalized ltree, pretty printed:");
    builder.pretty_print(ltree.clone());
  }
  let ltree = builder.resolve_ty_inf(ltree);
  if verbose {
    println!("DEBUG: ty-inf-resolved ltree, pretty printed:");
    builder.pretty_print(ltree.clone());
  }
  let ltree = ltree.root;
  let mut vm = VMachine::with_lbuilder(builder);
  let halt_mval = vm.eval(ltree);
  println!("done: {:?}", halt_mval);
}
