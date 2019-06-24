extern crate merwyn;

use merwyn::ir2::{LBuilder, LCtxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine};

use std::env::{args};
use std::fs::{File};
use std::io::{Read, Write, stdin, stdout};
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
  let mut file = match File::open(&file_path) {
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
  let mut builder = LBuilder::default();
  let lexer = HLexer::new(text);
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let module = builder.compile(htree, LCtxRef::default());
  let mut ctx = module.end_ctx.clone().unwrap_or_else(|| LCtxRef::default());
  /*let mut vm = VMachine::with_lbuilder(builder);
  vm.load_interactive(ltree);*/
  println!("merwyn# loaded module `{}`", file_path.display());
  //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
  let mut linebuf = String::new();
  loop {
    print!("merwyn> ");
    stdout().flush().unwrap();
    linebuf.clear();
    stdin().read_line(&mut linebuf).unwrap();
    if linebuf == "\n" {
      continue;
    } else if linebuf == ":help\n" || linebuf == ":h\n" || linebuf == ":?\n" {
      println!("merwyn# help yourself!");
      continue;
    }
    let lexer = HLexer::new(&linebuf);
    let parser = HParser::new(lexer);
    let htree = parser.parse();
    let module = builder.compile(htree, ctx);
    ctx = module.end_ctx.clone().unwrap_or_else(|| LCtxRef::default());
    //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
    /*vm.put_lbuilder(builder);
    vm.eval_interactive(ltree);*/
  }
}
