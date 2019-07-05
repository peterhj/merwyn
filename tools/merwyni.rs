extern crate merwyn;

use merwyn::builtins::top2::{build_top_level};
use merwyn::iio::{DefaultInteractiveIO};
use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine};

use std::env::{args};
use std::fs::{File};
use std::io::{Read};
use std::path::{PathBuf};
use std::str::{from_utf8};

fn main() {
  let args: Vec<_> = args().collect();
  let (verbose, file_path) = if args.len() <= 1 {
    (false, None)
  } else if args.len() == 2 {
    if args[1] == "-h" {
      println!("usage: merwyni [-h|<file>]");
      return;
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, Some(file_path))
    }
  } else if args.len() >= 3 {
    if args[1] == "-v" {
      let file_path = PathBuf::from(&args[2]);
      (true, Some(file_path))
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, Some(file_path))
    }
  } else {
    unreachable!();
  };
  let mut builder = LBuilder::default();
  let mut ctx = LCtxRef::empty_top_level();
  let mut tctx = LTyctxRef::default();
  //let mut ctx;
  //let mut tctx;
  let mut machine = Machine::default();
  let mut int_io = DefaultInteractiveIO::default();
  /*let top_module = build_top_level(&mut builder, ctx.clone());
  ctx = top_module.end_ctx.clone().unwrap_or_else(|| ctx);
  //machine.eval(top_module.code.clone());
  println!("merwyn# loaded top level");*/
  if let Some(file_path) = file_path {
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
    let lexer = HLexer::new(text);
    let parser = HParser::new(lexer);
    let htree = parser.parse();
    let module = match builder._compile(htree, ctx.clone(), tctx.clone()) {
      Err(_) => {
        int_io.error_print("# compile failure");
        return;
      }
      Ok(module) => module,
    };
    ctx = module.end_ctx.clone().unwrap_or_else(|| ctx);
    tctx = module.end_tctx.clone().unwrap_or_else(|| tctx);
    //machine.eval(module.code.clone());
    int_io.log_print(&format!("# loaded module `{}`", file_path.display()));
    //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
  }
  let mut eval_buf = String::new();
  loop {
    eval_buf.clear();
    int_io.eval_prompt(&mut eval_buf);
    if eval_buf == "\n" {
      continue;
    } else if eval_buf == ":help\n" || eval_buf == ":h\n" || eval_buf == ":?\n" {
      int_io.log_print("(* commands:");
      int_io.log_print("      :help :h :?      show this help message");
      int_io.log_print("      :quit :q         quit interactive mode");
      int_io.log_print("*)");
      continue;
    } else if eval_buf == ":quit\n" || eval_buf == ":q\n" {
      break;
    } else if eval_buf.chars().next() == Some(':') {
      int_io.error_print("# unknown command");
      continue;
    }
    let lexer = HLexer::new(&eval_buf);
    let parser = HParser::new(lexer);
    let htree = parser.parse();
    let module = match builder._compile(htree, ctx.clone(), tctx.clone()) {
      Err(_) => {
        int_io.error_print("# compile failure");
        continue;
      }
      Ok(module) => module,
    };
    ctx = module.end_ctx.clone().unwrap_or_else(|| ctx);
    tctx = module.end_tctx.clone().unwrap_or_else(|| tctx);
    //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
    //machine.eval(module.code.clone());
  }
}
