// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate merwyn;

//use merwyn::builtins::top2::{build_top_level};
use merwyn::ir2::{LBuilder, LCtxRef, LTyctxRef};
use merwyn::lang::{HLexer, HParser};
use merwyn::mach::{Machine};
use merwyn::repl::{async_repl_terminal};

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
    if args[1] == "-v" || args[1] == "-verbose" {
      (true, None)
    } else if args[1].chars().next() == Some('-') {
      println!("Usage: merwyni [-v|-verbose] [<src.merwyn>]");
      return;
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, Some(file_path))
    }
  } else if args.len() >= 3 {
    if args[1] == "-v" || args[1] == "-verbose" {
      let file_path = PathBuf::from(&args[2]);
      (true, Some(file_path))
    } else {
      let file_path = PathBuf::from(&args[1]);
      (false, Some(file_path))
    }
  } else {
    unreachable!();
  };

  /*let mut builder = LBuilder::default();
  let mut ctx = LCtxRef::empty_top_level();
  let mut tctx = LTyctxRef::default();
  let mut machine = Machine::default();

  if let Some(file_path) = file_path.clone() {
    let mut file = match File::open(&file_path) {
      Err(_) => {
        println!("error opening file");
        return;
        //return Some(ReplIOMode::Prompt);
      }
      Ok(f) => f,
    };
    let mut buf = Vec::new();
    match file.read_to_end(&mut buf) {
      Err(_) => {
        println!("error reading file");
        return;
        //return Some(ReplIOMode::Prompt);
      }
      Ok(_) => {}
    }
    let text = match from_utf8(&buf) {
      Err(_) => {
        println!("invalid utf8");
        return;
        //return Some(ReplIOMode::Prompt);
      }
      Ok(s) => s,
    };
    let lexer = HLexer::new(text);
    let parser = HParser::new(lexer);
    let htree = parser.parse();
    let module = match builder._compile(htree, ctx.clone(), tctx.clone()) {
      Err(_) => {
        //int_io.error_print("# compile failure");
        println!("top level module compilation failed");
        return;
        //return Some(ReplIOMode::Prompt);
      }
      Ok(module) => module,
    };
    ctx = module.end_ctx.clone().unwrap_or_else(|| ctx.clone());
    tctx = module.end_tctx.clone().unwrap_or_else(|| tctx.clone());
    //machine.eval(module.code.clone());
    //int_io.trace_print(&format!("# loaded module `{}`", file_path.display()));
    //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
  }*/

  let (repl_term, repl_intp) = async_repl_terminal();
  repl_intp.runloop();
  repl_term.join().unwrap();

  /*repl.runloop(
      &mut || {
        /*if let Some(file_path) = file_path.clone() {
          let mut file = match File::open(&file_path) {
            Err(_) => {
              //println!("error opening file");
              return Some(ReplIOMode::Prompt);
            }
            Ok(f) => f,
          };
          let mut buf = Vec::new();
          match file.read_to_end(&mut buf) {
            Err(_) => {
              //println!("error reading file");
              return Some(ReplIOMode::Prompt);
            }
            Ok(_) => {}
          }
          let text = match from_utf8(&buf) {
            Err(_) => {
              //println!("invalid utf8");
              return Some(ReplIOMode::Prompt);
            }
            Ok(s) => s,
          };
          let lexer = HLexer::new(text);
          let parser = HParser::new(lexer);
          let htree = parser.parse();
          let module = match builder._compile(htree, ctx.clone(), tctx.clone()) {
            Err(_) => {
              //int_io.error_print("# compile failure");
              return Some(ReplIOMode::Prompt);
            }
            Ok(module) => module,
          };
          ctx = module.end_ctx.clone().unwrap_or_else(|| ctx.clone());
          tctx = module.end_tctx.clone().unwrap_or_else(|| tctx.clone());
          //machine.eval(module.code.clone());
          //int_io.trace_print(&format!("# loaded module `{}`", file_path.display()));
          //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
        }*/
        Some(ReplIOMode::Blocked)
      },
      &mut |eval_buf| {
        /*if eval_buf == "\n" {
          //continue;
          return Some(ReplIOMode::Prompt);
        } else if eval_buf == ":help\n" || eval_buf == ":h\n" || eval_buf == ":?\n" {
          //int_io.log_print("(* commands:");
          //int_io.log_print("      :help :h :?      show this help message");
          //int_io.log_print("      :quit :q         quit interactive mode");
          //int_io.log_print("*)");
          //continue;
          return Some(ReplIOMode::Prompt);
        } else if eval_buf == ":quit\n" || eval_buf == ":q\n" {
          //break;
          return Some(ReplIOMode::Prompt);
        } else if eval_buf.chars().next() == Some(':') {
          //int_io.error_print("# unknown command");
          //continue;
          return Some(ReplIOMode::Prompt);
        }
        let lexer = HLexer::new(&eval_buf);
        let parser = HParser::new(lexer);
        let htree = parser.parse();
        let module = match builder._compile(htree, ctx.clone(), tctx.clone()) {
          Err(_) => {
            //int_io.error_print("# compile failure");
            //continue;
            return Some(ReplIOMode::Prompt);
          }
          Ok(module) => module,
        };
        ctx = module.end_ctx.clone().unwrap_or_else(|| ctx.clone());
        tctx = module.end_tctx.clone().unwrap_or_else(|| tctx.clone());
        //println!("merwyn# --  debug tree: {:?}", module.tree.exps);
        //machine.eval(module.code.clone());*/
        Some(ReplIOMode::Prompt)
      }
  );*/
}
