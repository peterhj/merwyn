// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::io::{Write, stdin, stdout};

pub struct DefaultInteractiveIO {
  prefix:   String,
}

impl Default for DefaultInteractiveIO {
  fn default() -> DefaultInteractiveIO {
    DefaultInteractiveIO{prefix: "merwyn".to_owned()}
  }
}

impl DefaultInteractiveIO {
  pub fn new(prefix: String) -> DefaultInteractiveIO {
    DefaultInteractiveIO{prefix}
  }

  pub fn eval_prompt(&mut self, linebuf: &mut String) {
    print!("{}- ", self.prefix);
    stdout().flush().unwrap();
    stdin().read_line(linebuf).unwrap();
  }

  pub fn stdin_line_prompt(&mut self, linebuf: &mut String) {
    print!("{}< ", self.prefix);
    stdout().flush().unwrap();
    stdin().read_line(linebuf).unwrap();
  }

  pub fn log_print(&mut self, msg: &str) {
    println!("{}. {}", self.prefix, msg);
    stdout().flush().unwrap();
  }

  pub fn debug_print(&mut self, msg: &str) {
    println!("{}: {}", self.prefix, msg);
    stdout().flush().unwrap();
  }

  pub fn error_print(&mut self, msg: &str) {
    println!("{}! {}", self.prefix, msg);
    stdout().flush().unwrap();
  }

  pub fn trace_print(&mut self, msg: &str) {
    println!("{}% {}", self.prefix, msg);
    stdout().flush().unwrap();
  }

  pub fn stdout_line_print(&mut self, msg: &str) {
    println!("{}> {}", self.prefix, msg);
    stdout().flush().unwrap();
  }
}
