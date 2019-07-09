// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::build::{GIT_COMMIT_HASH, GIT_MODIFIED};
use crate::ir2::{LBuilder};
use crate::mach::{Machine};

use termion::{AsyncReader, async_stdin};
use termion::clear::{CurrentLine};
use termion::cursor::{Left, Right};
use termion::raw::{IntoRawMode};

use std::collections::{VecDeque};
use std::fmt::{self, Write as FmtWrite};
use std::io::{Bytes, Read, Write, stdout};
use std::str::{from_utf8};
use std::sync::mpsc::{Receiver, Sender, SyncSender, channel, sync_channel};
use std::thread::{JoinHandle, sleep, spawn};
use std::time::{Duration};

const CTRL_A: u8 = 1;
const CTRL_C: u8 = 3;
const CTRL_D: u8 = 4;
const CTRL_E: u8 = 5;
const CTRL_H: u8 = 8;
const TAB:    u8 = 9;
const ESC:    u8 = 27;
const LEFT:   u8 = 37;
const UP:     u8 = 38;
const RIGHT:  u8 = 39;
const DOWN:   u8 = 40;
const BACK:   u8 = 127;

pub struct ReplLineWriter {
  linemode: ReplLineMode,
  ctrl_tq:  Sender<ReplCtrl>,
  buf:      String,
}

impl FmtWrite for ReplLineWriter {
  fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
    let mut toks = s.split("\n");
    match toks.next() {
      None => return Ok(()),
      Some(t) => {
        self.buf.push_str(t);
      }
    }
    for t in toks {
      self.ctrl_tq.send(ReplCtrl::Line(self.linemode, self.buf.clone()))
        .map_err(|_| fmt::Error)?;
      self.buf.clear();
      self.buf.push_str(t);
    }
    Ok(())
  }
}

impl ReplLineWriter {
  pub fn new_error(ctrl_tq: Sender<ReplCtrl>) -> ReplLineWriter {
    ReplLineWriter{
      linemode: ReplLineMode::Error,
      ctrl_tq,
      buf:      String::new(),
    }
  }

  pub fn new_info(ctrl_tq: Sender<ReplCtrl>) -> ReplLineWriter {
    ReplLineWriter{
      linemode: ReplLineMode::Info,
      ctrl_tq,
      buf:      String::new(),
    }
  }

  pub fn new_trace(ctrl_tq: Sender<ReplCtrl>) -> ReplLineWriter {
    ReplLineWriter{
      linemode: ReplLineMode::Trace,
      ctrl_tq,
      buf:      String::new(),
    }
  }
}

pub struct ReplInterpreter {
  ctrl_tq:  Sender<ReplCtrl>,
  error_fd: ReplLineWriter,
  info_fd:  ReplLineWriter,
  trace_fd:  ReplLineWriter,
  line_rq:  Receiver<ReplLine>,
  builder:  LBuilder,
  machine:  Machine,
}

impl ReplInterpreter {
  pub fn new(ctrl_tq: Sender<ReplCtrl>, line_rq: Receiver<ReplLine>) -> ReplInterpreter {
    ReplInterpreter::with_machine(ctrl_tq, line_rq, Machine::default())
  }

  pub fn with_machine(ctrl_tq: Sender<ReplCtrl>, line_rq: Receiver<ReplLine>, machine: Machine) -> ReplInterpreter {
    let error_fd = ReplLineWriter::new_error(ctrl_tq.clone());
    let info_fd = ReplLineWriter::new_info(ctrl_tq.clone());
    let trace_fd = ReplLineWriter::new_trace(ctrl_tq.clone());
    ReplInterpreter{
      ctrl_tq,
      error_fd,
      info_fd,
      trace_fd,
      line_rq,
      builder:  LBuilder::default(),
      machine,
    }
  }

  pub fn eval_loop(&mut self) {
    writeln!(&mut self.info_fd, "(** Merwyn interactive mode | git:{}{} | :? for help *)",
        GIT_COMMIT_HASH,
        if GIT_MODIFIED { "-mod" } else { "" }).unwrap();
    self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
    loop {
      match self.line_rq.recv() {
        Ok(ReplLine::Prompt(_)) => {
          writeln!(&mut self.trace_fd, "# todo: machine eval").unwrap();
          self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
        }
        Ok(ReplLine::Command(cmd_buf)) => {
          match &cmd_buf as &str {
            "?" | "h" | "help" => {
              writeln!(&mut self.info_fd, "(** Interactive commands:").unwrap();
              writeln!(&mut self.info_fd, "        :? :h :help     show this help message").unwrap();
              writeln!(&mut self.info_fd, "        :q :quit        quit repl").unwrap();
              writeln!(&mut self.info_fd, "*)").unwrap();
              self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
            }
            "q" | "quit" => {
              writeln!(&mut self.info_fd, "(* Goodbye... *)").unwrap();
              self.ctrl_tq.send(ReplCtrl::Halt).unwrap();
              break;
            }
            "hello" => {
              sleep(Duration::from_millis(450));
              writeln!(&mut self.trace_fd, "(* Hello, world! *)").unwrap();
              sleep(Duration::from_millis(300));
              self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
            }
            _ => {
              self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
            }
          }
        }
        Err(_) => {
          break;
        }
      }
    }
  }
}

pub enum ReplCtrl {
  Halt,
  IO(ReplIOMode),
  Line(ReplLineMode, String),
}

pub enum ReplLine {
  Prompt(String),
  Command(String),
}

#[derive(Clone, Copy)]
pub enum ReplIOMode {
  NoIO,
  Blocked,
  Prompt,
  Command,
  Stdin,
}

#[derive(Clone, Copy)]
pub enum ReplLineMode {
  Prompt,
  Command,
  Error,
  Info,
  Trace,
  Stdout,
}

pub struct ReplTermState {
  blocked:  String,
  query:    String,
  answer:   String,
  mode:     ReplIOMode,
  history:  VecDeque<String>,
  savebuf:  Option<String>,
  scroll:   usize,
  commit:   Option<String>,
  tmpbuf:   String,
  tmppos:   usize,
}

impl Default for ReplTermState {
  fn default() -> ReplTermState {
    ReplTermState{
      blocked:  "...   ".to_string(),
      query:    "merwyn".to_string(),
      answer:   "merwyn".to_string(),
      mode:     ReplIOMode::Blocked,
      history:  VecDeque::new(),
      savebuf:  None,
      scroll:   0,
      commit:   None,
      tmpbuf:   String::new(),
      tmppos:   0,
    }
  }
}

impl ReplTermState {
  fn query(&mut self, stdout: &mut dyn Write) {
    match self.mode {
      ReplIOMode::NoIO => {
        return;
      }
      ReplIOMode::Blocked => {
        write!(stdout, "{}\r{}  {}", CurrentLine, self.blocked, self.tmpbuf).unwrap();
      }
      ReplIOMode::Prompt => {
        write!(stdout, "{}\r{}- {}", CurrentLine, self.query, self.tmpbuf).unwrap();
      }
      ReplIOMode::Command => {
        write!(stdout, "{}\r{}-:{}", CurrentLine, self.query, self.tmpbuf).unwrap();
      }
      ReplIOMode::Stdin => {
        write!(stdout, "{}\r{}< {}", CurrentLine, self.query, self.tmpbuf).unwrap();
      }
    }
    if self.tmppos < self.tmpbuf.len() {
      let offset = (self.tmpbuf.len() - self.tmppos) as u16;
      write!(stdout, "{}", Left(offset)).unwrap();
    }
  }

  fn answer(&mut self, stdout: &mut dyn Write, linemode: ReplLineMode, line: &String) {
    match self.mode {
      ReplIOMode::NoIO => {
        return;
      }
      _ => match linemode {
        ReplLineMode::Prompt => {
          write!(stdout, "{}= {}\r\n", self.answer, line).unwrap();
        }
        ReplLineMode::Command => {
          write!(stdout, "{}=:{}\r\n", self.answer, line).unwrap();
        }
        ReplLineMode::Error => {
          write!(stdout, "{}! {}\r\n", self.answer, line).unwrap();
        }
        ReplLineMode::Info => {
          write!(stdout, "{}. {}\r\n", self.answer, line).unwrap();
        }
        ReplLineMode::Trace => {
          write!(stdout, "{}% {}\r\n", self.answer, line).unwrap();
        }
        ReplLineMode::Stdout => {
          write!(stdout, "{}> {}\r\n", self.answer, line).unwrap();
        }
      }
    }
  }

  fn drain(&mut self, stdin: &mut Bytes<AsyncReader>, stdout: &mut dyn Write) -> bool {
    match self.mode {
      ReplIOMode::NoIO => {
        panic!("This is almost certainly a bug.");
      }
      ReplIOMode::Blocked => loop {
        match stdin.next() {
          Some(Ok(CTRL_C)) => {
            // TODO: signal.
            //write!(stdout, "^C\r\n").unwrap();
            return true;
          }
          Some(Ok(CTRL_D)) => {
            write!(stdout, "^D\r\n").unwrap();
            return true;
          }
          Some(Ok(_)) => {}
          Some(Err(_)) |
          None => {
            break;
          }
        }
      },
      _ => loop {
        match stdin.next() {
          Some(Ok(CTRL_C)) => {
            // TODO: signal.
            //write!(stdout, "^C\r\n").unwrap();
            return true;
          }
          Some(Ok(CTRL_D)) => {
            write!(stdout, "^D\r\n").unwrap();
            return true;
          }
          Some(Ok(b'\n')) => {}
          Some(Ok(b'\r')) => {
            self.savebuf = None;
            self.commit = Some(self.tmpbuf.clone());
            self.tmpbuf.clear();
            self.tmppos = 0;
          }
          Some(Ok(b':')) => {
            if !self.tmpbuf.is_empty() {
              let c = b':' as char;
              self.tmpbuf.push(c);
              self.tmppos += 1;
              write!(stdout, "{}", c).unwrap();
              return false;
            }
            self.mode = ReplIOMode::Command;
            self.query(stdout);
          }
          Some(Ok(CTRL_H)) |
          Some(Ok(BACK)) => {
            // FIXME
            match self.mode {
              ReplIOMode::Command => {
                if self.tmpbuf.is_empty() {
                  self.mode = ReplIOMode::Prompt;
                  self.query(stdout);
                } else if !self.tmpbuf.is_empty() && self.tmppos > 0 {
                  self.tmpbuf.pop();
                  self.tmppos -= 1;
                  write!(stdout, "{} {}", Left(1), Left(1)).unwrap();
                }
              }
              _ => {
                if !self.tmpbuf.is_empty() && self.tmppos > 0 {
                  self.tmpbuf.pop();
                  self.tmppos -= 1;
                  write!(stdout, "{} {}", Left(1), Left(1)).unwrap();
                }
              }
            }
          }
          Some(Ok(TAB)) => {}
          Some(Ok(LEFT)) |
          Some(Ok(UP)) |
          Some(Ok(RIGHT)) |
          Some(Ok(DOWN)) => {}
          Some(Ok(CTRL_A)) => {
            if self.tmppos > 0 {
              let offset = self.tmppos as u16;
              self.tmppos = 0;
              write!(stdout, "{}", Left(offset)).unwrap();
            }
          }
          Some(Ok(CTRL_E)) => {
            if self.tmppos < self.tmpbuf.len() {
              let offset = (self.tmpbuf.len() - self.tmppos) as u16;
              self.tmppos = self.tmpbuf.len();
              write!(stdout, "{}", Right(offset)).unwrap();
            }
          }
          Some(Ok(ESC)) => {
            match stdin.next() {
              Some(Ok(b'[')) => {
                match stdin.next() {
                  Some(Ok(b'A')) => {
                    // Up.
                    if self.scroll > 0 {
                      self.scroll -= 1;
                      if self.savebuf.is_none() {
                        self.savebuf = Some(self.tmpbuf.clone());
                      }
                      self.tmpbuf = self.history[self.scroll].clone();
                      self.tmppos = self.tmpbuf.len();
                      self.query(stdout);
                    }
                  }
                  Some(Ok(b'B')) => {
                    // Down.
                    if self.scroll < self.history.len() {
                      self.scroll += 1;
                      if self.scroll == self.history.len() {
                        if let Some(savebuf) = self.savebuf.take() {
                          self.tmpbuf = savebuf;
                        }
                      } else {
                        self.tmpbuf = self.history[self.scroll].clone();
                      }
                      self.tmppos = self.tmpbuf.len();
                      self.query(stdout);
                    }
                  }
                  Some(Ok(b'C')) => {
                    // Right.
                    if self.tmppos < self.tmpbuf.len() {
                      self.tmppos += 1;
                      write!(stdout, "{}", Right(1)).unwrap();
                    }
                  }
                  Some(Ok(b'D')) => {
                    // Left.
                    if self.tmppos > 0 {
                      self.tmppos -= 1;
                      write!(stdout, "{}", Left(1)).unwrap();
                    }
                  }
                  Some(Ok(b)) => {
                    write!(stdout, "^[\\x{:x}", b).unwrap();
                  }
                  _ => {}
                }
              }
              _ => {}
            }
          }
          Some(Ok(b)) => {
            let c = b as char;
            self.tmpbuf.push(c);
            self.tmppos += 1;
            write!(stdout, "{}", c).unwrap();
          }
          Some(Err(_)) |
          None => {
            break;
          }
        }
      }
    }
    false
  }
}

pub struct ReplTerminal {
  term:     ReplTermState,
  ctrl_rq:  Receiver<ReplCtrl>,
  //ctrl_tq:  Sender<ReplCtrl>,
  line_tq:  Sender<ReplLine>,
}

impl ReplTerminal {
  pub fn new() -> (ReplTerminal, Sender<ReplCtrl>, Receiver<ReplLine>) {
    let (ctrl_tq, ctrl_rq) = channel();
    let (line_tq, line_rq) = channel();
    (ReplTerminal{
      term:     ReplTermState::default(),
      ctrl_rq,
      //ctrl_tq:  ctrl_tq.clone(),
      line_tq,
    }, ctrl_tq, line_rq)
  }
}

impl ReplTerminal {
  pub fn start_async() -> (JoinHandle<()>, Sender<ReplCtrl>, Receiver<ReplLine>) {
    let (mut repl_term, ctrl_tq, line_rq) = ReplTerminal::new();
    let h = spawn(move || repl_term.runloop());
    (h, ctrl_tq, line_rq)
  }

  pub fn runloop(&mut self) {
    let mut stdin = async_stdin().bytes();
    let stdout = stdout();
    let mut stdout = stdout.lock().into_raw_mode().unwrap();
    self.term.mode = ReplIOMode::Blocked;
    self.term.query(&mut stdout);
    stdout.flush().unwrap();
    let sleep_delay = Duration::from_millis(8);
    let mut ctr = 0;
    'main_loop: loop {
      if self.term.drain(&mut stdin, &mut stdout) {
        break;
      }
      let mut commit = false;
      loop {
        match self.ctrl_rq.try_recv() {
          Ok(ReplCtrl::Halt) => {
            break 'main_loop;
          }
          Ok(ReplCtrl::IO(iomode)) => {
            if !commit {
              write!(&mut stdout, "{}\r", CurrentLine).unwrap();
              commit = true;
            }
            self.term.mode = iomode;
          }
          Ok(ReplCtrl::Line(linemode, msg)) => {
            if !commit {
              write!(&mut stdout, "{}\r", CurrentLine).unwrap();
              commit = true;
            }
            self.term.answer(&mut stdout, linemode, &msg);
          }
          _ => {
            break;
          }
        }
      }
      if let Some(line) = self.term.commit.take() {
        if !commit {
          write!(&mut stdout, "{}\r", CurrentLine).unwrap();
          commit = true;
        }
        match self.term.mode {
          ReplIOMode::Prompt => {
            self.term.answer(&mut stdout, ReplLineMode::Prompt, &line);
          }
          ReplIOMode::Command => {
            self.term.answer(&mut stdout, ReplLineMode::Command, &line);
          }
          _ => {}
        }
        if !line.is_empty() {
          self.term.history.push_back(line.clone());
          self.term.scroll += 1;
          match self.term.mode {
            ReplIOMode::Prompt => {
              self.line_tq.send(ReplLine::Prompt(line)).unwrap();
            }
            ReplIOMode::Command => {
              self.line_tq.send(ReplLine::Command(line)).unwrap();
            }
            _ => {}
          }
          self.term.mode = ReplIOMode::Blocked;
        }
      }
      if commit {
        self.term.query(&mut stdout);
      }
      stdout.flush().unwrap();
      sleep(sleep_delay);
    }
    stdout.flush().unwrap();
  }
}
