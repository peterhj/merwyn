// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::arch_util::{CpuInfo, GpuInfo};
use crate::build::{GIT_COMMIT_HASH, GIT_MODIFIED};
use crate::ir2::{LBuilder};
use crate::mach::{Machine};

use libc::{termios};

use std::collections::{VecDeque};
use std::fmt::{Display, Error as FmtError, Result as FmtResult, Formatter, Write as FmtWrite};
use std::fs::{File, OpenOptions};
use std::io::{Bytes, Error as IoError, Result as IoResult, Read, Write, stdout};
use std::mem::{zeroed};
use std::ops::{Deref, DerefMut};
use std::os::raw::{c_int};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::thread::{JoinHandle, sleep, spawn};
use std::time::{Duration, Instant};

/* Some parts below were thinly adapted from termion: */

/* termion
   (authors: ticki <Ticki@users.noreply.github.com>,
    gycos <alexandre.bury@gmail.com>,
    IGI-111 <igi-111@protonmail.com>):

The MIT License (MIT)

Copyright (c) 2016 Ticki

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

// Create a CSI-introduced sequence.
macro_rules! csi {
  ($( $l:expr ),*) => { concat!("\x1B[", $( $l ),*) };
}

// Derive a CSI sequence struct.
macro_rules! derive_csi_sequence {
  ($doc:expr, $name:ident, $value:expr) => {
    #[doc = $doc]
    #[derive(Copy, Clone)]
    pub struct $name;

    impl Display for $name {
      fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, csi!($value))
      }
    }

    impl AsRef<[u8]> for $name {
      fn as_ref(&self) -> &'static [u8] { csi!($value).as_bytes() }
    }

    impl AsRef<str> for $name {
      fn as_ref(&self) -> &'static str { csi!($value) }
    }
  };
}

derive_csi_sequence!("Clear the current line.", ClearCurrentLine, "2K");

// Move cursor left.
#[derive(Copy, Clone, PartialEq, Eq)]
struct CursorLeft(pub u16);

impl From<CursorLeft> for String {
  fn from(this: CursorLeft) -> String {
    let mut buf = [0u8; 20];
    format!("\x1B[{}D", this.0)
  }
}

impl Display for CursorLeft {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    f.write_str(&String::from(*self))
  }
}

// Move cursor right.
#[derive(Copy, Clone, PartialEq, Eq)]
struct CursorRight(pub u16);

impl From<CursorRight> for String {
  fn from(this: CursorRight) -> String {
    let mut buf = [0u8; 20];
    format!("\x1B[{}C", this.0)
  }
}

impl Display for CursorRight {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    f.write_str(&String::from(*self))
  }
}

// Managing raw mode.
//
// Raw mode is a particular state a TTY can have. It signifies that:
//
// 1. No line buffering (the input is given byte-by-byte).
// 2. The input is not written out, instead it has to be done manually by the programmer.
// 3. The output is not canonicalized (for example, `\n` means "go one line down", not "line
//    break").
//
// It is essential to design terminal programs.
//
// # Example
//
// ```rust,no_run
// use termion::raw::IntoRawMode;
// use std::io::{Write, stdout};
//
// fn main() {
//     let mut stdout = stdout().into_raw_mode().unwrap();
//
//     write!(stdout, "Hey there.").unwrap();
// }
// ```

fn int2result(t: c_int) -> IoResult<c_int> {
  if t == -1 {
    Err(IoError::last_os_error())
  } else {
    Ok(t)
  }
}

fn get_terminal_attr() -> IoResult<termios> {
  extern "C" {
    pub fn tcgetattr(fd: c_int, termptr: *mut termios) -> c_int;
  }
  unsafe {
    let mut termios = zeroed();
    int2result(tcgetattr(1, &mut termios))?;
    Ok(termios)
  }
}

fn set_terminal_attr(termios: &termios) -> IoResult<()> {
  extern "C" {
    pub fn tcsetattr(fd: c_int, opt: c_int, termptr: *const termios) -> c_int;
  }
  int2result(unsafe { tcsetattr(1, 0, termios) }).and(Ok(()))
}

fn raw_terminal_attr(termios: &mut termios) {
  extern "C" {
    pub fn cfmakeraw(termptr: *mut termios);
  }
  unsafe { cfmakeraw(termios) }
}

// A terminal restorer, which keeps the previous state of the terminal, and restores it, when
// dropped.
//
// Restoring will entirely bring back the old TTY state.
struct RawTerminal<W: Write> {
  prev_ios: termios,
  output: W,
}

impl<W: Write> Drop for RawTerminal<W> {
  fn drop(&mut self) {
    set_terminal_attr(&self.prev_ios).unwrap();
  }
}

impl<W: Write> Deref for RawTerminal<W> {
  type Target = W;

  fn deref(&self) -> &W {
    &self.output
  }
}

impl<W: Write> DerefMut for RawTerminal<W> {
  fn deref_mut(&mut self) -> &mut W {
    &mut self.output
  }
}

impl<W: Write> Write for RawTerminal<W> {
  fn write(&mut self, buf: &[u8]) -> IoResult<usize> {
    self.output.write(buf)
  }

  fn flush(&mut self) -> IoResult<()> {
    self.output.flush()
  }
}

/// Types which can be converted into "raw mode".
///
/// # Why is this type defined on writers and not readers?
///
/// TTYs has their state controlled by the writer, not the reader. You use the writer to clear the
/// screen, move the cursor and so on, so naturally you use the writer to change the mode as well.
trait IntoRawMode: Write + Sized {
  /// Switch to raw mode.
  ///
  /// Raw mode means that stdin won't be printed (it will instead have to be written manually by
  /// the program). Furthermore, the input isn't canonicalised or buffered (that is, you can
  /// read from stdin one byte of a time). The output is neither modified in any way.
  fn into_raw_mode(self) -> IoResult<RawTerminal<Self>>;
}

impl<W: Write> IntoRawMode for W {
  fn into_raw_mode(self) -> IoResult<RawTerminal<W>> {
    let mut ios = get_terminal_attr()?;
    let prev_ios = ios;

    raw_terminal_attr(&mut ios);

    set_terminal_attr(&ios)?;

    Ok(RawTerminal {
      prev_ios: prev_ios,
      output: self,
    })
  }
}

impl<W: Write> RawTerminal<W> {
  fn suspend_raw_mode(&self) -> IoResult<()> {
    set_terminal_attr(&self.prev_ios)?;
    Ok(())
  }

  fn activate_raw_mode(&self) -> IoResult<()> {
    let mut ios = get_terminal_attr()?;
    raw_terminal_attr(&mut ios);
    set_terminal_attr(&ios)?;
    Ok(())
  }
}

// Get the TTY device.
//
// This allows for getting stdio representing _only_ the TTY, and not other streams.
fn get_tty() -> IoResult<File> {
  OpenOptions::new().read(true).write(true).open("/dev/tty")
}

// Construct an asynchronous handle to the TTY standard input.
//
// This allows you to read from standard input _without blocking_ the current thread.
// Specifically, it works by firing up another thread to handle the event stream, which will then
// be buffered in a mpsc queue, which will eventually be read by the current thread.
//
// This will not read the piped standard input, but rather read from the TTY device, since reading
// asyncronized from piped input would rarely make sense. In other words, if you pipe standard
// output from another process, it won't be reflected in the stream returned by this function, as
// this represents the TTY device, and not the piped standard input.
fn async_stdin() -> AsyncReader {
  let (send, recv) = channel();

  spawn(move || for i in get_tty().unwrap().bytes() {
    if send.send(i).is_err() {
      return;
    }
  });

  AsyncReader { recv: recv }
}

// An asynchronous reader.
//
// This acts as any other stream, with the exception that reading from it won't block. Instead,
// the buffer will only be partially updated based on how much the internal buffer holds.
pub struct AsyncReader {
  // The underlying mpsc receiver.
  recv: Receiver<IoResult<u8>>,
}

impl Read for AsyncReader {
  // Read from the byte stream.
  //
  // This will never block, but try to drain the event queue until empty. If the total number of
  // bytes written is lower than the buffer's length, the event queue is empty or that the event
  // stream halted.
  fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
    let mut total = 0;

    loop {
      if total >= buf.len() {
        break;
      }

      match self.recv.try_recv() {
        Ok(Ok(b)) => {
          buf[total] = b;
          total += 1;
        }
        Ok(Err(e)) => return Err(e),
        Err(_) => break,
      }
    }

    Ok(total)
  }
}

const CTRL_A: u8 = 1;
const CTRL_C: u8 = 3;
const CTRL_D: u8 = 4;
const CTRL_E: u8 = 5;
const CTRL_H: u8 = 8;
const TAB:    u8 = 9;
//const CTRL_K: u8 = 11;
//const CTRL_U: u8 = 21;
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
  fn write_str(&mut self, s: &str) -> Result<(), FmtError> {
    let mut toks = s.split('\n');
    match toks.next() {
      None => return Ok(()),
      Some(t) => {
        self.buf.push_str(t);
      }
    }
    for t in toks {
      self.ctrl_tq.send(ReplCtrl::Line(self.linemode, self.buf.clone()))
        .map_err(|_| FmtError)?;
      self.buf.clear();
      self.buf.push_str(t);
    }
    Ok(())
  }
}

impl ReplLineWriter {
  pub fn new_prompt(ctrl_tq: Sender<ReplCtrl>) -> ReplLineWriter {
    ReplLineWriter{
      linemode: ReplLineMode::Prompt,
      ctrl_tq,
      buf:      String::new(),
    }
  }

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
  prmpt_fd: ReplLineWriter,
  error_fd: ReplLineWriter,
  info_fd:  ReplLineWriter,
  trace_fd: ReplLineWriter,
  line_rq:  Receiver<ReplLine>,
  builder:  LBuilder,
  machine:  Machine,
  mod_ctr:  usize,
}

impl ReplInterpreter {
  pub fn new(ctrl_tq: Sender<ReplCtrl>, line_rq: Receiver<ReplLine>) -> ReplInterpreter {
    ReplInterpreter::with_machine(ctrl_tq, line_rq, Machine::default())
  }

  pub fn with_machine(ctrl_tq: Sender<ReplCtrl>, line_rq: Receiver<ReplLine>, machine: Machine) -> ReplInterpreter {
    let prmpt_fd = ReplLineWriter::new_prompt(ctrl_tq.clone());
    let error_fd = ReplLineWriter::new_error(ctrl_tq.clone());
    let info_fd = ReplLineWriter::new_info(ctrl_tq.clone());
    let trace_fd = ReplLineWriter::new_trace(ctrl_tq.clone());
    ReplInterpreter{
      ctrl_tq,
      prmpt_fd,
      error_fd,
      info_fd,
      trace_fd,
      line_rq,
      builder:  LBuilder::default(),
      machine,
      mod_ctr:  0,
    }
  }

  fn write_usage(&mut self) {
  }

  fn write_help(&mut self) {
    writeln!(&mut self.info_fd, "(| ").unwrap();
    //writeln!(&mut self.info_fd, "").unwrap();
    writeln!(&mut self.info_fd, "Usage: `merwyni [-v|-verbose] [<src.merwyn>]`").unwrap();
    writeln!(&mut self.info_fd, "").unwrap();
    writeln!(&mut self.info_fd, "\t-v -verbose\t").unwrap();
    writeln!(&mut self.info_fd, "\t<src.merwyn>\tPath to the source of the").unwrap();
    writeln!(&mut self.info_fd, "\t\t\tinitial user module").unwrap();
    writeln!(&mut self.info_fd, "").unwrap();
    writeln!(&mut self.info_fd, "General Commands").unwrap();
    writeln!(&mut self.info_fd, "\t:? :h :help \tShow this help message").unwrap();
    writeln!(&mut self.info_fd, "\t:q :quit    \tQuit repl").unwrap();
    //writeln!(&mut self.info_fd, "\t:               repeat the previous command").unwrap();
    writeln!(&mut self.info_fd, "").unwrap();
    writeln!(&mut self.info_fd, "Programming").unwrap();
    writeln!(&mut self.info_fd, "\t<expr>      \tEvaluate the expression <expr>").unwrap();
    writeln!(&mut self.info_fd, "|)").unwrap();
  }

  pub fn runloop(mut self) {
    writeln!(&mut self.info_fd,
        "(| Merwyn | git:{}..{} | {}{} | :? for help |)",
        &GIT_COMMIT_HASH[ .. 7],
        if GIT_MODIFIED { "+mod" } else { "." },
        CpuInfo::cached().digest(),
        match GpuInfo::cached().digest() {
          Some(s) => format!(" | {}", s),
          None => "".to_owned(),
        },
    ).unwrap();
    self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
    loop {
      match self.line_rq.recv() {
        Ok(ReplLine::Prompt(eval_buf)) => {
          // FIXME
          self.mod_ctr += 1;
          assert!(self.mod_ctr != 0);
          writeln!(&mut self.prmpt_fd, "(--:{}--) {}", self.mod_ctr, eval_buf).unwrap();
          writeln!(&mut self.trace_fd, "-- TODO: The repl is currently unplugged from the embedded").unwrap();
          writeln!(&mut self.trace_fd, "-- interpreter, so expression evaluation will not yet work.").unwrap();
          writeln!(&mut self.trace_fd, "-- But please feel free to look around (type :? for help).").unwrap();
          self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
        }
        Ok(ReplLine::Command(cmd_buf)) => {
          match &cmd_buf as &str {
            "?" | "h" | "help" => {
              self.write_help();
              self.ctrl_tq.send(ReplCtrl::IO(ReplIOMode::Prompt)).unwrap();
            }
            "q" | "quit" => {
              writeln!(&mut self.info_fd, "(-- Goodbye. --)").unwrap();
              self.ctrl_tq.send(ReplCtrl::Halt).unwrap();
              break;
            }
            "hello" => {
              sleep(Duration::from_millis(450));
              writeln!(&mut self.trace_fd, "(-- Hello, world! --)").unwrap();
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
      query:    "Merwyn".to_string(),
      answer:   "Merwyn".to_string(),
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
        write!(stdout, "{}\r{}  {}", ClearCurrentLine, self.blocked, self.tmpbuf).unwrap();
      }
      ReplIOMode::Prompt => {
        write!(stdout, "{}\r{}- {}", ClearCurrentLine, self.query, self.tmpbuf).unwrap();
      }
      ReplIOMode::Command => {
        write!(stdout, "{}\r{}-:{}", ClearCurrentLine, self.query, self.tmpbuf).unwrap();
      }
      ReplIOMode::Stdin => {
        write!(stdout, "{}\r{}< {}", ClearCurrentLine, self.query, self.tmpbuf).unwrap();
      }
    }
    if self.tmppos < self.tmpbuf.len() {
      let offset = (self.tmpbuf.len() - self.tmppos) as u16;
      write!(stdout, "{}", CursorLeft(offset)).unwrap();
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
            match self.mode {
              ReplIOMode::Command => {
                if self.tmpbuf.is_empty() {
                  self.mode = ReplIOMode::Prompt;
                  self.query(stdout);
                } else if self.tmppos == self.tmpbuf.len() && !self.tmpbuf.is_empty() {
                  // FIXME
                  self.tmpbuf.pop();
                  self.tmppos -= 1;
                  write!(stdout, "{} {}", CursorLeft(1), CursorLeft(1)).unwrap();
                } else if self.tmppos > 0 {
                  // FIXME
                  self.tmppos -= 1;
                  write!(stdout, "{}", CursorLeft(1)).unwrap();
                }
              }
              _ => {
                if self.tmppos == self.tmpbuf.len() && !self.tmpbuf.is_empty() {
                  // FIXME
                  self.tmpbuf.pop();
                  self.tmppos -= 1;
                  write!(stdout, "{} {}", CursorLeft(1), CursorLeft(1)).unwrap();
                } else if self.tmppos > 0 {
                  // FIXME
                  self.tmppos -= 1;
                  write!(stdout, "{}", CursorLeft(1)).unwrap();
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
              write!(stdout, "{}", CursorLeft(offset)).unwrap();
            }
          }
          Some(Ok(CTRL_E)) => {
            if self.tmppos < self.tmpbuf.len() {
              let offset = (self.tmpbuf.len() - self.tmppos) as u16;
              self.tmppos = self.tmpbuf.len();
              write!(stdout, "{}", CursorRight(offset)).unwrap();
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
                      write!(stdout, "{}", CursorRight(1)).unwrap();
                    }
                  }
                  Some(Ok(b'D')) => {
                    // Left.
                    if self.tmppos > 0 {
                      self.tmppos -= 1;
                      write!(stdout, "{}", CursorLeft(1)).unwrap();
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
    let stdout = stdout();
    let mut stdout = stdout.lock().into_raw_mode().unwrap();
    let mut stdin = async_stdin().bytes();
    self.term.mode = ReplIOMode::Blocked;
    self.term.query(&mut stdout);
    stdout.flush().unwrap();
    let refresh = Duration::from_millis(8);
    let mut base_ts = Instant::now();
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
              write!(&mut stdout, "{}\r", ClearCurrentLine).unwrap();
              commit = true;
            }
            self.term.mode = iomode;
          }
          Ok(ReplCtrl::Line(linemode, msg)) => {
            if !commit {
              write!(&mut stdout, "{}\r", ClearCurrentLine).unwrap();
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
          write!(&mut stdout, "{}\r", ClearCurrentLine).unwrap();
          commit = true;
        }
        match self.term.mode {
          /*ReplIOMode::Prompt => {
            self.term.answer(&mut stdout, ReplLineMode::Prompt, &line);
          }*/
          ReplIOMode::Command => {
            self.term.answer(&mut stdout, ReplLineMode::Command, &line);
          }
          _ => {}
        }
        if line.is_empty() {
          match self.term.mode {
            ReplIOMode::Prompt => {
              self.term.answer(&mut stdout, ReplLineMode::Prompt, &line);
            }
            _ => {}
          }
        } else {
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
      let next_ts = Instant::now();
      match refresh.checked_sub(next_ts.duration_since(base_ts)) {
        None => {}
        Some(delay) => sleep(delay),
      };
      base_ts = next_ts;
    }
    stdout.flush().unwrap();
  }
}

pub fn async_repl_terminal() -> (JoinHandle<()>, ReplInterpreter) {
  let (repl_term, ctrl_tq, line_rq) = ReplTerminal::start_async();
  let repl_intp = ReplInterpreter::new(ctrl_tq, line_rq);
  (repl_term, repl_intp)
}
