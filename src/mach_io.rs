// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::io_util::{WriteBytesExt, LE};

#[cfg(target_os = "linux")]
use libc::{readlink};
#[cfg(target_os = "macos")]
use libc::{F_GETPATH, PATH_MAX, fcntl};
use std::collections::{VecDeque};
use std::ffi::{CStr, OsStr, OsString};
use std::fs::{File};
use std::io::{Read, Write, Error as IoError, Cursor};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::os::unix::ffi::{OsStrExt};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::os::unix::io::{FromRawFd, IntoRawFd, RawFd};
use std::path::{PathBuf, Path};

/* The rdseed-based entropy source is derived from nagisa's rdrand crate:

Copyright (c) 2014, Simonas Kazlauskas <rdrand@kazlauskas.me>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

#[cfg(target_arch = "x86_64")]
pub struct IOEntropySource {}

#[cfg(target_arch = "x86_64")]
impl Default for IOEntropySource {
  fn default() -> IOEntropySource {
    if is_x86_feature_detected!("rdseed") {
      IOEntropySource{}
    } else {
      panic!();
    }
  }
}

#[cfg(target_arch = "x86_64")]
impl IOEntropySource {
  #[inline]
  pub fn retry_next_u64(&mut self, max_iters: usize) -> Option<u64> {
    let mut x: u64 = 0;
    for _ in 0 .. max_iters {
      if unsafe { std::arch::x86_64::_rdseed64_step(&mut x) } != 0 {
        return Some(x);
      }
    }
    None
  }
}

pub struct IOEntropyStream<'r> {
  replay:   &'r mut MachIOReplayBuffer,
  source:   IOEntropySource,
  tmp_buf:  [u8; 8],
  tmp_ctr:  usize,
}

impl<'r> IOEntropyStream<'r> {
  pub fn open(state: &'r mut MachIOState) -> IOEntropyStream<'r> {
    IOEntropyStream{
      replay:   &mut state.replay,
      source:   IOEntropySource::default(),
      tmp_buf:  [0; 8],
      tmp_ctr:  8,
    }
  }
}

impl<'r> Drop for IOEntropyStream<'r> {
  fn drop(&mut self) {
    // TODO
    /*zero_buf(&mut self.tmp_buf);*/
    let mut tmp_buf = Cursor::new(&mut self.tmp_buf as &mut [u8]);
    match tmp_buf.write_u64::<LE>(0) {
      Err(_) => unreachable!(),
      Ok(_) => {}
    }
  }
}

impl<'r> Read for IOEntropyStream<'r> {
  fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError> {
    match self.read_exact(buf) {
      Err(e) => Err(e),
      Ok(()) => Ok(buf.len())
    }
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), IoError> {
    let mut cursor = 0;
    loop {
      if cursor == buf.len() {
        let entropy_action = match self.replay.actions.len() {
          0 => None,
          k => match &mut self.replay.actions[k - 1] {
            &mut IOReplayAction::ReadEntropy(ref mut ctr, ref mut read_cts, ref mut entropy_buf) => {
              Some((ctr, read_cts, entropy_buf))
            }
            _ => None,
          }
        };
        match entropy_action {
          Some((ctr, read_cts, entropy_buf)) => {
            *ctr += 1;
            read_cts.push_back(buf.len() as _);
            /*entropy_buf.extend_from_slice(buf);*/
            entropy_buf.extend(buf.iter());
          }
          None => {
            let mut read_cts = VecDeque::new();
            read_cts.push_back(buf.len() as _);
            self.replay.actions.push_back(IOReplayAction::ReadEntropy(1, read_cts, buf.to_owned().into()));
          }
        }
        return Ok(());
      }
      if self.tmp_ctr == 8 {
        let u = match self.source.retry_next_u64(127) {
          None => continue,
          Some(u) => u,
        };
        let mut tmp_buf = Cursor::new(&mut self.tmp_buf as &mut [u8]);
        match tmp_buf.write_u64::<LE>(u) {
          Err(_) => unreachable!(),
          Ok(_) => {}
        }
        self.tmp_ctr = 0;
      }
      buf[cursor] = self.tmp_buf[self.tmp_ctr];
      cursor += 1;
      self.tmp_ctr += 1;
    }
  }
}

pub struct IOEntropyReplay<'r> {
  replay:   &'r mut MachIOReplayBuffer,
}

impl<'r> IOEntropyReplay<'r> {
  pub fn open(state: &'r mut MachIOState) -> IOEntropyReplay<'r> {
    IOEntropyReplay{
      replay:   &mut state.replay,
    }
  }
}

impl<'r> Read for IOEntropyReplay<'r> {
  fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError> {
    match self.read_exact(buf) {
      Err(e) => Err(e),
      Ok(()) => Ok(buf.len())
    }
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), IoError> {
    match self.replay.actions.front_mut() {
      Some(&mut IOReplayAction::ReadEntropy(ref mut ctr, ref mut read_cts, ref mut entropy_buf)) => {
        assert!(*ctr >= 1);
        let buf_len = buf.len();
        match read_cts.front() {
          None => panic!(),
          Some(&read_ct) => {
            assert_eq!(buf_len as u64, read_ct);
          }
        }
        assert!(buf_len <= entropy_buf.len());
        let (front_buf, back_buf) = entropy_buf.as_slices();
        if buf_len <= front_buf.len() {
          buf.copy_from_slice(&front_buf[ .. buf_len]);
        } else {
          buf[ .. front_buf.len()].copy_from_slice(front_buf);
          buf[front_buf.len() .. ].copy_from_slice(&back_buf[ .. buf_len - front_buf.len()]);
        }
        *ctr -= 1;
        read_cts.pop_front();
        entropy_buf.drain( .. buf_len);
        if *ctr == 0 {
          self.replay.actions.pop_front();
        }
        Ok(())
      }
      Some(_) | None => panic!(),
    }
  }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub struct NondetIOFileStream<'r> {
  replay:   &'r mut MachIOReplayBuffer,
  fd:       RawFd,
  path:     Option<PathBuf>,
  file_len: Option<u64>,
  flag:     bool,
}

impl<'r> NondetIOFileStream<'r> {
  #[cfg(target_os = "linux")]
  pub unsafe fn from_fd(state: &'r mut MachIOState, fd: RawFd) -> NondetIOFileStream<'r> {
    let mut fd_path_buf = Vec::new();
    {
      let mut fd_path_writer = Cursor::new(&mut fd_path_buf);
      write!(&mut fd_path_writer, b"/proc/self/fd/{}\0", fd).unwrap();
    }
    let fd_path_cstr = CStr::from_bytes_with_nul(&fd_path_buf).unwrap();
    let path = {
      let mut path_buf: Vec<u8> = vec![0; 1024];
      let ret: isize = readlink(fd_path_cstr.as_ptr(), path_buf.as_mut_ptr(), path_buf.len());
      match ret {
        -1 => None,
        n => {
          let path_len = n as usize;
          assert!(path_len <= path_buf.len());
          if path_len == path_buf.len() {
            None
          } else {
            Some(OsStr::from_bytes(&path_buf[ .. path_len]).to_os_string())
          }
        }
      }
    };
    let f = unsafe { File::from_raw_fd(fd) };
    let file_len = match f.metadata() {
      Err(_) => None,
      Ok(meta) => meta.len(),
    };
    let fd = f.into_raw_fd();
    state.replay.actions.push_back(IOReplayAction::NondetFromFd(fd, path.clone(), file_len));
    let path = path.map(|s| PathBuf::from(s));
    NondetIOFileStream{
      replay:   &mut state.replay,
      fd,
      path,
      file_len,
      flag:     false
    }
  }

  #[cfg(target_os = "macos")]
  pub unsafe fn from_fd(state: &'r mut MachIOState, fd: RawFd) -> NondetIOFileStream<'r> {
    let mut path_buf: Vec<u8> = vec![0; PATH_MAX as _];
    let ret = fcntl(fd, F_GETPATH, path_buf.as_mut_ptr());
    let path = match ret {
      -1 => None,
      _ => {
        let path_len = {
          CStr::from_ptr(path_buf.as_ptr() as *const _).to_bytes().len()
        };
        assert!(path_len < PATH_MAX as _);
        Some(OsStr::from_bytes(&path_buf[ .. path_len]).to_os_string())
      }
    };
    let f = unsafe { File::from_raw_fd(fd) };
    let file_len = match f.metadata() {
      Err(_) => None,
      Ok(meta) => Some(meta.len()),
    };
    let fd = f.into_raw_fd();
    state.replay.actions.push_back(IOReplayAction::NondetFromFd(fd, path.clone(), file_len));
    let path = path.map(|s| PathBuf::from(s));
    NondetIOFileStream{
      replay:   &mut state.replay,
      fd,
      path,
      file_len,
      flag:     false
    }
  }

  pub fn open<P: AsRef<Path>>(state: &'r mut MachIOState, path: P) -> Option<NondetIOFileStream<'r>> {
    let path = path.as_ref();
    let path = path.to_owned();
    let f = match File::open(&path) {
      Err(_) => {
        state.replay.actions.push_back(IOReplayAction::NondetOpenPath(path.into(), None, None));
        return None;
      }
      Ok(f) => f,
    };
    let file_len = match f.metadata() {
      Err(_) => None,
      Ok(meta) => Some(meta.len()),
    };
    let fd = f.into_raw_fd();
    state.replay.actions.push_back(IOReplayAction::NondetOpenPath(path.clone().into(), Some(fd), file_len));
    Some(NondetIOFileStream{
      replay:   &mut state.replay,
      fd,
      path:     Some(path),
      file_len,
      flag:     false
    })
  }
}

impl<'r> Drop for NondetIOFileStream<'r> {
  fn drop(&mut self) {
    unsafe { File::from_raw_fd(self.fd) };
  }
}

impl<'r> Read for NondetIOFileStream<'r> {
  fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError> {
    match self.read_exact(buf) {
      Err(e) => Err(e),
      Ok(()) => Ok(buf.len())
    }
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), IoError> {
    // FIXME: if flagged, should return an io::Error.
    assert!(!self.flag);
    let mut f = unsafe { File::from_raw_fd(self.fd) };
    match f.read_exact(buf) {
      Err(e) => {
        assert_eq!(self.fd, f.into_raw_fd());
        self.flag = true;
        self.replay.actions.push_back(IOReplayAction::NondetReadFile(self.fd, buf.len() as _, None));
        return Err(e);
      }
      Ok(()) => {}
    }
    assert_eq!(self.fd, f.into_raw_fd());
    self.replay.actions.push_back(IOReplayAction::NondetReadFile(self.fd, buf.len() as _, Some(self.fd)));
    Ok(())
  }
}

pub enum IOReplayAction {
  ReadEntropy(u64, VecDeque<u64>, VecDeque<u8>),
  //ReadEntropy(u64, VecDeque<u8>),
  NondetFromFd(i32, Option<OsString>, Option<u64>),
  NondetOpenPath(OsString, Option<i32>, Option<u64>),
  NondetReadFile(i32, u64, Option<i32>),
  //NondetMmapFile(i32, u64, u64, Option<i32>),
}

#[derive(Default)]
pub struct MachIOReplayBuffer {
  actions:  VecDeque<IOReplayAction>,
}

pub struct MachIOState {
  replay:   MachIOReplayBuffer,
}

impl MachIOState {
  pub fn new() -> MachIOState {
    MachIOState{
      replay:   MachIOReplayBuffer::default(),
    }
  }

  pub fn _replay(&self) -> &MachIOReplayBuffer {
    &self.replay
  }
}
