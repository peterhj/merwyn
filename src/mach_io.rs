// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use byteorder::{ReadBytesExt, WriteBytesExt, LE};

#[cfg(target_os = "linux")]
use libc::{readlink};
#[cfg(target_os = "macos")]
use libc::{F_GETPATH, PATH_MAX, fcntl};
use std::collections::{VecDeque};
use std::ffi::{CStr, OsStr};
use std::io::{Read, Error as IoError, Cursor};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::os::unix::ffi::{OsStrExt};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::os::unix::io::{AsRawFd, RawFd};
use std::path::{PathBuf};

/* The rdrand-based entropy source is derived from nagisa's rdrand crate:

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
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#[cfg(target_arch = "x86_64")]
pub struct IOEntropySource {}

#[cfg(target_arch = "x86_64")]
fn cpuid_contains_rdrand() -> bool {
  let flag: u32 = 1 << 30;
  let res = unsafe { std::arch::x86_64::__cpuid(1) };
  (res.ecx & flag) == flag
}

#[cfg(target_arch = "x86_64")]
impl Default for IOEntropySource {
  fn default() -> IOEntropySource {
    if is_x86_feature_detected!("rdrand") || cpuid_contains_rdrand() {
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
      if unsafe { std::arch::x86_64::_rdrand64_step(&mut x) } != 0 {
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
    let mut cursor = 0;
    loop {
      if cursor == buf.len() {
        let entropy_action = match self.replay.actions.len() {
          0 => None,
          k => match &mut self.replay.actions[k - 1] {
            &mut IOReplayAction::ReadEntropy(ref mut ctr, ref mut entropy_buf) => {
              Some((ctr, entropy_buf))
            }
            _ => None,
          }
        };
        match entropy_action {
          Some((ctr, entropy_buf)) => {
            /*entropy_buf.extend_from_slice(buf);*/
            entropy_buf.extend(buf.iter());
            *ctr += 1;
          }
          None => {
            self.replay.actions.push_back(IOReplayAction::ReadEntropy(1, buf.to_owned().into()));
          }
        }
        return Ok(cursor);
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
    match self.replay.actions.front_mut() {
      None => panic!(),
      Some(&mut IOReplayAction::ReadEntropy(ref mut ctr, ref mut entropy_buf)) => {
        let buf_len = buf.len();
        let (front_buf, back_buf) = entropy_buf.as_slices();
        if buf_len <= front_buf.len() {
          buf.copy_from_slice(&front_buf[ .. buf_len]);
        } else {
          buf[ .. front_buf.len()].copy_from_slice(front_buf);
          buf[front_buf.len() .. ].copy_from_slice(&back_buf[ .. buf_len - front_buf.len()]);
        }
        entropy_buf.drain( .. buf_len);
        *ctr -= 1;
        if *ctr == 0 {
          self.replay.actions.pop_front();
        }
        Ok(buf_len)
      }
    }
  }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub struct UnsafeIOFile {
  fd:   RawFd,
  path: Option<PathBuf>,
}

impl UnsafeIOFile {
  #[cfg(target_os = "linux")]
  pub unsafe fn from_fd(fd: RawFd) -> UnsafeIOFile {
    let mut fd_path_buf = Vec::new();
    {
      let mut fd_path_writer = Cursor::new(&mut fd_path_buf);
      write!(&mut fd_path_writer, b"/proc/self/fd/{}\0", fd).unwrap();
    }
    let fd_path_cstr = CStr::from_bytes_with_nul(&fd_path_buf).unwrap();
    let mut path_buf: Vec<u8> = vec![0; 1024];
    let ret: isize = readlink(fd_path_cstr.as_ptr(), path_buf.as_mut_ptr(), path_buf.len());
    let path_len = match ret {
      -1 => {
        return UnsafeIOFile{fd, path: None};
      }
      n => n as usize,
    };
    assert!(path_len <= path_buf.len());
    if path_len == path_buf.len() {
      return UnsafeIOFile{fd, path: None};
    }
    let path = PathBuf::from(OsStr::from_bytes(&path_buf[ .. path_len]).to_os_string());
    UnsafeIOFile{fd, path: Some(path)}
  }

  #[cfg(target_os = "macos")]
  pub unsafe fn from_fd(fd: RawFd) -> UnsafeIOFile {
    let mut path_buf: Vec<u8> = vec![0; PATH_MAX as _];
    let ret = fcntl(fd, F_GETPATH, path_buf.as_mut_ptr());
    match ret {
      -1 => {
        return UnsafeIOFile{fd, path: None};
      }
      _ => {}
    }
    let path_len = {
      CStr::from_ptr(path_buf.as_ptr() as *const _).to_bytes().len()
    };
    assert!(path_len < PATH_MAX as _);
    let path = PathBuf::from(OsStr::from_bytes(&path_buf[ .. path_len]).to_os_string());
    UnsafeIOFile{fd, path: Some(path)}
  }
}

#[derive(Clone, Debug)]
pub enum IOReplayAction {
  ReadEntropy(usize, /*VecDeque<usize>,*/ VecDeque<u8>),
}

#[derive(Clone, Default, Debug)]
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
