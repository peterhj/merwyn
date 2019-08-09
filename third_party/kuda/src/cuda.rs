use crate::{Version};

use libloading::{Library, Symbol};

use std::io::{Error as IoError};
use std::os::raw::{c_char, c_int};

#[derive(Clone, Debug)]
pub struct Libcuda<'lib> {
  pub cuDriverGetVersion:   Symbol<'lib, unsafe extern "C" fn (*mut c_int) -> c_int>,
  pub cuGetErrorName:       Symbol<'lib, unsafe extern "C" fn (c_int, *mut *const c_char) -> c_int>,
  pub cuGetErrorString:     Symbol<'lib, unsafe extern "C" fn (c_int, *mut *const c_char) -> c_int>,
  pub cuInit:               Symbol<'lib, unsafe extern "C" fn (c_int) -> c_int>,
  pub cuDeviceGetCount:     Symbol<'lib, unsafe extern "C" fn (*mut c_int) -> c_int>,
}

impl<'lib> Libcuda<'lib> {
  pub fn open(lib: &'lib Library) -> Result<Libcuda<'lib>, IoError> {
    unsafe { Ok(Libcuda{
      cuDriverGetVersion:   lib.get(b"cuDriverGetVersion")?,
      cuGetErrorName:       lib.get(b"cuGetErrorName")?,
      cuGetErrorString:     lib.get(b"cuGetErrorString")?,
      cuInit:               lib.get(b"cuInit")?,
      cuDeviceGetCount:     lib.get(b"cuDeviceGetCount")?,
    }) }
  }

  pub fn version(&self) -> Result<Version, c_int> {
    let mut raw_version: c_int = 0;
    unsafe {
      match (self.cuDriverGetVersion)(&mut raw_version as *mut c_int) {
        0 => {}
        e => return Err(e)
      }
    }
    let major = (raw_version / 1000) as u32;
    let minor = ((raw_version % 1000) / 10) as u32;
    let patch = 0;
    Ok(Version{major, minor, patch})
  }
}
