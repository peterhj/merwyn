use crate::{Version};

use libloading::{Library, Symbol};

use std::io::{Error as IoError};
use std::os::raw::{c_char, c_int};

#[derive(Clone, Debug)]
pub struct Libcudart<'lib> {
  pub cudaDriverGetVersion:     Symbol<'lib, unsafe extern "C" fn (*mut c_int) -> c_int>,
  pub cudaRuntimeGetVersion:    Symbol<'lib, unsafe extern "C" fn (*mut c_int) -> c_int>,
  pub cudaGetErrorString:       Symbol<'lib, unsafe extern "C" fn (c_int) -> *const c_char>,
}

impl<'lib> Libcudart<'lib> {
  pub fn open(lib: &'lib Library) -> Result<Libcudart<'lib>, IoError> {
    unsafe { Ok(Libcudart{
      cudaDriverGetVersion:     lib.get(b"cudaDriverGetVersion")?,
      cudaRuntimeGetVersion:    lib.get(b"cudaRuntimeGetVersion")?,
      cudaGetErrorString:       lib.get(b"cudaGetErrorString")?,
    }) }
  }

  pub fn version(&self) -> Result<Version, c_int> {
    let mut raw_version: c_int = 0;
    unsafe {
      match (self.cudaRuntimeGetVersion)(&mut raw_version as *mut c_int) {
        0 => {}
        e => return Err(e)
      }
    }
    let major = (raw_version / 1000) as u32;
    let minor = ((raw_version % 1000) / 10) as u32;
    let patch = 0;
    Ok(Version{major, minor, patch})
  }

  pub fn driver_supported_version(&self) -> Result<Option<Version>, c_int> {
    let mut raw_version: c_int = 0;
    unsafe {
      match (self.cudaDriverGetVersion)(&mut raw_version as *mut c_int) {
        0 => {}
        e => return Err(e)
      }
    }
    if raw_version == 0 {
      return Ok(None);
    }
    let major = (raw_version / 1000) as u32;
    let minor = ((raw_version % 1000) / 10) as u32;
    let patch = 0;
    Ok(Some(Version{major, minor, patch}))
  }
}
