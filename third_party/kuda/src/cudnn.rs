use crate::{Version};

use libloading::{Library, Symbol};

use std::io::{Error as IoError};

#[derive(Clone, Debug)]
pub struct Libcudnn<'lib> {
  pub cudnnGetVersion:          Symbol<'lib, unsafe extern "C" fn () -> usize>,
  pub cudnnGetCudartVersion:    Symbol<'lib, unsafe extern "C" fn () -> usize>,
}

impl<'lib> Libcudnn<'lib> {
  pub fn open(lib: &'lib Library) -> Result<Libcudnn<'lib>, IoError> {
    unsafe { Ok(Libcudnn{
      cudnnGetVersion:          lib.get(b"cudnnGetVersion")?,
      cudnnGetCudartVersion:    lib.get(b"cudnnGetCudartVersion")?,
    }) }
  }

  pub fn version(&self) -> Version {
    let raw_version: usize = unsafe { (self.cudnnGetVersion)() };
    let major = (raw_version / 1000) as u32;
    let minor = ((raw_version % 1000) / 100) as u32;
    let patch = (raw_version % 100) as u32;
    Version{major, minor, patch}
  }

  pub fn required_runtime_version(&self) -> Version {
    let raw_version: usize = unsafe { (self.cudnnGetCudartVersion)() };
    let major = (raw_version / 1000) as u32;
    let minor = ((raw_version % 1000) / 10) as u32;
    let patch = 0;
    Version{major, minor, patch}
  }
}
