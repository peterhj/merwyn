#![allow(non_snake_case)]

#[macro_use] extern crate lazy_static;
extern crate libloading;

use crate::cuda::{Libcuda};
use crate::cudart::{Libcudart};
use crate::cudnn::{Libcudnn};

use libloading::{Library};

use std::cmp::{Ordering};

lazy_static! {
  static ref _CUDA: Option<Library> = Library::new("libcuda.so").ok();
  pub static ref CUDA: Option<Libcuda<'static>> = {
    _CUDA.as_ref().and_then(|lib| Libcuda::open(lib).ok())
  };

  static ref _CUDART: Option<Library> = Library::new("libcudart.so").ok();
  pub static ref CUDART: Option<Libcudart<'static>> = {
    _CUDART.as_ref().and_then(|lib| Libcudart::open(lib).ok())
  };

  static ref _CUDNN: Option<Library> = Library::new("libcudnn.so").ok();
  pub static ref CUDNN: Option<Libcudnn<'static>> = {
    _CUDNN.as_ref().and_then(|lib| Libcudnn::open(lib).ok())
  };
}

pub mod cuda;
pub mod cudart;
pub mod cudnn;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Version {
  pub major:    u32,
  pub minor:    u32,
  pub patch:    u32,
}

impl PartialOrd for Version {
  fn partial_cmp(&self, other: &Version) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Version {
  fn cmp(&self, other: &Version) -> Ordering {
    match self.major.cmp(&other.major) {
      Ordering::Equal => {}
      Ordering::Greater => return Ordering::Greater,
      Ordering::Less => return Ordering::Less,
    }
    match self.minor.cmp(&other.minor) {
      Ordering::Equal => {}
      Ordering::Greater => return Ordering::Greater,
      Ordering::Less => return Ordering::Less,
    }
    match self.patch.cmp(&other.patch) {
      Ordering::Equal => {}
      Ordering::Greater => return Ordering::Greater,
      Ordering::Less => return Ordering::Less,
    }
    Ordering::Equal
  }
}
