// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[cfg(all(feature = "xgpu", target_os = "macos"))]
use crate::os_util::{MTLCreateSystemDefaultDevice, MTLDevice};

use std::fmt::{Write};

thread_local! {
  static TL_CPU_INFO: CpuInfo = CpuInfo::query();
  static TL_GPU_INFO: GpuInfo = GpuInfo::query();
}

#[cfg(target_arch = "x86_64")]
#[derive(Clone, Copy, Debug)]
pub struct CpuInfo {
  pub sse2:     bool,
  pub avx:      bool,
  pub avx2:     bool,
  pub avx512f:  bool,
  pub rdseed:   bool,
}

impl CpuInfo {
  pub fn cached() -> CpuInfo {
    TL_CPU_INFO.with(|x| *x)
  }
}

#[cfg(target_arch = "x86_64")]
impl CpuInfo {
  pub fn query() -> CpuInfo {
    CpuInfo{
      sse2:     is_x86_feature_detected!("sse2"),
      avx:      is_x86_feature_detected!("avx"),
      avx2:     is_x86_feature_detected!("avx2"),
      avx512f:  is_x86_feature_detected!("avx512f"),
      rdseed:   is_x86_feature_detected!("rdseed"),
    }
  }

  pub fn digest(&self) -> String {
    let mut any_feat = false;
    let mut buf: String = "x64".to_owned();
    if self.avx512f {
      if any_feat {
        write!(&mut buf, "+").unwrap();
      } else {
        write!(&mut buf, ":").unwrap();
      }
      write!(&mut buf, "avx512f").unwrap();
      any_feat = true;
    }
    if self.avx2 {
      if any_feat {
        write!(&mut buf, "+").unwrap();
      } else {
        write!(&mut buf, ":").unwrap();
      }
      write!(&mut buf, "avx2").unwrap();
      any_feat = true;
    } else if self.avx {
      if any_feat {
        write!(&mut buf, "+").unwrap();
      } else {
        write!(&mut buf, ":").unwrap();
      }
      write!(&mut buf, "avx").unwrap();
      any_feat = true;
    } else if self.sse2 {
      if any_feat {
        write!(&mut buf, "+").unwrap();
      } else {
        write!(&mut buf, ":").unwrap();
      }
      write!(&mut buf, "sse2").unwrap();
      any_feat = true;
    }
    if self.rdseed {
      if any_feat {
        write!(&mut buf, "+").unwrap();
      } else {
        write!(&mut buf, ":").unwrap();
      }
      write!(&mut buf, "rdseed").unwrap();
      any_feat = true;
    }
    buf
  }
}

#[cfg(not(feature = "xgpu"))]
#[derive(Clone, Debug)]
pub struct GpuInfo {
}

#[cfg(not(feature = "xgpu"))]
impl GpuInfo {
  pub fn cached() -> GpuInfo {
    GpuInfo{}
  }

  pub fn query() -> GpuInfo {
    GpuInfo{}
  }

  pub fn digest(&self) -> Option<String> {
    None
  }
}

#[cfg(all(feature = "xgpu", target_os = "macos"))]
#[derive(Clone, Debug)]
pub struct MetalGpuInfo {
  pub dev_name: String,
}

#[cfg(all(feature = "xgpu", target_os = "linux"))]
#[derive(Clone, Debug)]
pub struct CudaGpuInfo {
  pub driver:   kuda::Version,
  //pub runtime:  kuda::Version,
}

#[cfg(feature = "xgpu")]
#[derive(Clone, Debug)]
pub struct GpuInfo {
  #[cfg(target_os = "macos")]
  pub metal:    Option<String>,
  #[cfg(target_os = "linux")]
  pub cuda:     Option<kuda::Version>,
}

#[cfg(feature = "xgpu")]
impl GpuInfo {
  pub fn cached() -> GpuInfo {
    TL_GPU_INFO.with(|x| x.clone())
  }

  pub fn query() -> GpuInfo {
    GpuInfo{
      #[cfg(target_os = "macos")]
      metal:    {
        match MTLCreateSystemDefaultDevice() {
          None => None,
          Some(dev) => match dev.name() {
            None => None,
            Some(dev) => Some((*dev).as_ref().to_owned()),
          }
        }
      },
      #[cfg(target_os = "linux")]
      cuda:     {
        kuda::CUDA.as_ref().and_then(|cuda| cuda.version().ok())
      },
    }
  }

  pub fn digest(&self) -> Option<String> {
    #[cfg(target_os = "linux")]
    match self.cuda.as_ref() {
      Some(v) => {
        return Some(format!("cuda:{}.{}", v.major, v.minor));
      }
      None => {}
    }
    #[cfg(target_os = "macos")]
    match self.metal.as_ref() {
      Some(dev) => {
        if dev.contains("Intel") {
          return Some(format!("mtl:intel"));
        } else {
          return Some(format!("mtl:?"));
        }
      }
      None => {}
    }
    None
  }
}
