// This file and its contents are licensed by their authors and copyright holders under the Apache
// License (Version 2.0), MIT license, or Mozilla Public License (Version 2.0), at your option, and
// may not be copied, modified, or distributed except according to those terms. For copies of these
// licenses and more information, see the COPYRIGHT file in this distribution's top-level directory.

/*
objrs is an open source project. The contents of all files within the objrs project are triple-licensed under the Apache License (Version 2.0), MIT license, or Mozilla Public License (Version 2.0), at your option.

See http://www.apache.org/licenses/LICENSE-2.0 or the LICENSE_APACHE file at the top-level directory of this distribution for a copy of the Apache License, Version 2.0.

See http://opensource.org/licenses/MIT or the LICENSE_MIT file at the top-level directory of this distribution for a copy of the MIT license.

See http://mozilla.org/MPL/2.0/ or the LICENSE_MPL file at the top-level directory of this distribution for a copy of the Mozilla Public License, Version 2.0.

You are free to fork the objrs project (under its license terms), though if you do so it is asked that you use a name distinct from objrs.
*/

#[cfg(feature = "xgpu")]
pub use self::metal::*;

#[cfg(feature = "xgpu")]
mod metal {

use objrs::{objrs, Auto, Id, Strong};
use objrs_frameworks_foundation::{NSError, NSString};

// TODO
#[objrs(protocol, name = "MTLDevice")]
//#[objrs(protocol, name = "MTLDevice", property(name: Option<Auto<NSString>>, readonly))]
#[link(name = "Metal", kind = "framework")]
pub trait MTLDevice {
  #[objrs(selector = "name")]
  fn name(&self) -> Option<Auto<NSString>>;
}

#[inline(always)]
pub fn MTLCreateSystemDefaultDevice() -> Option<Strong<Id<dyn MTLDevice>>> {
  #[link(name = "Metal", kind = "framework")]
  extern "C" {
    // TODO: file a feature request to get Option<T> whitelisted for FFI (where sizeof(T) == sizeof(Option<T>) and T is whitelisted for FFI).
    #[allow(improper_ctypes)]
    fn MTLCreateSystemDefaultDevice() -> Option<Strong<Id<dyn MTLDevice>>>;
  }
  return unsafe { MTLCreateSystemDefaultDevice() };
}

}
