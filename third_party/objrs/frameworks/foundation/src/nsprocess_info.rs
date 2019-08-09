// This file and its contents are licensed by their authors and copyright holders under the Apache
// License (Version 2.0), MIT license, or Mozilla Public License (Version 2.0), at your option, and
// may not be copied, modified, or distributed except according to those terms. For copies of these
// licenses and more information, see the COPYRIGHT file in this distribution's top-level directory.

use crate::nsobject::NSObject;
use crate::nsstring::NSString;
use objrs::objrs;

#[objrs(class, super = NSObject)]
#[link(name = "Foundation", kind = "framework")]
pub struct NSProcessInfo;

#[objrs(impl)]
#[link(name = "Foundation", kind = "framework")]
impl NSProcessInfo {
  // TODO: this is really an autoreleased value.
  #[objrs(selector = "processInfo")]
  pub fn process_info() -> &'static NSProcessInfo {}

  #[objrs(selector = "processName")]
  pub fn process_name(&self) -> &NSString {}
}
