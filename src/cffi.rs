// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ir2::{LBuilder};
use crate::lang::{HExpr, HLexer, HParser};
use crate::mach::{Machine};

//use std::os::raw::{c_char};
use std::ptr::{null};
use std::rc::{Rc};
use std::slice::{from_raw_parts};
use std::str::{from_utf8};

#[repr(C)]
pub struct CSourceRef {
  htree:    Rc<HExpr>,
}

#[no_mangle]
pub extern "C" fn merwyn_source_read(text_ptr: *const u8, text_len: usize) -> *const CSourceRef {
  // TODO: error handling.
  let text_buf = unsafe { from_raw_parts(text_ptr, text_len) };
  let text = match from_utf8(text_buf) {
    Err(_) => return null(),
    Ok(s) => s,
  };
  let lexer = HLexer::new(text);
  let parser = HParser::new(lexer);
  let htree = parser.parse();
  let src = Rc::new(CSourceRef{htree});
  Rc::into_raw(src)
}

#[no_mangle]
pub extern "C" fn merwyn_source_clone(src_ptr: *const CSourceRef) -> *const CSourceRef {
  if src_ptr.is_null() {
    // TODO: should panic.
    return null();
  }
  let src = unsafe { Rc::from_raw(src_ptr) };
  let src2 = src.clone();
  Rc::into_raw(src);
  Rc::into_raw(src2)
}

#[no_mangle]
pub extern "C" fn merwyn_source_reclaim(src_ptr: *const CSourceRef) {
  if src_ptr.is_null() {
    // TODO: should panic.
    return;
  }
  unsafe { Rc::from_raw(src_ptr) };
}

#[repr(C)]
pub struct CModuleRef {
  // TODO
}

#[repr(C)]
pub struct CCodegen {
  inner:    LBuilder,
}

#[no_mangle]
pub extern "C" fn merwyn_code_clone(src: *const CModuleRef) -> *const CModuleRef {
  unimplemented!();
}

#[no_mangle]
pub extern "C" fn merwyn_code_reclaim(src: *const CModuleRef) {
  unimplemented!();
}

#[no_mangle]
pub extern "C" fn merwyn_codegen_new() -> *mut CCodegen {
  let cg = Box::new(CCodegen{inner: LBuilder::default()});
  Box::into_raw(cg)
}

#[no_mangle]
pub extern "C" fn merwyn_codegen_drop(cg_ptr: *mut CCodegen) {
  if cg_ptr.is_null() {
    // TODO: should panic.
    return;
  }
  unsafe { Box::from_raw(cg_ptr) };
}

#[no_mangle]
pub extern "C" fn merwyn_codegen_compile(cg: *mut CCodegen, src: *const CSourceRef) -> CModuleRef {
  unimplemented!();
}

pub type MCValRef = CValRef;

#[repr(C)]
pub struct CValRef {
  // TODO
}

#[repr(C)]
pub struct CMachine {
  inner:    Machine,
}

#[no_mangle]
pub extern "C" fn merwyn_machine_new() -> *mut CMachine {
  let mach = Box::new(CMachine{inner: Machine::default()});
  Box::into_raw(mach)
}

#[no_mangle]
pub extern "C" fn merwyn_machine_drop(mach_ptr: *mut CMachine) {
  if mach_ptr.is_null() {
    // TODO: should panic.
    return;
  }
  unsafe { Box::from_raw(mach_ptr) };
}

#[no_mangle]
pub extern "C" fn merwyn_machine_step(mach_ptr: *mut CMachine) {
  if mach_ptr.is_null() {
    // TODO: should panic.
    return;
  }
  let mut mach = unsafe { Box::from_raw(mach_ptr) };
  mach.inner = mach.inner._step();
  assert_eq!(mach_ptr, Box::into_raw(mach));
}
