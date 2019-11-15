// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fs;
use std::io::{BufRead, Write, Cursor};
use std::path::{PathBuf};
use std::process::{Command};

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-changed=.git/logs/HEAD");
  let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    //.canonicalize().unwrap();
  eprintln!("TRACE: cargo manifest dir: {:?}", manifest_dir);
  let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    //.canonicalize().unwrap();
  eprintln!("TRACE: out dir: {:?}", out_dir);
  let out = Command::new("git")
    .current_dir(&manifest_dir)
    .arg("log")
    .arg("-n").arg("1")
    .arg("--format=%H")
    .output().unwrap();
  if !out.status.success() {
    panic!("`git log` failed with exit status: {:?}", out.status);
  }
  match Cursor::new(out.stdout).lines().next() {
    None => panic!("`git log` did not print the commit hash"),
    Some(line) => {
      let line = line.unwrap();
      let mut file = fs::File::create(out_dir.join("git_commit_hash")).unwrap();
      write!(&mut file, "{}", line).unwrap();
    }
  }
  let mut changed = false;
  let mut untracked = false;
  let out = Command::new("git")
    .current_dir(&manifest_dir)
    .arg("diff")
    .arg("--stat")
    .output().unwrap();
  if !out.status.success() {
    panic!("`git diff` failed with exit status: {:?}", out.status);
  }
  match Cursor::new(out.stdout).lines().next() {
    None => {}
    Some(_) => {
      changed = true;
    }
  }
  let out = Command::new("git")
    .current_dir(&manifest_dir)
    .arg("status")
    .arg("--short")
    .output().unwrap();
  if !out.status.success() {
    panic!("`git status` failed with exit status: {:?}", out.status);
  }
  match Cursor::new(out.stdout).lines().next() {
    None => {}
    Some(_) => {
      untracked = true;
    }
  }
  let mut modified_file = fs::File::create(out_dir.join("git_modified")).unwrap();
  if changed || untracked {
    write!(&mut modified_file, "true").unwrap();
  } else {
    write!(&mut modified_file, "false").unwrap();
  }
}
