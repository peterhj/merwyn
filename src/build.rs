// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub static GIT_COMMIT_HASH: &'static str = include_str!(concat!(env!("OUT_DIR"), "/git_commit_hash"));
pub static GIT_MODIFIED: bool = include!(concat!(env!("OUT_DIR"), "/git_modified"));
