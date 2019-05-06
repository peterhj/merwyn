// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use envy;

/*fn default_repro_level() -> i32 {
  0
}*/

#[derive(Deserialize, Debug)]
pub struct GlobalConfig {
  /*#[serde(default="default_repro_level")]
  pub merwyn_rt_repro_level: i32,*/
}

impl Default for GlobalConfig {
  fn default() -> GlobalConfig {
    match envy::from_env::<GlobalConfig>() {
      Err(_) => panic!("failed to parse env vars"),
      Ok(cfg) => { println!("DEBUG: cfg: {:?}", cfg); cfg }
    }
  }
}
