use envy;

fn default_determinism() -> i32 {
  0
}

#[derive(Deserialize, Debug)]
pub struct Config {
  #[serde(default="default_determinism")]
  pub hebb_determinism: i32,
}

impl Default for Config {
  fn default() -> Config {
    match envy::from_env::<Config>() {
      Err(_) => panic!("failed to parse env vars"),
      Ok(cfg) => { println!("DEBUG: env cfg: {:?}", cfg); cfg }
    }
  }
}
