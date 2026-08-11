use goldentests::{TestConfig, TestResult};

#[test]
fn golden_tests() -> TestResult<()> {
    let mut config = TestConfig::new(env!("CARGO_BIN_EXE_hemlis"), "tests/golden", "-- + ")?;
    config.overwrite_tests = std::env::var_os("GOLDENTESTS_OVERWRITE").is_some();
    config.run_tests()
}
