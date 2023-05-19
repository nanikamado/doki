use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use std::process::Command;

fn test_examples(file_name: &str, stdout: &str) {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["examples/", file_name].concat())
        .assert()
        .stdout(stdout.to_string())
        .success();
}

fn test_test_fail(file_name: &str) {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/fail/", file_name].concat())
        .assert()
        .code(1);
}

#[test]
fn bin_tree() {
    test_examples("bin_tree.doki", "ok\n");
}

#[test]
fn red_black_tree() {
    test_examples("red_black_tree.doki", "ok\n");
}

#[test]
fn helloworld() {
    test_examples("helloworld.doki", "Hello, world.\n");
}

#[test]
fn r#match() {
    test_examples("match.doki", "True\n");
}

#[test]
fn fail_inexhaustive_match() {
    test_test_fail("inexhaustive_match.doki");
}
