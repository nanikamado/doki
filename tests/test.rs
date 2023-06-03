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

fn test_test_fail(file_name: &str) -> assert_cmd::assert::Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/fail/", file_name].concat())
        .assert()
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
fn simple() {
    test_examples("simple.doki", "Hello, world.\n");
}

#[test]
fn closure() {
    test_examples("closure.doki", "a\n");
}

#[test]
fn r#match() {
    test_examples("match.doki", "True\n");
}

#[test]
fn fail_inexhaustive_match() {
    test_test_fail("inexhaustive_match.doki")
        .stderr("error: match is not exhaustive\n")
        .code(1);
}

#[test]
fn fn_union() {
    test_examples("fn_union.doki", "Hello\n");
}

#[test]
fn fail_not_a_function() {
    test_test_fail("not_a_function.doki")
        .stderr("error: not a function\n")
        .code(1);
}

#[test]
fn literal_pattern() {
    test_examples(
        "literal_pattern.doki",
        "is not a zero\nis not a zero\nis zero\n",
    );
}

#[test]
fn taut() {
    test_examples("taut.doki", "True\nTrue\nFalse\nTrue\n");
}
