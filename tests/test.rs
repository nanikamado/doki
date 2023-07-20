use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use std::io::Write;
use std::process::{Command, Stdio};

fn test_example(file_name: &str, stdout: &str) {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["examples/", file_name].concat())
        .assert()
        .stdout(stdout.to_string())
        .success();
}

fn positive_test_with_stdin(file_name: &str, stdin: &str, stdout: &str) {
    let mut c = Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/positive/", file_name].concat())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(stdin.as_bytes()).unwrap();
    let output = c.wait_with_output().unwrap();
    assert_eq!(&output.stdout, stdout.as_bytes());
}

fn positive_test(file_name: &str, stdout: &str) {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/positive/", file_name].concat())
        .assert()
        .stdout(stdout.to_string())
        .success();
}

fn negative_test(file_name: &str) -> assert_cmd::assert::Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(["tests/negative/", file_name].concat())
        .assert()
}

#[test]
fn bin_tree() {
    test_example("bin_tree.doki", "ok\n");
}

#[test]
fn red_black_tree() {
    test_example("red_black_tree.doki", "ok\n");
}

#[test]
fn helloworld() {
    test_example("helloworld.doki", "Hello, world.\n");
}

#[test]
fn simple() {
    test_example("simple.doki", "Hello, world.\n");
}

#[test]
fn closure() {
    test_example("closure.doki", "a\n");
}

#[test]
fn r#match() {
    test_example("match.doki", "True\n");
}

#[test]
fn fail_inexhaustive_match() {
    negative_test("inexhaustive_match.doki")
        .stderr("error: match is not exhaustive\n")
        .code(1);
}

#[test]
fn fn_union() {
    test_example("fn_union.doki", "Hello\n");
}

#[test]
fn fail_not_a_function() {
    negative_test("not_a_function.doki")
        .stderr("error: not a function\n")
        .code(1);
}

#[test]
fn literal_pattern() {
    test_example(
        "literal_pattern.doki",
        "is not a zero\nis not a zero\nis zero\n",
    );
}

#[test]
fn taut() {
    test_example("taut.doki", "True\nTrue\nFalse\nTrue\n");
}

#[test]
fn recursive_env() {
    positive_test("recursive_env.doki", "A\nA\n");
}

#[test]
fn mut_list() {
    positive_test("mut_list.doki", "10\n");
}

#[test]
fn r#mut() {
    test_example("mut.doki", "0\n1\n2\n");
}

#[test]
fn variable_scope() {
    positive_test("variable_scope.doki", "success\n");
}

#[test]
fn global_variables() {
    test_example("global_variables.doki", "success\n");
}

#[test]
fn fib() {
    positive_test_with_stdin("fib.doki", "92\n", "> 7540113804746346429\n");
}

#[test]
fn fixed_point_fib() {
    positive_test_with_stdin("fixed_point_fib.doki", "92\n", "> 7540113804746346429\n");
}

#[test]
fn fixed_point_fib_lambda() {
    positive_test_with_stdin("fixed_point_fib.doki", "92\n", "> 7540113804746346429\n");
}

#[test]
fn diverging_struct() {
    positive_test_with_stdin("diverging_struct.doki", "3\n", "#\n#\n#\n");
}

#[test]
fn memcpy() {
    positive_test_with_stdin("memcpy.doki", "", "Hello, world.\n");
}

#[test]
fn oo() {
    positive_test_with_stdin("oo.doki", "1\n10\n100", "> > > 111\n");
}
