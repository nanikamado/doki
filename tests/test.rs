use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use std::io::Write;
use std::process::{Command, Stdio};

const OPTIONS: &[&str] = &[
    "-q",
    "run",
    "--unique-tmp",
    "-C=-pedantic-errors -Wno-gnu-empty-struct -Wno-gnu-empty-initializer \
    -fsanitize=undefined,address -fno-sanitize-recover -ftrivial-auto-var-init=pattern",
];

const OPTIONS_WITH_BOEHM: &[&str] = &[
    "-q",
    "run",
    "--boehm",
    "--unique-tmp",
    // it seems like Boehm GC does not work well with `-fsanitize=address`
    "-C=-pedantic-errors -Wno-gnu-empty-struct -Wno-gnu-empty-initializer \
    -fsanitize=undefined -fno-sanitize-recover -ftrivial-auto-var-init=pattern",
];

const ENVS: [(&str, &str); 1] = [("ASAN_OPTIONS", "detect_leaks=0")];

fn test_example(file_name: &str, stdout: &str) {
    let run = |boehm| {
        let mut c = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
        if boehm {
            c.args(OPTIONS_WITH_BOEHM);
        } else {
            c.args(OPTIONS);
        }
        c.envs(ENVS)
            .arg(["examples/", file_name].concat())
            .assert()
            .stdout(stdout.to_string())
            .stderr("")
            .success();
    };
    run(false);
    run(true);
}

fn positive_test_with_stdin_with_gc_option(
    file_name: &str,
    stdin: &str,
    stdout: &str,
    boehm: bool,
) {
    let mut c = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
    if boehm {
        c.args(OPTIONS_WITH_BOEHM);
    } else {
        c.args(OPTIONS);
    }
    let mut c = c
        .envs(ENVS)
        .arg(["tests/positive/", file_name].concat())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(stdin.as_bytes()).unwrap();
    let output = c.wait_with_output().unwrap();
    assert_eq!(&output.stdout, stdout.as_bytes());
    assert!(output.stderr.is_empty());
}

fn positive_test_with_stdin(file_name: &str, stdin: &str, stdout: &str) {
    positive_test_with_stdin_with_gc_option(file_name, stdin, stdout, false);
    positive_test_with_stdin_with_gc_option(file_name, stdin, stdout, true);
}

fn positive_test(file_name: &str, stdout: &str) {
    positive_test_with_stdin(file_name, "", stdout)
}

fn negative_test(file_name: &str) -> assert_cmd::assert::Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .args(OPTIONS)
        .envs(ENVS)
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
        .stderr("error: match is not exhaustive\ntests/negative/inexhaustive_match.doki:10:20\n")
        .stdout("")
        .code(1);
}

#[test]
fn fn_union() {
    test_example("fn_union.doki", "Hello\n");
}

#[test]
fn fail_not_a_function() {
    negative_test("not_a_function.doki")
        .stderr("error: not a function\ntests/negative/not_a_function.doki:1:11\n")
        .stdout("")
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
    positive_test_with_stdin("fib.doki", "91\n", "> 4660046610375530309\n");
}

#[test]
fn fixed_point_prime() {
    positive_test_with_stdin("fixed_point_prime.doki", "2147483647\n", "True\n");
    positive_test_with_stdin("fixed_point_prime.doki", "68718821377\n", "False\n");
}

#[test]
fn fixed_point_lambda_prime() {
    positive_test_with_stdin("fixed_point_lambda_prime.doki", "100003\n", "True\n");
    positive_test_with_stdin_with_gc_option(
        "fixed_point_lambda_prime.doki",
        "2147483647\n",
        "True\n",
        false,
    );
    positive_test_with_stdin_with_gc_option(
        "fixed_point_lambda_prime.doki",
        "68718821377\n",
        "False\n",
        false,
    );
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

#[test]
fn mod2() {
    positive_test_with_stdin("mod2.doki", "111\n111\n", "> 1\n> 1\n");
}

#[test]
fn mod3() {
    positive_test_with_stdin("mod3.doki", "112\n112\n112", "> 1\n> 1\n> 1\n");
}

#[test]
fn diviter() {
    positive_test_with_stdin("larceny_bench/diviter.doki", "1000\n", "500\n");
}

#[test]
fn divrec() {
    positive_test_with_stdin("larceny_bench/divrec.doki", "1000\n", "500\n");
}

#[test]
fn tak() {
    positive_test_with_stdin("larceny_bench/tak.doki", "32\n16\n8\n", "9\n");
}

#[test]
fn takl() {
    positive_test_with_stdin("larceny_bench/takl.doki", "32\n16\n8\n", "9\n");
}

#[test]
fn type_caching() {
    positive_test_with_stdin("type_caching.doki", "", "");
}

#[test]
fn incomplete_parser() {
    positive_test_with_stdin("incomplete_parser.doki", "", "");
}

#[test]
fn expr_fib() {
    positive_test_with_stdin(
        "expr.doki",
        std::str::from_utf8(include_bytes!("positive/expr_inputs/fib.exp")).unwrap(),
        "4660046610375530309\n",
    );
}

#[test]
fn expr_prime() {
    positive_test_with_stdin(
        "expr.doki",
        std::str::from_utf8(include_bytes!("positive/expr_inputs/prime.exp")).unwrap(),
        "1\n",
    );
}

#[test]
fn prime() {
    positive_test_with_stdin("prime.doki", "2147483647", "True\n");
    positive_test_with_stdin("prime.doki", "68718821377", "False\n");
}

#[test]
fn prime_table_mut() {
    positive_test_with_stdin("prime_table_mut.doki", "524287", "True\n");
    positive_test_with_stdin("prime_table_mut.doki", "68718821377", "False\n");
}

#[test]
fn prime_table_global_mut() {
    positive_test_with_stdin("prime_table_global_mut.doki", "524287", "True\n");
    positive_test_with_stdin("prime_table_global_mut.doki", "68718821377", "False\n");
}

#[test]
fn prime_table() {
    positive_test_with_stdin("prime_table.doki", "524287", "True\n");
    positive_test_with_stdin("prime_table.doki", "68718821377", "False\n");
}

#[test]
fn prime_table_deletion() {
    positive_test_with_stdin("prime_table_deletion.doki", "524287", "True\n");
    positive_test_with_stdin("prime_table_deletion.doki", "68718821377", "False\n");
}

#[test]
fn boxed_ctx() {
    positive_test_with_stdin("boxed_ctx.doki", "", "10\n");
}

#[test]
fn global_order() {
    positive_test_with_stdin("global_order.doki", "", "306\n");
}

#[test]
fn global_order_negative() {
    negative_test("global_order.doki")
        .stderr("error: cycle detected when initializing global variables\n")
        .stdout("")
        .code(1);
}

#[test]
fn dummy_fn_in_dummy_fn() {
    positive_test_with_stdin("dummy_fn_in_dummy_fn.doki", "", "");
}

#[test]
fn dead_function() {
    negative_test("dead_function.doki")
        .stderr("error: not a function\ntests/negative/dead_function.doki:3:5\n")
        .stdout("")
        .code(1);
}

#[test]
fn toml() {
    positive_test_with_stdin(
        "toml/toml.doki",
        std::str::from_utf8(include_bytes!("positive/toml/test.toml")).unwrap(),
        "{\"value\": [{\"a\": [\"\\u00ABa\\u00BB\", 10], \
        \"actor\": {\"id\": \"\u{00ff} \u{d7ff} \u{e000} \u{ffff} \u{10000} \u{10ffff}\"}}]}\n",
    );
}

#[test]
fn global_mut() {
    positive_test("global_mut.doki", "2\n2\n");
}
