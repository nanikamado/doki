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

fn positive_with_gc_option(file_name: &str, stdin: &str, stdout: &str, boehm: bool) {
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

fn positive(file_name: &str, stdin: &str, stdout: &str) {
    positive_with_gc_option(file_name, stdin, stdout, false);
    positive_with_gc_option(file_name, stdin, stdout, true);
}

fn positive_without_stdin(file_name: &str, stdout: &str) {
    positive(file_name, "", stdout)
}

fn negative(file_name: &str) -> assert_cmd::assert::Assert {
    Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .args(OPTIONS)
        .envs(ENVS)
        .arg(["tests/negative/", file_name].concat())
        .assert()
}

#[test]
#[ignore]
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
#[ignore]
fn r#match() {
    test_example("match.doki", "True\n");
}

#[test]
#[ignore]
fn fail_inexhaustive_match() {
    negative("inexhaustive_match.doki")
        .stderr("error: match is not exhaustive\ntests/negative/inexhaustive_match.doki:10:20\n")
        .stdout("")
        .code(1);
}

#[test]
#[ignore]
fn fn_union() {
    test_example("fn_union.doki", "Hello\n");
}

#[test]
#[ignore]
fn fail_not_a_function() {
    negative("not_a_function.doki")
        .stderr("error: not a function\ntests/negative/not_a_function.doki:1:11\n")
        .stdout("")
        .code(1);
}

#[test]
#[ignore]
fn literal_pattern() {
    test_example(
        "literal_pattern.doki",
        "is not a zero\nis not a zero\nis zero\n",
    );
}

#[test]
#[ignore]
fn taut() {
    test_example("taut.doki", "True\nTrue\nFalse\nTrue\n");
}

#[test]
fn recursive_env() {
    positive_without_stdin("recursive_env.doki", "A\nA\n");
}

#[test]
fn mut_list() {
    positive_without_stdin("mut_list.doki", "10\n");
}

#[test]
#[ignore]
fn r#mut() {
    test_example("mut.doki", "0\n1\n2\n");
}

#[test]
#[ignore]
fn variable_scope() {
    positive_without_stdin("variable_scope.doki", "success\n");
}

#[test]
#[ignore]
fn global_variables() {
    test_example("global_variables.doki", "success\n");
}

#[test]
#[ignore]
fn fib() {
    positive("fib.doki", "91\n", "> 4660046610375530309\n");
}

#[test]
#[ignore]
fn fixed_point_prime() {
    positive("fixed_point_prime.doki", "2147483647\n", "True\n");
    positive("fixed_point_prime.doki", "68718821377\n", "False\n");
}

#[test]
fn fixed_point_lambda_prime() {
    positive("fixed_point_lambda_prime.doki", "100003\n", "True\n");
    positive_with_gc_option(
        "fixed_point_lambda_prime.doki",
        "2147483647\n",
        "True\n",
        false,
    );
    positive_with_gc_option(
        "fixed_point_lambda_prime.doki",
        "68718821377\n",
        "False\n",
        false,
    );
}

#[test]
fn diverging_struct() {
    positive("diverging_struct.doki", "3\n", "#\n#\n#\n");
}

#[test]
#[ignore]
fn memcpy() {
    positive("memcpy.doki", "", "Hello, world.\n");
}

#[test]
#[ignore]
fn oo() {
    positive("oo.doki", "1\n10\n100", "> > > 111\n");
}

#[test]
#[ignore]
fn mod2() {
    positive("mod2.doki", "111\n111\n", "> 1\n> 1\n");
}

#[test]
#[ignore]
fn mod3() {
    positive("mod3.doki", "112\n112\n112", "> 1\n> 1\n> 1\n");
}

#[test]
fn diviter() {
    positive("larceny_bench/diviter.doki", "1000\n", "500\n");
}

#[test]
#[ignore]
fn divrec() {
    positive("larceny_bench/divrec.doki", "1000\n", "500\n");
}

#[test]
#[ignore]
fn tak() {
    positive("larceny_bench/tak.doki", "32\n16\n8\n", "9\n");
}

#[test]
#[ignore]
fn takl() {
    positive("larceny_bench/takl.doki", "32\n16\n8\n", "9\n");
}

#[test]
#[ignore]
fn type_caching() {
    positive("type_caching.doki", "", "");
}

#[test]
#[ignore]
fn incomplete_parser() {
    positive("incomplete_parser.doki", "", "");
}

#[test]
#[ignore]
fn expr_fib() {
    positive(
        "expr.doki",
        std::str::from_utf8(include_bytes!("positive/expr_inputs/fib.exp")).unwrap(),
        "4660046610375530309\n",
    );
}

#[test]
fn expr_prime() {
    positive(
        "expr.doki",
        std::str::from_utf8(include_bytes!("positive/expr_inputs/prime.exp")).unwrap(),
        "1\n",
    );
}

#[test]
#[ignore]
fn prime() {
    positive("prime.doki", "2147483647", "True\n");
    positive("prime.doki", "68718821377", "False\n");
}

#[test]
#[ignore]
fn prime_table_mut() {
    positive("prime_table_mut.doki", "524287", "True\n");
    positive("prime_table_mut.doki", "68718821377", "False\n");
}

#[test]
#[ignore]
fn prime_table_global_mut() {
    positive("prime_table_global_mut.doki", "524287", "True\n");
    positive("prime_table_global_mut.doki", "68718821377", "False\n");
}

#[test]
#[ignore]
fn prime_table() {
    positive("prime_table.doki", "524287", "True\n");
    positive("prime_table.doki", "68718821377", "False\n");
}

#[test]
#[ignore]
fn prime_table_deletion() {
    positive("prime_table_deletion.doki", "524287", "True\n");
    positive("prime_table_deletion.doki", "68718821377", "False\n");
}

#[test]
#[ignore]
fn boxed_ctx() {
    positive("boxed_ctx.doki", "", "10\n");
}

#[test]
#[ignore]
fn global_order() {
    positive("global_order.doki", "", "306\n");
}

#[test]
#[ignore]
fn global_order_negative() {
    negative("global_order.doki")
        .stderr("error: cycle detected when initializing global variables\n")
        .stdout("")
        .code(1);
}

#[test]
#[ignore]
fn dummy_fn_in_dummy_fn() {
    positive("dummy_fn_in_dummy_fn.doki", "", "");
}

#[test]
#[ignore]
fn dead_function() {
    negative("dead_function.doki")
        .stderr("error: not a function\ntests/negative/dead_function.doki:3:5\n")
        .stdout("")
        .code(1);
}

#[test]
fn toml() {
    positive(
        "toml/toml.doki",
        std::str::from_utf8(include_bytes!("positive/toml/test.toml")).unwrap(),
        "{\"value\": [{\"a\": [\"\\u00ABa\\u00BB\", 10], \
        \"actor\": {\"id\": \"\u{00ff} \u{d7ff} \u{e000} \u{ffff} \u{10000} \u{10ffff}\"}}]}\n",
    );
}

#[test]
#[ignore]
fn global_mut() {
    positive_without_stdin("global_mut.doki", "2\n2\n");
}

#[test]
#[ignore]
fn nbody() {
    positive(
        "benchmarksgame/nbody.doki",
        "50000000",
        "-0.169075164\n-0.169059907\n",
    );
}
