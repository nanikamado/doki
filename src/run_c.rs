use itertools::{self, Itertools};
use owo_colors::OwoColorize;
use std::fmt::Display;
use std::io::Write;
use std::os::unix::process::CommandExt;
use std::process::{self, ExitStatus, Stdio};

fn run_cc(
    f: impl Display,
    cc: &str,
    cc_options: &str,
    tmp_path: &str,
    boehm: bool,
) -> Result<(), std::io::Error> {
    let mut c = process::Command::new(cc);
    c.args(["-std=c17", "-x", "c", "-O2", "-lm", "-o", tmp_path, "-"]);
    if boehm {
        c.arg("-lgc");
    }
    c.args(cc_options.split_ascii_whitespace());
    log::info!(
        "     {} {cc} {}",
        "Running".green().bold(),
        c.get_args()
            .format_with(" ", |a, f| f(&format_args!("{}", a.to_str().unwrap())))
    );
    match c.stdin(Stdio::piped()).spawn() {
        Ok(mut child) => {
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_fmt(format_args!("{f}"))
                .unwrap();
            assert!(child.wait().unwrap().success());
            log::info!("     {} {tmp_path}", "Running".green().bold());
            Ok(())
        }
        Err(e) => Err(e),
    }
}

pub fn run(
    f: impl Display,
    cc: &str,
    cc_options: &str,
    boehm: bool,
) -> Result<ExitStatus, std::io::Error> {
    let mut tmp = std::env::temp_dir();
    tmp.push("doki_a.out");
    let tmp_path = tmp.to_str().unwrap();
    run_cc(f, cc, cc_options, tmp_path, boehm)?;
    Err(process::Command::new(tmp_path).exec())
}

pub fn run_with_unique_tmp(
    f: impl Display,
    cc: &str,
    cc_options: &str,
    boehm: bool,
) -> Result<ExitStatus, std::io::Error> {
    let tmp = tempfile::Builder::new()
        .prefix(".doki_")
        .tempfile()
        .unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    run_cc(f, cc, cc_options, &tmp_path, boehm)?;
    tmp.keep().unwrap();
    let e = process::Command::new(&tmp_path)
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    std::fs::remove_file(tmp_path).unwrap();
    Ok(e)
}
