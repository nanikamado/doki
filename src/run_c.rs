use owo_colors::OwoColorize;
use std::fmt::Display;
use std::io::{ErrorKind, Write};
use std::os::unix::process::CommandExt;
use std::process::{self, ExitStatus, Stdio};

fn run_clang(f: impl Display, clang_options: &str, tmp_path: &str, boehm: bool) -> Result<(), ()> {
    let mut c = process::Command::new("clang");
    c.args(["-std=c17", "-x", "c", "-O2", "-o", &tmp_path, "-"]);
    if boehm {
        c.arg("-lgc");
    }
    match c
        .args(clang_options.split_ascii_whitespace())
        .stdin(Stdio::piped())
        .spawn()
    {
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
        Err(e) => {
            match e.kind() {
                ErrorKind::NotFound => eprintln!(
                    "clang command not found. \
                    You need to install clang."
                ),
                _ => eprintln!("failed to run clang"),
            };
            Err(())
        }
    }
}

pub fn run(f: impl Display, clang_options: &str, boehm: bool) -> Result<ExitStatus, ()> {
    let mut tmp = std::env::temp_dir();
    tmp.push("doki_a.out");
    let tmp_path = tmp.to_str().unwrap();
    run_clang(f, clang_options, tmp_path, boehm)?;
    process::Command::new(tmp_path).exec();
    Err(())
}

pub fn run_with_unique_tmp(
    f: impl Display,
    clang_options: &str,
    boehm: bool,
) -> Result<ExitStatus, ()> {
    let tmp = tempfile::Builder::new()
        .prefix(".doki_")
        .tempfile()
        .unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    run_clang(f, clang_options, &tmp_path, boehm)?;
    tmp.keep().unwrap();
    let e = process::Command::new(&tmp_path)
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    std::fs::remove_file(tmp_path).unwrap();
    Ok(e)
}
