use owo_colors::OwoColorize;
use std::fmt::Display;
use std::io::{ErrorKind, Write};
use std::os::unix::process::CommandExt;
use std::process::{self, ExitStatus, Stdio};

pub fn run(f: impl Display, clang_options: &str) -> Result<ExitStatus, ()> {
    let mut tmp = std::env::temp_dir();
    tmp.push("doki_a.out");
    let tmp_path = tmp.to_str().unwrap();
    match process::Command::new("clang")
        .args(["-std=c17", "-x", "c", "-O2", "-o", &tmp_path, "-"])
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
            process::Command::new(tmp_path).exec();
            Err(())
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
