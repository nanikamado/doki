use std::fmt::Display;
use std::fs;
use std::io::{ErrorKind, Write};
use std::process::{self, ExitStatus, Stdio};
use tempfile::NamedTempFile;

pub fn run(f: impl Display, clang_options: &str) -> Result<ExitStatus, ()> {
    let tmp = NamedTempFile::new().unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    tmp.close().unwrap();
    match process::Command::new("clang")
        .args(["-std=c17", "-x", "c", "-O1", "-o", &tmp_path, "-"])
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
            let e = process::Command::new(&tmp_path)
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
            fs::remove_file(tmp_path).unwrap();
            Ok(e)
        }
        Err(e) => {
            match e.kind() {
                ErrorKind::NotFound => eprintln!(
                    "clang command not found. \
                    You need to install clang."
                ),
                _ => eprintln!("failed to run clang"),
            };
            fs::remove_file(tmp_path).unwrap();
            Err(())
        }
    }
}
