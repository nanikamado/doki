use std::fmt::Display;
use std::fs;
use std::io::{ErrorKind, Write};
use std::process::{self, ExitStatus, Stdio};
use tempfile::NamedTempFile;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum COptLevel {
    O0,
    #[default]
    O1,
    O2,
    O3,
    Ofast,
    Os,
    Oz,
}

impl COptLevel {
    pub fn as_str(self) -> &'static str {
        match self {
            COptLevel::O0 => "0",
            COptLevel::O1 => "1",
            COptLevel::O2 => "2",
            COptLevel::O3 => "3",
            COptLevel::Ofast => "fast",
            COptLevel::Os => "s",
            COptLevel::Oz => "z",
        }
    }
}

pub fn run(f: impl Display, opt_level: COptLevel) -> Result<ExitStatus, ()> {
    let tmp = NamedTempFile::new().unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    tmp.close().unwrap();
    match process::Command::new("clang")
        .args([
            "-std=c17",
            "-x",
            "c",
            &format!("-O{}", opt_level.as_str()),
            "-o",
            &tmp_path,
            "-",
        ])
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
