use std::fs;
use std::io::ErrorKind;
use std::process::{self, ChildStdin, ExitStatus, Stdio};
use tempfile::NamedTempFile;

pub fn run(f: impl FnOnce(&mut ChildStdin)) -> Result<ExitStatus, ()> {
    let tmp = NamedTempFile::new().unwrap();
    let tmp_path = tmp.path().to_str().unwrap().to_string();
    tmp.close().unwrap();
    match process::Command::new("clang")
        .args(["-x", "c", "-o", &tmp_path, "-"])
        .stdin(Stdio::piped())
        .spawn()
    {
        Ok(mut child) => {
            f(child.stdin.as_mut().unwrap());
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
