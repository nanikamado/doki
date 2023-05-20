mod run_c;

use clap::Parser;
use compiler::gen_c;
use std::fs;
use std::io::{stderr, stdout};
use std::process::exit;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[clap(arg_required_else_help(true))]
struct Args {
    #[arg(required_unless_present_any(["language_server"]))]
    file: Option<String>,
    /// Output generated c code
    #[arg(short('c'), long)]
    emit_c: bool,
    /// start language server
    #[arg(short('l'), long, exclusive(true))]
    language_server: bool,
}

fn main() {
    let args = Args::parse();
    if args.language_server {
        #[cfg(feature = "language-server")]
        language_server::run();
        #[cfg(not(feature = "language-server"))]
        panic!();
    } else {
        let file_name = args.file.unwrap();
        let src = fs::read_to_string(&file_name).unwrap();
        match compiler::parse(&src) {
            Ok(ast) => {
                if args.emit_c {
                    gen_c(ast, &mut stdout());
                } else if let Ok(exit_status) = run_c::run(|w| gen_c(ast, w)) {
                    exit(exit_status.code().unwrap());
                } else {
                    exit(1);
                }
            }
            Err(e) => {
                e.write(stderr(), &file_name, &src).unwrap();
                exit(1);
            }
        }
    }
}
