#![deny(clippy::allow_attributes_without_reason)]
#![deny(clippy::exit)]
#![deny(clippy::todo)]
#![deny(clippy::semicolon_outside_block)]

mod run_c;

use clap::Parser;
use compiler::gen_c;
use std::fs;
use std::io::stderr;
use std::process::ExitCode;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[clap(arg_required_else_help(true))]
struct Args {
    #[arg(required(true), conflicts_with("language_server"))]
    file: Option<String>,
    /// Output generated c code
    #[arg(short('c'), long, conflicts_with("language_server"))]
    emit_c: bool,
    /// Do not minimize types
    #[arg(long)]
    no_type_minimization: bool,
    /// start language server
    #[arg(short('l'), long)]
    language_server: bool,
}

fn main() -> ExitCode {
    #[cfg(feature = "backtrace-on-stack-overflow")]
    unsafe {
        backtrace_on_stack_overflow::enable()
    };
    let args = Args::parse();
    if args.language_server {
        #[cfg(feature = "language-server")]
        {
            language_server::run(!args.no_type_minimization);
            ExitCode::SUCCESS
        }
        #[cfg(not(feature = "language-server"))]
        panic!()
    } else {
        let file_name = args.file.unwrap();
        let src = fs::read_to_string(&file_name).unwrap();
        match compiler::parse(&src) {
            Ok(ast) => {
                if args.emit_c {
                    print!("{}", gen_c(ast, !args.no_type_minimization));
                    ExitCode::SUCCESS
                } else if let Ok(exit_status) =
                    run_c::run(gen_c(ast, !args.no_type_minimization).to_string())
                {
                    ExitCode::from(exit_status.code().unwrap() as u8)
                } else {
                    ExitCode::FAILURE
                }
            }
            Err(e) => {
                e.write(stderr(), &file_name, &src).unwrap();
                ExitCode::FAILURE
            }
        }
    }
}
