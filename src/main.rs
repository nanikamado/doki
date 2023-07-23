#![deny(clippy::allow_attributes_without_reason)]
#![deny(clippy::exit)]
#![deny(clippy::todo)]
#![deny(clippy::semicolon_outside_block)]

mod run_c;

use clap::{Parser, Subcommand};
use compiler::gen_c;
use std::fmt::{Debug, Display};
use std::fs;
use std::io::stderr;
use std::process::ExitCode;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[clap(arg_required_else_help(true))]
struct Args {
    /// Do not minimize types
    #[arg(long)]
    no_type_minimization: bool,
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    #[command(alias("r"))]
    Run {
        file: String,
        #[arg(long, short('C'))]
        clang_options: Option<String>,
    },
    /// Output generated c code
    #[command(alias("c"))]
    EmitC { file: String },
    /// Start the language server
    LanguageServer,
}

fn compile<'a>(
    src: &'a str,
    file_name: &str,
    no_type_minimization: bool,
) -> Result<impl Display + 'a, ()> {
    match compiler::parse(src) {
        Ok(ast) => Ok(gen_c(ast, !no_type_minimization)),
        Err(e) => {
            e.write(stderr(), file_name, src).unwrap();
            Err(())
        }
    }
}

fn main() -> ExitCode {
    #[cfg(feature = "backtrace-on-stack-overflow")]
    unsafe {
        backtrace_on_stack_overflow::enable()
    };
    let args = Args::parse();
    match args.command {
        Commands::Run {
            file,
            clang_options,
        } => {
            let src = fs::read_to_string(&file).unwrap();
            let r = compile(&src, &file, args.no_type_minimization);
            match r {
                Ok(c) => {
                    if let Ok(exit_status) =
                        run_c::run(c.to_string(), clang_options.as_deref().unwrap_or(""))
                    {
                        ExitCode::from(exit_status.code().unwrap() as u8)
                    } else {
                        ExitCode::FAILURE
                    }
                }
                Err(()) => ExitCode::FAILURE,
            }
        }
        Commands::EmitC { file } => {
            let src = fs::read_to_string(&file).unwrap();
            let r = compile(&src, &file, args.no_type_minimization);
            match r {
                Ok(c) => {
                    print!("{}", c);
                    ExitCode::SUCCESS
                }
                Err(()) => ExitCode::FAILURE,
            }
        }
        Commands::LanguageServer => {
            #[cfg(feature = "language-server")]
            {
                language_server::run(!args.no_type_minimization);
                ExitCode::SUCCESS
            }
            #[cfg(not(feature = "language-server"))]
            panic!()
        }
    }
}
