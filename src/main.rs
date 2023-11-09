#![deny(clippy::allow_attributes_without_reason)]
#![deny(clippy::exit)]
#![deny(clippy::todo)]
#![deny(clippy::semicolon_outside_block)]

mod run_c;

use clap::{Parser, Subcommand};
use compiler::gen_c;
use log::LevelFilter;
use rustc_hash::FxHashMap;
use simplelog::{ColorChoice, ConfigBuilder, TermLogger, TerminalMode};
use std::fmt::{Debug, Display};
use std::io::stderr;
use std::process::ExitCode;
use typed_arena::Arena;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[clap(arg_required_else_help(true))]
struct Args {
    /// Do not minimize types
    #[arg(long, global = true)]
    no_type_minimization: bool,
    #[arg(long, short('q'), global = true)]
    quiet: bool,
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
        #[arg(long)]
        unique_tmp: bool,
        #[arg(long)]
        backtrace: bool,
    },
    /// Output generated c code
    #[command(alias("c"))]
    EmitC {
        file: String,
        #[arg(long)]
        backtrace: bool,
    },
    /// Start the language server
    LanguageServer,
}

fn compile<'a>(
    file_name: &'a str,
    no_type_minimization: bool,
    backtrace: bool,
    src_files: &mut FxHashMap<&'a str, &'a str>,
    arena: &'a mut Arena<String>,
) -> Result<impl Display + 'a, ()> {
    match compiler::parse(file_name, src_files, arena) {
        Ok(ast) => Ok(gen_c(ast, src_files, !no_type_minimization, backtrace)),
        Err((file_name, e)) => {
            e.write(stderr(), file_name, src_files[file_name]).unwrap();
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
    TermLogger::init(
        if args.quiet {
            LevelFilter::Off
        } else {
            LevelFilter::Trace
        },
        ConfigBuilder::new()
            .set_location_level(LevelFilter::Error)
            .set_time_level(LevelFilter::Off)
            .set_thread_level(LevelFilter::Off)
            .set_target_level(LevelFilter::Off)
            .set_location_level(LevelFilter::Debug)
            .set_max_level(LevelFilter::Debug)
            .build(),
        TerminalMode::Stderr,
        ColorChoice::Auto,
    )
    .unwrap();
    let mut arena = Arena::new();
    let mut src_files = FxHashMap::default();
    match args.command {
        Commands::Run {
            file,
            clang_options,
            unique_tmp,
            backtrace,
        } => {
            let r = compile(
                &file,
                args.no_type_minimization,
                backtrace,
                &mut src_files,
                &mut arena,
            );
            match r {
                Ok(c) => {
                    if let Ok(exit_status) = if unique_tmp {
                        run_c::run_with_unique_tmp(
                            c.to_string(),
                            clang_options.as_deref().unwrap_or(""),
                        )
                    } else {
                        run_c::run(c.to_string(), clang_options.as_deref().unwrap_or(""))
                    } {
                        ExitCode::from(exit_status.code().unwrap() as u8)
                    } else {
                        ExitCode::FAILURE
                    }
                }
                Err(()) => ExitCode::FAILURE,
            }
        }
        Commands::EmitC { file, backtrace } => {
            let r = compile(
                &file,
                args.no_type_minimization,
                backtrace,
                &mut src_files,
                &mut arena,
            );
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
