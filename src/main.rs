mod gen_c;
mod intrinsics;
mod parse;
mod run_c;

use clap::Parser;
use std::fs;
use std::process::exit;

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File name
    file: String,
}

fn main() {
    let args = Args::parse();
    let s = fs::read_to_string(args.file).unwrap();
    let ast = parse::parse(&s);
    let c_src = gen_c::gen_c(ast);
    if run_c::run(&c_src).is_err() {
        exit(1);
    }
}
