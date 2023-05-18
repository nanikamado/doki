mod gen_c;
mod intrinsics;
mod parse;
mod run_c;

use clap::Parser;
use std::fs;
use std::process::exit;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// File name
    file: String,
    #[arg(short('c'), long)]
    /// Output generated c code
    emit_c: bool,
}

fn main() {
    let args = Args::parse();
    let s = fs::read_to_string(args.file).unwrap();
    let ast = parse::parse(&s);
    let c_src = gen_c::gen_c(ast);
    if args.emit_c {
        println!("{c_src}");
    } else if run_c::run(&c_src).is_err() {
        exit(1);
    }
}
