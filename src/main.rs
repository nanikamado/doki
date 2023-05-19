mod gen_c;
mod intrinsics;
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
    let s = fs::read_to_string(&args.file).unwrap();
    let ast = parser::parse(&s, &args.file);
    let c_src = gen_c::gen_c(ast);
    if args.emit_c {
        println!("{c_src}");
    } else if let Ok(exit_status) = run_c::run(&c_src) {
        exit(exit_status.code().unwrap());
    } else {
        exit(1);
    }
}
