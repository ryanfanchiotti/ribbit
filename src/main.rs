mod syntax;
use std::env::{args};
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = args().collect();
    if args.len() < 2 {
        println!("usage: {} [FILE]\n", args[0]);
        return ExitCode::FAILURE;
    }

    let file = &args[1];
    let input = fs::read_to_string(file).expect("file to exist");

    match syntax::parse_program(input.as_str()) {
        Ok((_, program)) => {
            println!("program:\n{:?}", program);
            return ExitCode::SUCCESS;
        }
        Err(e) => {
            println!("parse error:\n{:?}", e);
            return ExitCode::FAILURE;
        }
    }
}
