mod syntax;
mod blast;
mod vars;
mod sat;

use std::env::{args};
use std::fs;
use std::process::ExitCode;

use crate::blast::*;
use crate::sat::*;

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
            // println!("program:\n{:?}", program);
            let (clauses, vars) = make_clauses(program);
            // println!("clauses:\n{:?}", clauses);
            // println!("vars:\n{:?}", vars);
            print_sat(clauses, vars);
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("parse error:\n{:?}", e);
            ExitCode::FAILURE
        }
    }
}
