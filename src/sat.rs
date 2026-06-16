// convert clauses to rustsat input, and create models

use crate::vars::*;
use crate::blast::*;

use std::collections::HashMap;

use rustsat::instances::{SatInstance};
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::TernaryVal;
use rustsat_kissat::Kissat;
use rustsat::types::Var as RSVar;
use rustsat::types::Lit as RSLit;
use rustsat::types::Clause as RSClause;


pub fn print_sat(clauses: Vec<Clause>, vars: Vec<BvVar>) {
    let mut instance: SatInstance = SatInstance::new();
    let mut solver = Kissat::default();

    let mut name_to_var: HashMap<(String, u128), RSVar> = HashMap::new();

    for var in &vars {
        for i in 0 .. get_bits(var.get_sort()) {
            let rs_var = instance.new_var();
            name_to_var.insert((var.owned_name(), i), rs_var);
        }
    }

    for clause in clauses {
        let lits = clause.iter().map(|pv| conv_propvar(&name_to_var, pv));
        let rs_clause = RSClause::from_iter(lits);
        solver.add_clause(rs_clause).expect("solver should take clause");
    }

    let sat_res = solver.solve().expect("solver should solve formula");

    match sat_res {
        SolverResult::Sat => {
            println!("sat");
            print_model(&vars, &solver, &name_to_var)
        },
        SolverResult::Interrupted => println!("unknown"),
        SolverResult::Unsat => println!("unsat")
    }
}

fn print_model<T: Solve> (vars: &Vec<BvVar>, solver: &T, name_to_var: &HashMap<(String, u128), RSVar>) {
    for var in vars {
        if !var.get_display() {
            continue
        }
        let bits = get_bits(var.get_sort());
        let mut uint_val: u128 = 0;
        let mut res_bits: Vec<bool> = Vec::new();
        for i in 0 .. bits {
            let key = (var.owned_name(), i);
            let res_var = name_to_var.get(&key).expect("var should be in map");
            let res_val = solver.var_val(*res_var).expect("solver should have value");
            let res_bit = match res_val {
                TernaryVal::True => true,
                TernaryVal::DontCare => true,
                TernaryVal::False => false
            };
            res_bits.push(res_bit);
            uint_val |= (res_bit as u128) << i;
        }
        
        res_bits.reverse();
        println!("------ {}: {} bits ------", var.owned_name(), bits);
        for bit in res_bits {
            print!("{}", bit as u8)
        }
        println!("\nunsigned int value: {}", uint_val);

    }
}

fn get_bits(sort: &Sort) -> u128 {
    match sort {
        Sort::Unit => 0,
        Sort::BitVec(n) => *n
    }
}

fn conv_propvar(name_to_var: &HashMap<(String, u128), RSVar>, pv: &PropVar) -> RSLit {
    let key = (pv.owned_name(), pv.get_offset());
    let var = name_to_var.get(&key).expect("var to be in map");

    var.lit(!pv.get_value())
}