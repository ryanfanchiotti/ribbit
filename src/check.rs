use crate::var::*;
use crate::syntax::*;

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PropVar {
    name: String,
    offset: u128,
    value: bool
}

impl PropVar {
    pub fn new(name: String, offset: u128, value: bool) -> Self {
        PropVar {name, offset, value}
    }
}

// disjunction of each variable (or bit, here)
pub type Clause = Vec<PropVar>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    clauses: Vec<Clause>,
    vars: HashMap<String, BvVar>,
    // map from uninterpreted function name to (usages, signature in bits)
    fun_insts: HashMap<String, (Vec<String>, Vec<u128>)>,
}

impl State {
    pub fn new() -> Self {
        Self {clauses: vec![], vars: HashMap::new(), fun_insts: HashMap::new()}
    }
}

// implementation of Tseitin's transformation, where new variables are made for
// each expression (instead of using distributive laws, etc)

pub fn create_clauses(state: &mut State, prog: Program) {
    for expr in prog {
        create_clauses_expr(state, expr);
    }
}

pub fn create_clauses_expr(state: &mut State, expr: Expr) -> BvVar {
    match expr {
        Expr::Var(name) => lookup_var(state, name),
        Expr::List(lst) => create_clauses_list(state, lst),
        _ => panic!("bad expr in create_clause, likely lone num: {:?}\n", expr)
    }
}

pub fn create_clauses_list(state: &mut State, lst: Vec<Expr>) -> BvVar {
    match &lst[..] {
        // slightly hacky method of dealing with our primitives that need literal ints, to save space
        [Expr::Var(n), Expr::Int(num), Expr::Int(size)] if *n == "to-bv".to_string() =>
            create_clauses_to_bv(state, *num, *size),
        // const function -> normal variable
        [Expr::Var(n), Expr::Var(name), Expr::Int(size)] if *n == "declare-bv-fun".to_string() =>
            create_clauses_decl_var(state, name.clone(), *size),
        [Expr::Var(n), Expr::Var(name), rest @ ..] if *n == "declare-bv-fun".to_string() =>
            create_clauses_decl_fun(
                state,
                name.clone(),
                rest.into_iter()
                    .map(|e| get_int(e.clone(), "types in func decl"))
                    .collect()),
        [Expr::Var(n), rest @ ..] => {
            let bvs: Vec<BvVar> = rest.into_iter().map(|e| create_clauses_expr(state, e.clone())).collect();
            create_clauses_fun_bvs(state, n.clone(), bvs)
        },
        _ => panic!("unknown list expr: {:?}", lst)
    }
}

pub fn create_clauses_fun_bvs(state: &mut State, name: String, args: Vec<BvVar>) -> BvVar {
    // here, we expect all args to be proper bit-vector variables, since we create a new
    // variable at each stage
    let temp = BvVar::new_temp(Sort::Unit);
    temp
}

pub fn create_clauses_to_bv(state: &mut State, num: u128, size: u128) -> BvVar {
    let temp = BvVar::new_temp(Sort::BitVec(size));
    // for each bit in the vector, we push a clause (which must be true, in CNF) asserting
    // that it must be true if that bit is set and false otherwise
    for i in 0 .. size {
        state.clauses.push(
            vec![PropVar::new(temp.get_name().clone(), i, get_bit(num, i))]
        )
    }
    temp
}

pub fn create_clauses_decl_fun(state: &mut State, name: String, sig: Vec<u128>) -> BvVar {
    state.fun_insts.insert(name, (vec![], sig));
    BvVar::new_temp(Sort::Unit)
}

pub fn create_clauses_decl_var(state: &mut State, name: String, size: u128) -> BvVar {
    let temp = BvVar::new(name.clone(), Sort::Unit, true);
    state.vars.insert(name, temp);
    BvVar::new_temp(Sort::Unit)
}

fn lookup_var(state: &mut State, name: String) -> BvVar {
    match state.vars.get(&name) {
        Some(var) => var.clone(),
        _ => panic!("{} used before definition\n", name)
    }
}

fn get_int(expr: Expr, loc: &str) -> u128 {
    match expr {
        Expr::Int(n) => n,
        _ => panic!("{}: expected int\n", loc)
    }
}

// we know a built-in needs the same size operands, ensure this is the case
// and return the size if found, else panic
fn expect_all_bv_size(lst: &Vec<BvVar>) -> u128 {
    let mut cur_size: Option<u128> = None;
    let msg = "all arguments to built-ins must be the same size\n";

    for var in lst {
        match var.get_sort() {
            Sort::BitVec(n) => {
                if *cur_size.get_or_insert(*n) != *n {
                    panic!("{}", msg)
                }
            }
            _ => panic!("{}", msg)
        }
    }
    cur_size.expect(msg)
}

// similar to above, but with a specified list of sizes
fn expect_vec_bv_size(lst: &Vec<BvVar>, sizes: &Vec<u128>, loc: &str) {
    if lst.len() != sizes.len() {
        panic!("arguments to {} must be of sizes {:?}\n", loc, sizes)
    }

    for (bv, s) in lst.iter().zip(sizes.iter()) {
        match bv.get_sort() {
            Sort::BitVec(n) if n != s => 
                panic!("arguments to {} must be of sizes {:?}\n", loc, sizes),
            Sort::Unit =>
                panic!("arguments to {} must be of sizes {:?}\n", loc, sizes),
            _ => continue
        }
    }
}

fn get_bit(num: u128, n: u128) -> bool {
    ((num >> n) & 1) != 0
}