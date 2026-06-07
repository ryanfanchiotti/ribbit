use crate::var::*;
use crate::syntax::*;

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bit {
    name: String,
    offset: u64
}

// disjunction of each variable (or bit, here)
pub type Clause = Vec<Bit>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    clauses: Vec<Clause>,
    vars: HashMap<String, BvVar>,
    // map from uninterpreted function name to (usages, signature in bits)
    fun_insts: HashMap<String, (Vec<String>, Vec<u64>)>,
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
    let match_var = |name: String, expr: Expr| {
        match expr {
            Expr::Var(n) if n == name => true,
            _ => false
        }
    };
    match &lst[..] {
        // slightly hacky method of dealing with our primitives that need literal ints, to save space
        [e1, e2, e3] if match_var("to-bv".to_string(), e1.clone()) => todo!(),
        [e1, rest @ ..] if match_var("declare-bv-fun".to_string(), e1.clone()) => todo!(),
        [Expr::Var(n), rest @ ..] => {
            let bvs: Vec<BvVar> = rest.into_iter().map(|e| create_clauses_expr(state, e.clone())).collect();
            create_clauses_fun_bvs(state, n.clone(), bvs)
        },
        _ => panic!("unknown list expr: {:?}", lst)
    }
}

pub fn create_clauses_fun_bvs(state: &mut State, name: String, args: Vec<BvVar>) -> BvVar {
    // todo!
    BvVar::new_temp(Sort::Unit)
}

pub fn create_clauses_to_bv(state: &mut State, num: i128, size: i128) -> BvVar {
    // todo!
    BvVar::new_temp(Sort::Unit)
}

pub fn create_clauses_decl(state: &mut State, name: String, sig: Vec<i128>) -> BvVar {
    // todo!
    BvVar::new_temp(Sort::Unit)
}

fn lookup_var(state: &mut State, name: String) -> BvVar {
    match state.vars.get(&name) {
        Some(var) => var.clone(),
        _ => panic!("{} used before definition\n", name)
    }
}

fn get_int(expr: Expr, loc: &str) -> i128 {
    match expr {
        Expr::Int(n) => n,
        _ => panic!("{}: expected int\n", loc)
    }
}

// we know a built-in needs the same size operands, ensure this is the case
// and return the size if found, else panic
fn all_bvs_size(lst: Vec<BvVar>) -> i128 {
    let mut cur_size: Option<i128> = None;
    let msg = "all arguments to built-ins must be the same size:\n";

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