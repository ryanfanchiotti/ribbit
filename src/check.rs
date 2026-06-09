use crate::var::*;
use crate::syntax::*;

use std::collections::HashMap;
use std::fmt;

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

    pub fn mk_bv(&mut self, name: String, sort: Sort, display: bool) -> BvVar {
        let bv = BvVar::new(name.clone(), sort, display);
        self.vars.insert(name, bv.clone());
        bv
    }

    pub fn mk_temp_bv(&mut self, sort: Sort) -> BvVar {
        let bv = BvVar::new_temp(sort);
        self.vars.insert(bv.get_name().clone(), bv.clone());
        bv
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "clauses:\n{:?}\nvars:\n{:?}\nfun_insts:\n{:?}", 
            self.clauses, self.vars, self.fun_insts)
    }
}

// implementation of Tseitin's transformation, where new variables are made for
// each expression (instead of using distributive laws, etc)

pub fn make_clauses(prog: Program) -> Vec<Clause> {
    let mut state = State::new();
    for expr in prog {
        let bv = add_clauses_expr(&mut state, expr);
        if *bv.get_sort() != Sort::Unit {
            panic!("one or more top level expressions doesn't return unit:\n{:?}", bv);
        }
    }
    state.clauses
}

fn add_clauses_expr(state: &mut State, expr: Expr) -> BvVar {
    match expr {
        Expr::Var(name) => lookup_var(state, name),
        Expr::List(lst) => add_clauses_list(state, lst),
        _ => panic!("bad expr in create_clause, likely lone num: {:?}\n", expr)
    }
}

fn add_clauses_list(state: &mut State, lst: Vec<Expr>) -> BvVar {
    match &lst[..] {
        // slightly hacky method of dealing with our primitives that need literal ints, to save space
        [Expr::Var(n), Expr::Int(num), Expr::Int(size)] if *n == "to-bv".to_string() =>
            add_clauses_to_bv(state, *num, *size),
        // const function -> normal variable
        [Expr::Var(n), Expr::Var(name), Expr::Int(size)] if *n == "declare-bv-fun".to_string() =>
            add_clauses_decl_var(state, name.clone(), *size),
        [Expr::Var(n), Expr::Var(name), rest @ ..] if *n == "declare-bv-fun".to_string() =>
            add_clauses_decl_fun(
                state,
                name.clone(),
                rest.into_iter()
                    .map(|e| get_int(e.clone(), "types in func decl"))
                    .collect()),
        [Expr::Var(n), rest @ ..] => {
            let bvs: Vec<BvVar> = rest.into_iter().map(|e| add_clauses_expr(state, e.clone())).collect();
            add_clauses_fun_bvs(state, n.clone(), bvs)
        },
        _ => panic!("unknown list expr: {:?}", lst)
    }
}

fn add_clauses_fun_bvs(state: &mut State, name: String, args: Vec<BvVar>) -> BvVar {
    // here, we expect all args to be proper bit-vector variables, since we create a new
    // variable at each stage
    match name.as_str() {
        "assert" => add_clauses_assert(state, args),
        "eq" => add_clauses_eq(state, args),
        "neq" => add_clauses_neq(state, args),
        "lt" => add_clauses_lt(state, args),
        "gt" => add_clauses_gt(state, args),
        "leq" => add_clauses_leq(state, args),
        "geq" => add_clauses_geq(state, args),
        "bv-and" => add_clauses_bv_and(state, args),
        _ => panic!("unknown function {}\n", name)
    }
}

fn add_clauses_assert(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let temp = state.mk_temp_bv(Sort::Unit);
    expect_vec_bv_size(&args, &vec![1], "assert");
    state.clauses.push(vec![PropVar::new(temp.get_name().clone(), 0, true)]);
    temp
}

fn add_clauses_eq(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "eq");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_neq(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "neq");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_lt(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "lt");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_leq(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "leq");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_gt(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "gt");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_geq(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, "geq");
    let temp = state.mk_temp_bv(Sort::BitVec(1));
    temp
}

fn add_clauses_bv_and(state: &mut State, args: Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, "bv-and");
    let temp = state.mk_temp_bv(Sort::BitVec(size));
    temp
}

fn add_clauses_to_bv(state: &mut State, num: u128, size: u128) -> BvVar {
    let temp = state.mk_temp_bv(Sort::BitVec(size));
    // for each bit in the vector, we push a clause (which must be true, in CNF) asserting
    // that it must be true if that bit is set and false otherwise
    for i in 0 .. size {
        state.clauses.push(
            vec![PropVar::new(temp.get_name().clone(), i, get_bit(num, i))]
        )
    }
    temp
}

fn add_clauses_decl_fun(state: &mut State, name: String, sig: Vec<u128>) -> BvVar {
    state.fun_insts.insert(name, (vec![], sig));
    state.mk_temp_bv(Sort::Unit)
}

fn add_clauses_decl_var(state: &mut State, name: String, size: u128) -> BvVar {
    state.mk_bv(name, Sort::BitVec(size), true);
    // we need to return unit here, as well (so that declarations must be top-level)
    state.mk_temp_bv(Sort::Unit)
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
fn expect_all_bv_size(lst: &Vec<BvVar>, loc: &str) -> u128 {
    let mut cur_size: Option<u128> = None;
    let die = || panic!("all arguments to {} must be of the same bit-width\n", loc);

    for var in lst {
        match var.get_sort() {
            Sort::BitVec(n) => {
                if *cur_size.get_or_insert(*n) != *n {
                    die()
                }
            }
            _ => die()
        }
    }
    cur_size.unwrap_or_else(|| {die(); 0})
}

// similar to above, but with a specified list of sizes
fn expect_vec_bv_size(lst: &[BvVar], sizes: &[u128], loc: &str) {
    let die = || panic!("arguments to {} must be of sizes {:?}:\n{:?}", loc, sizes, lst);
    
    if lst.len() != sizes.len() {
        die()
    }

    for (bv, s) in lst.iter().zip(sizes.iter()) {
        match bv.get_sort() {
            Sort::BitVec(n) if n != s => die(),
            Sort::Unit => die(),
            _ => continue
        }
    }
}

fn get_bit(num: u128, n: u128) -> bool {
    ((num >> n) & 1) != 0
}