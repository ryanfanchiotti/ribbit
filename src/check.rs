use crate::vars::*;
use crate::syntax::*;

use std::collections::HashMap;
use std::fmt;

// disjunction of each variable (or bit, here)
pub type Clause = Vec<PropVar>;

// state for checking types, adding clauses, etc
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
        self.vars.insert(bv.owned_name(), bv.clone());
        bv
    }

    fn bulk_clause_push(&mut self, clauses: Vec<Vec<(&BvVar, u128, bool)>>) {
        for clause in clauses {
            let clause1 = clause
                .into_iter()
                .map(|(var, off, b)| PropVar::new(var.owned_name(), off, b))
                .collect();
            self.clauses.push(clause1)
        }
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "clauses:\n{:?}\nvars:\n{:?}\nfun_insts:\n{:?}", 
            self.clauses, self.vars, self.fun_insts)
    }
}

// implementation of Tseytin's transformation, where new variables are made for
// each expression (instead of using distributive laws, etc)

pub fn make_clauses(prog: Program) -> (Vec<Clause>, Vec<BvVar>) {
    let mut state = State::new();
    for expr in prog {
        let bv = add_clauses_expr(&mut state, expr);
        if *bv.get_sort() != Sort::Unit {
            panic!("one or more top level expressions doesn't return unit:\n{:?}", bv);
        }
    }
    (state.clauses, state.vars.into_values().collect())
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
            add_clauses_fun_bvs(state, n.clone(), &bvs)
        },
        _ => panic!("unknown list expr: {:?}", lst)
    }
}

fn add_clauses_fun_bvs(state: &mut State, name: String, args: &Vec<BvVar>) -> BvVar {
    // here, we expect all args to be proper bit-vector variables, since we create a new
    // variable at each stage
    match name.as_str() {
        "assert" => add_clauses_assert(state, args),

        "eq" => add_clauses_eq(state, args),
        "ne" => add_clauses_ne(state, args),

        "ult" => add_clauses_ult(state, args),
        "ugt" => add_clauses_ugt(state, args),
        "ule" => add_clauses_ule(state, args),
        "uge" => add_clauses_uge(state, args),

        "and" => add_clauses_and(state, args),
        "or" => add_clauses_or(state, args),
        "xor" => add_clauses_xor(state, args),
        "not" => add_clauses_not(state, args),

        "bv-and" => add_clauses_bv_and(state, args),
        "bv-or" => add_clauses_bv_or(state, args),
        "bv-xor" => add_clauses_bv_xor(state, args),
        "bv-not" => add_clauses_bv_not(state, args),
        "bv-nand" => add_clauses_bv_nand(state, args),
        "bv-nor" => add_clauses_bv_nor(state, args),
        "bv-xnor" => add_clauses_bv_xnor(state, args),

        "bv-add" => add_clauses_bv_add(state, args),
        "bv-sub" => add_clauses_bv_sub(state, args),

        _ => panic!("unknown function {}\n", name)
    }
}

fn add_clauses_assert(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let temp = state.mk_temp_bv(Sort::Unit);
    expect_vec_bv_size(&args[..], &vec![1], "assert");
    state.clauses.push(vec![PropVar::new(args[0].owned_name(), 0, true)]);
    temp
}

fn add_clauses_eq(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "eq");
    // stores equality for each bit
    let helper = state.mk_temp_bv(Sort::BitVec(size));
    let res = state.mk_temp_bv(Sort::BitVec(1));
    let arg1 = &args[0];
    let arg2 = &args[1];
    let combos = [ (false, true, false), (true, false, false)
                 , (true, true, true), (false, false, true) ];
    let mut negated_helpers: Clause = vec![PropVar::new(res.owned_name(), 0, true)];
    for i in 0 .. size {
        for (b1, b2, b3) in combos {
            state.clauses.push(vec![
                PropVar::new(arg1.owned_name(), i, b1),
                PropVar::new(arg2.owned_name(), i, b2),
                PropVar::new(helper.owned_name(), i, b3)
            ]);
        }
        // we need to force res to be false if any helper bit is false
        state.clauses.push(vec![
            PropVar::new(helper.owned_name(), i, true),
            PropVar::new(res.owned_name(), 0, false)
        ]);
        negated_helpers.push(PropVar::new(helper.owned_name(), i, false))
    }
    state.clauses.push(negated_helpers);
    res
}

fn add_clauses_ne(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_all_bv_size(&args, 2, "ne");
    let eq_bv = add_clauses_eq(state, args);
    return add_clauses_not(state, &vec![eq_bv]);
}

fn add_clauses_ult(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    // goal here: build up current less than for each bit, propagating from
    // previous bit if they are the same and overriding on a difference; if
    // the last bit is turned on, arg 1 is less than arg 2
    let size = expect_all_bv_size(&args, 2, "ult");
    let lt = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        if i == 0 {
            state.bulk_clause_push(vec![
                vec![(&args[0], i, true), (&args[1], i, true), (&lt, i, false)],
                vec![(&args[0], i, false), (&args[1], i, false), (&lt, i, false)],
                vec![(&args[0], i, true), (&args[1], i, false), (&lt, i, true)],
                vec![(&args[0], i, false), (&args[1], i, true), (&lt, i, false)],
            ]);
        } else {
            state.bulk_clause_push(vec![
                vec![(&args[0], i, true), (&args[1], i, true), (&lt, i - 1, true), (&lt, i, false)],
                vec![(&args[0], i, true), (&args[1], i, true), (&lt, i - 1, false), (&lt, i, true)],
                vec![(&args[0], i, true), (&args[1], i, false), (&lt, i - 1, true), (&lt, i, true)],
                vec![(&args[0], i, false), (&args[1], i, true), (&lt, i - 1, true), (&lt, i, false)],
                vec![(&args[0], i, false), (&args[1], i, false), (&lt, i - 1, true), (&lt, i, false)],
                vec![(&args[0], i, false), (&args[1], i, true), (&lt, i - 1, false), (&lt, i, false)],
                vec![(&args[0], i, true), (&args[1], i, false), (&lt, i - 1, false), (&lt, i, true)],
                vec![(&args[0], i, false), (&args[1], i, false), (&lt, i - 1, false), (&lt, i, true)],
            ]);
        }
    }
    let res = state.mk_temp_bv(Sort::BitVec(1));
    state.bulk_clause_push(vec![
        vec![(&res, 0, true), (&lt, size - 1, false)],
        vec![(&res, 0, false), (&lt, size - 1, true)],
    ]);
    res
}

fn add_clauses_ule(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_all_bv_size(&args, 2, "ule");
    let lt = add_clauses_ult(state, args);
    let eq = add_clauses_eq(state, args);
    add_clauses_or(state, &vec![lt, eq])
}

fn add_clauses_ugt(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, 2, "ugt");
    let le = add_clauses_ule(state, args);
    add_clauses_not(state, &vec![le])
}

fn add_clauses_uge(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let _ = expect_all_bv_size(&args, 2, "uge");
    let lt = add_clauses_ult(state, args);
    add_clauses_not(state, &vec![lt])
}

fn add_clauses_bv_add(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-add");
    let sum = state.mk_temp_bv(Sort::BitVec(size));
    add_clauses_bv_add_triple(state, &args[0], &args[1], &sum, size);
    sum
}

fn add_clauses_bv_sub(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    // a - b = c implies that c + b = a, under modular arithmetic
    let size = expect_all_bv_size(&args, 2, "bv-sub");
    let subt = state.mk_temp_bv(Sort::BitVec(size));
    add_clauses_bv_add_triple(state, &subt, &args[1], &args[0], size);
    subt
}

// arg0 + arg1 = sum
fn add_clauses_bv_add_triple(state: &mut State, arg0: &BvVar, arg1: &BvVar, sum: &BvVar, size: u128) {
    let carry = state.mk_temp_bv(Sort::BitVec(size + 1));
    // first carry bit is zero / false
    state.clauses.push(vec![PropVar::new(carry.owned_name(), 0, false)]);
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            // we need to enforce that carry[i] + arg0[i] + arg1[1] maps to the
            // correct result (0 for two or zero true, 1 for one or three true)
            vec![(arg0, i, true), (arg1, i, true), (&carry, i, true), (&sum, i, false)],
            vec![(arg0, i, false), (arg1, i, false), (&carry, i, true), (&sum, i, false)],
            vec![(arg0, i, false), (arg1, i, true), (&carry, i, false), (&sum, i, false)],
            vec![(arg0, i, true), (arg1, i, false), (&carry, i, false), (&sum, i, false)],
            vec![(arg0, i, true), (arg1, i, true), (&carry, i, false), (&sum, i, true)],
            vec![(arg0, i, true), (arg1, i, false), (&carry, i, true), (&sum, i, true)],
            vec![(arg0, i, false), (arg1, i, true), (&carry, i, true), (&sum, i, true)],
            vec![(arg0, i, false), (arg1, i, false), (&carry, i, false), (&sum, i, true)],

            // now we enforce the carry logic, where at least two of carry[i], arg0[i],
            // and arg1[i] must be true
            vec![(arg0, i, false), (arg1, i, false), (&carry, i, true), (&carry, i + 1, true)],
            vec![(arg0, i, false), (arg1, i, true), (&carry, i, false), (&carry, i + 1, true)],
            vec![(arg0, i, true), (arg1, i, false), (&carry, i, false), (&carry, i + 1, true)],
            vec![(arg0, i, false), (arg1, i, false), (&carry, i, false), (&carry, i + 1, true)],
            vec![(arg0, i, true), (arg1, i, true), (&carry, i, false), (&carry, i + 1, false)],
            vec![(arg0, i, true), (arg1, i, false), (&carry, i, true), (&carry, i + 1, false)],
            vec![(arg0, i, false), (arg1, i, true), (&carry, i, true), (&carry, i + 1, false)],
            vec![(arg0, i, true), (arg1, i, true), (&carry, i, true), (&carry, i + 1, false)],

        ]);
    }
}

fn add_clauses_bv_and(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-and");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, false), (&args[1], i, false), (&res, i, true)],
            vec![(&args[0], i, true), (&res, i, false)],
            vec![(&args[1], i, true), (&res, i, false)]
        ]);
    }
    res
}

fn add_clauses_and(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_vec_bv_size(&args[..], &vec![1, 1], "and");
    let res = state.mk_temp_bv(Sort::BitVec(1));
    state.bulk_clause_push(vec![
        vec![(&args[0], 0, false), (&args[1], 0, false), (&res, 0, true)],
        vec![(&args[0], 0, true), (&res, 0, false)],
        vec![(&args[1], 0, true), (&res, 0, false)]
    ]);
    res
}

fn add_clauses_bv_or(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-or");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, true), (&args[1], i, true), (&res, i, false)],
            vec![(&args[0], i, false), (&res, i, true)],
            vec![(&args[1], i, false), (&res, i, true)]
        ]);
    }
    res
}

fn add_clauses_or(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_vec_bv_size(&args[..], &vec![1, 1], "or");
    let res = state.mk_temp_bv(Sort::BitVec(1));
    state.bulk_clause_push(vec![
        vec![(&args[0], 0, true), (&args[1], 0, true), (&res, 0, false)],
        vec![(&args[0], 0, false), (&res, 0, true)],
        vec![(&args[1], 0, false), (&res, 0, true)]
    ]);
    res
}

fn add_clauses_bv_xor(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-xor");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, false), (&args[1], i, false), (&res, i, false)],
            vec![(&args[0], i, true), (&args[1], i, true), (&res, i, false)],
            vec![(&args[0], i, true), (&args[1], i, false), (&res, i, true)],
            vec![(&args[0], i, false), (&args[1], i, true), (&res, i, true)],
        ]);
    }
    res
}

fn add_clauses_xor(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_vec_bv_size(&args[..], &vec![1, 1], "xor");
    let res = state.mk_temp_bv(Sort::BitVec(1));
    state.bulk_clause_push(vec![
            vec![(&args[0], 0, false), (&args[1], 0, false), (&res, 0, false)],
            vec![(&args[0], 0, true), (&args[1], 0, true), (&res, 0, false)],
            vec![(&args[0], 0, true), (&args[1], 0, false), (&res, 0, true)],
            vec![(&args[0], 0, false), (&args[1], 0, true), (&res, 0, true)],
    ]);
    res
}

fn add_clauses_bv_nand(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-nand");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, false), (&args[1], i, false), (&res, i, false)],
            vec![(&args[0], i, true), (&res, i, true)],
            vec![(&args[1], i, true), (&res, i, true)]
        ]);
    }
    res
}

fn add_clauses_bv_nor(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-nor");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, true), (&args[1], i, true), (&res, i, true)],
            vec![(&args[0], i, false), (&res, i, false)],
            vec![(&args[1], i, false), (&res, i, false)]
        ]);
    }
    res
}

fn add_clauses_bv_xnor(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 2, "bv-xnor");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, false), (&args[1], i, false), (&res, i, true)],
            vec![(&args[0], i, true), (&args[1], i, true), (&res, i, true)],
            vec![(&args[0], i, true), (&args[1], i, false), (&res, i, false)],
            vec![(&args[0], i, false), (&args[1], i, true), (&res, i, false)],
        ]);
    }
    res
}

fn add_clauses_bv_not(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    let size = expect_all_bv_size(&args, 1, "bv-not");
    let res = state.mk_temp_bv(Sort::BitVec(size));
    for i in 0 .. size {
        state.bulk_clause_push(vec![
            vec![(&args[0], i, false), (&res, i, false)],
            vec![(&args[0], i, true), (&res, i, true)],
        ]);
    }
    res
}

fn add_clauses_not(state: &mut State, args: &Vec<BvVar>) -> BvVar {
    expect_vec_bv_size(&args[..], &vec![1], "not");
    let res = state.mk_temp_bv(Sort::BitVec(1));
    state.bulk_clause_push(vec![
            vec![(&args[0], 0, false), (&res, 0, false)],
            vec![(&args[0], 0, true), (&res, 0, true)],
    ]);
    res
}

fn add_clauses_to_bv(state: &mut State, num: u128, size: u128) -> BvVar {
    let temp = state.mk_temp_bv(Sort::BitVec(size));
    // for each bit in the vector, we push a clause (which must be true, in CNF) asserting
    // that it must be true if that bit is set and false otherwise
    for i in 0 .. size {
        state.clauses.push(
            vec![PropVar::new(temp.owned_name(), i, get_bit(num, i))]
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
fn expect_all_bv_size(lst: &Vec<BvVar>, len: usize, loc: &str) -> u128 {
    let mut cur_size: Option<u128> = None;
    let die = || panic!("all arguments to {} must be of the same bit-width\n", loc);

    if lst.len() != len {
        panic!("{} expects {} arguments\n", loc, len)
    }

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