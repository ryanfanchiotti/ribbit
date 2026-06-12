use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

// we don't need a full type system for this, since we are making variables and
// uninterpreted functions return fixed-size bit-vectors. some built-in functions
// are generic, but only over one variable, which can be dynamically checked when
// destructuring each function.

static NEXT_VAR: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Unit, // for declare-bv-fun, ...
    BitVec(u128), // for fixed size bit-vectors, such as 1-bit booleans
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BvVar {
    name: String,
    sort: Sort, // also known as type, in other places
    display: bool // whether we want to show this var in our model
}

impl BvVar {
    pub fn new(name: String, sort: Sort, display: bool) -> Self {
        BvVar {name, sort, display}
    }

    pub fn new_temp(sort: Sort) -> Self {
        let name = fresh_name();
        BvVar {name, sort, display: false}
    }

    pub fn get_sort(&self) -> &Sort {
        &self.sort
    }

    pub fn get_display(&self) -> bool {
        self.display
    }

    pub fn owned_name(&self) -> String {
        self.name.clone()
    }
}

impl fmt::Display for BvVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: sort={:?}, display={}", self.name, self.sort, self.display)
    }
}

pub fn fresh_id() -> usize {
    NEXT_VAR.fetch_add(1, Ordering::Relaxed)
}

pub fn fresh_name() -> String {
    let id = fresh_id();
    format!("fresh_name_{}", id)
}

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

    pub fn owned_name(&self) -> String {
        self.name.clone()
    }

    pub fn get_offset(&self) -> u128 {
        self.offset
    }

    pub fn get_value(&self) -> bool {
        self.value
    }
}