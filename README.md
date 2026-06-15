## Ribbit

Eager, bit-blasting toy SMT solver for quantifier free bit vectors. Input language is a simplified version of QF_BV and similar theories from SMT-LIB, as described below and seen in `/examples`. Mostly made for fun / learning purposes, hence the silly language. Uses Kissat as the underlying SMT solver, through the rustsat crate.

Dependencies outside of Cargo:
- Libclang, for bindgen

#### Input language
- For all of these, assume A is a generic bit-vector, and bool is a bit-vector of size 1 that can be made with to-bv

Declare uninterpreted functions (or constants)
- `declare-bv-fun` (`identifier` `int+`, returns `unit`)

Assert that a statement is true
- `assert` (`bool`, returns `unit`)

If-then-else
- `ite` (`bool` `A` `A`, returns `A`)

Equality and comparisons, a U prefix stands for unsigned
- `eq` (`bool` `bool`, returns `bool`)
- `ne` (`bool` `bool`, returns `bool`)
- `ult` (`A` `A`, returns `bool`)
- `ugt` (`A` `A`, returns `bool`)
- `ule` (`A` `A`, returns `bool`)
- `uge` (`A` `A`, returns `bool`)

Boolean functions
- `and` (`bool` `bool`, returns `bool`)
- `or` (`bool` `bool`, returns `bool`)
- `xor` (`bool` `bool`, returns `bool`)
- `not` (`bool` `bool`, returns `bool`)
- `implies` (`bool` `bool`, returns `bool`)

Boolean functions, on bit-vectors
- `bv-and` (`A` `A`, returns `A`)
- `bv-or` (`A` `A`, returns `A`)
- `bv-xor` (`A` `A`, returns `A`)
- `bv-not` (`A` `A`, returns `A`)
- `bv-nand` (`A` `A`, returns `A`)
- `bv-nor` (`A` `A`, returns `A`)
- `bv-xnor` (`A` `A`, returns `A`)

Arithmetic
- `bv-add` (`A` `A`, returns `A`)
- `bv-sub` (`A` `A`, returns `A`)