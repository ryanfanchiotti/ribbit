use nom::{
    IResult,
    Parser,
    error::ParseError,
    branch::alt,
    multi::{many0_count, many1},
    bytes::complete::tag,
    sequence::{delimited, pair},
    character::complete::{char, i128, multispace0, alpha1, alphanumeric1},
    combinator::recognize,
};

// S-expression for our lisp-like language
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(String),
    Int(i128),
    List(Vec<Expr>)
}

pub type Program = Vec<Expr>;

// Whitespace eater, from the nom recipes
// Really not sure why they didn't just implement these...?
pub fn whitespace<'a, O, E: ParseError<&'a str>, F>(
    inner: F,
) -> impl Parser<&'a str, Output = O, Error = E>
where
    F: Parser<&'a str, Output = O, Error = E>,
{
    delimited(multispace0, inner, multispace0)
}

pub fn parse_int(input: &str) -> IResult<&str, Expr> {
    whitespace(i128).map(|n| Expr::Int(n)).parse(input)
}

pub fn other_ident_char(input: &str) -> IResult<&str, &str> {
    alt((tag("-"), tag("_"))).parse(input)
}

// Identifier eater, from the nom recipes
pub fn parse_ident(input: &str) -> IResult<&str, &str> {
  recognize(
    pair(
      alt((alpha1, other_ident_char)),
      many0_count(alt((alphanumeric1, other_ident_char)))
    )
  ).parse(input)
}

pub fn parse_var(input: &str) -> IResult<&str, Expr> {
    whitespace(parse_ident).map(|s: &str| Expr::Var(s.to_string())).parse(input)
}

pub fn parse_list(input: &str) -> IResult<&str, Expr> {
    delimited(
        whitespace(char('(')),
        many1(parse_expr),
        whitespace(char(')')),
    ).map(|l| Expr::List(l)).parse(input)
}  

pub fn parse_expr(input: &str) -> IResult<&str, Expr> {
    alt((parse_list, parse_var, parse_int)).parse(input)
}

pub fn parse_program(input: &str) -> IResult<&str, Program> {
    many1(parse_expr).parse(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_basic() {
        let input = "(declare-bv-fun x 32)\n(declare-bv-fun y 32)\n(assert (eq x (bv-and y (to-bv 10))))\n(assert (lt x (to-bv 15)))";

        let expected = vec![
            Expr::List(vec![
                Expr::Var("declare-bv-fun".to_string()),
                Expr::Var("x".to_string()),
                Expr::Int(32),
            ]),
            Expr::List(vec![
                Expr::Var("declare-bv-fun".to_string()),
                Expr::Var("y".to_string()),
                Expr::Int(32),
            ]),
            Expr::List(vec![
                Expr::Var("assert".to_string()),
                Expr::List(vec![
                    Expr::Var("eq".to_string()),
                    Expr::Var("x".to_string()),
                    Expr::List(vec![
                        Expr::Var("bv-and".to_string()),
                        Expr::Var("y".to_string()),
                        Expr::List(vec![
                            Expr::Var("to-bv".to_string()),
                            Expr::Int(10),
                        ]),
                    ]),
                ]),
            ]),
            Expr::List(vec![
                Expr::Var("assert".to_string()),
                Expr::List(vec![
                    Expr::Var("lt".to_string()),
                    Expr::Var("x".to_string()),
                    Expr::List(vec![
                        Expr::Var("to-bv".to_string()),
                        Expr::Int(15),
                    ]),
                ]),
            ]),
        ];

        let (_, parsed_program) = parse_program(input).expect("program parsed");
        assert_eq!(parsed_program, expected);
    }
}