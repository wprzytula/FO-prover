use anyhow::{Context, Result};
use bnf::{Grammar, ParseTree};

use super::formula::Formula;

static BNF_GRAMMAR: &str = include_str!("grammar.bnf");

pub(crate) struct Parser {
    grammar: Grammar,
}

impl Parser {
    pub(crate) fn new() -> Result<Self> {
        let grammar: Grammar = BNF_GRAMMAR.parse().context("Couldn't parse grammar")?;
        Ok(Self { grammar })
    }

    pub(crate) fn parse_to_tree<'a>(&'a self, formula: &'a str) -> Result<ParseTree> {
        self.grammar
            .parse_input(formula)
            .next()
            .context(format!("Grammar could not parse input: {}", formula))
    }

    pub(crate) fn parse<'a>(&'a self, formula: &'a str) -> Result<Formula> {
        let parse_tree = self.parse_to_tree(formula)?;
        Formula::parse_input(&parse_tree)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;
    use bnf::Grammar;

    use crate::tests::for_each_external_test;

    use super::Parser;

    #[test]
    fn grammar_is_parsable() {
        let _parser = Parser::new().unwrap();
    }

    #[test]
    fn experiments() {
        let grammar: Grammar = "
<input> ::= <string> | <string> '\n'

<string> ::= '\"' <alphanumeric_seq> '\"'

<alphanumeric_seq> ::= <alphanumeric> | <alphanumeric> <alphanumeric_seq>

<alphanumeric> ::= 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' | 'L' | 'M' |
                   'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' | 'X' | 'Y' | 'Z' |
                   'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' | 'l' | 'm' |
                   'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' | 'x' | 'y' | 'z' |
                   '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
"
        .parse()
        .expect("Unparsable grammar");

        let input = "\"Ala\"\n";

        grammar
            .parse_input(input)
            .next()
            .context(format!("Could not parse input: {}", input))
            .unwrap();
    }

    #[test]
    fn good_inputs_are_parsed() {
        let parser = Parser::new().unwrap();

        {
            let drinker_paradox =
                r#"Exists "x" (Implies (Rel "D" [Var "x"]) (Forall "y" (Rel "D" [Var "y"])))"#;

            let formulas = [
                "T",
                "And (T) (T)",
                r#"Exists "x" (T)"#,
                r#"Rel "D" [Var "x"]"#,
                r#"Forall "y" (F)"#,
                r#"Forall "y" (Rel "D" [Var "y"])"#,
                drinker_paradox,
            ];

            for formula in formulas {
                parser.parse_to_tree(formula).unwrap();
            }
        }

        for_each_external_test(|input| {
            parser.parse_to_tree(input).unwrap();
        });
    }
}
