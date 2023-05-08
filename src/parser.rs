use anyhow::{anyhow, Context, Result};
use bnf::Grammar;

static BNF_GRAMMAR: &str = include_str!("grammar.bnf");

struct Parser {
    grammar: Grammar,
}

impl Parser {
    pub(crate) fn new() -> Result<Self> {
        let grammar: Grammar = BNF_GRAMMAR.parse().context("Couldn't parse grammar")?;
        Ok(Self { grammar })
    }

    pub(crate) fn parse(&self, formula: &str) -> Result<()> {
        let parse_tree = self
            .grammar
            .parse_input(formula)
            .next()
            .context(format!("Grammar could not parse input: {}", formula))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{fs::read_dir, path::Path};

    use anyhow::Context;
    use bnf::Grammar;

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
".parse().expect("Unparsable grammar");

        let input =
            "\"Ala\"\n"
        ;

        grammar.parse_input(input).next().context(format!("Could not parse input: {}", input)).unwrap();
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
                parser.parse(formula).unwrap();
            }
        }


        let test_path = Path::new("/home/xps15/Studia/Sem8/Logika/Laby/Zal/FO-prover/tests");
        assert!(test_path.exists());

        let good_paths = ["A", "B", "C"];

        let good = good_paths
            .iter()
            .map(|&path| {
                let case_path = test_path.join(path);
                read_dir(&case_path)
                    .unwrap()
                    .map(move |entry| (case_path.clone(), entry))
            })
            .flatten();

        for (path, file) in good {
            let file = file.unwrap();
            println!("\nTest: {:?}", &file);
            let os_name = file.file_name();
            let name = os_name.to_str().unwrap();
            if file.file_type().unwrap().is_file()
            /* && name.ends_with(".lat")*/
            {
                let complete_filename = path.join(name);
                let input = std::fs::read(complete_filename).unwrap();
                let input_str = String::from_utf8(input).unwrap();
                println!("Input:\n{}", &input_str);
                parser.parse(&input_str).unwrap()
            }
        }
    }
}
