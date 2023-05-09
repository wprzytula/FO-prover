use anyhow::{bail, Context};
use bnf::{ParseTree, ParseTreeNode};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Formula {
    Instant(Instant),
    LogOp(LogOp),
    Rel(Rel),
    Quantifier(Quantifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum Instant {
    T,
    F,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LogOp {
    Not(Box<Formula>),
    Bin(BinLogOp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BinLogOp {
    kind: BinLogOpKind,
    phi: Box<Formula>,
    psi: Box<Formula>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BinLogOpKind {
    And,
    Or,
    Implies,
    Iff,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Quantifier {
    kind: QuantifierKind,
    var: String,
    phi: Box<Formula>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum QuantifierKind {
    Exists,
    Forall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Rel {
    name: String,
    terms: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

mod parse {
    use super::*;

    use anyhow::Result;

    fn assert_nonterminal_lhs(tree: &ParseTree, ident: &str) -> Result<()> {
        match tree.lhs {
            bnf::Term::Terminal(t) => bail!("Expected nonterminal {}, got terminal {}", ident, t),
            bnf::Term::Nonterminal(s) => {
                if s != ident {
                    bail!("Expected {}, got {}", ident, s);
                }
            }
        };
        Ok(())
    }

    fn extract_rhs<'a, const LEN: usize>(
        tree: &'a ParseTree<'a>,
    ) -> Result<[&'a ParseTreeNode<'a>; LEN]> {
        static MOCK: ParseTreeNode = ParseTreeNode::Terminal("()");
        let mut iter = tree.rhs_iter();
        let mut array = [&MOCK; LEN];
        for item in array.iter_mut() {
            *item = iter.next().context("rhs too short")?;
        }
        if let Some(x) = iter.next() {
            bail!(
                "Nonexhaustive rhs extraction; remained: {:#?}",
                std::iter::once(x).chain(iter).collect::<Vec<_>>()
            );
        }
        Ok(array)
    }

    fn extract_singleton_rhs<'a>(tree: &'a ParseTree<'a>) -> Result<&'a ParseTreeNode<'a>> {
        extract_rhs::<1>(tree).map(|array| array[0])
    }

    fn extract_nonterminal_node<'a>(
        node: &'a ParseTreeNode,
        ident: &str,
    ) -> Result<&'a ParseTree<'a>> {
        match node {
            ParseTreeNode::Terminal(t) => {
                bail!("Expected nonterminal <{}>, got terminal {}", ident, t)
            }
            ParseTreeNode::Nonterminal(node) => Ok(node),
        }
    }

    fn extract_terminal_node<'a>(node: &'a ParseTreeNode, ident: &str) -> Result<&'a str> {
        match node {
            ParseTreeNode::Terminal(t) => Ok(t),
            ParseTreeNode::Nonterminal(node) => {
                bail!("Expected terminal {}, got nonterminal <{}>", ident, node)
            }
        }
    }

    fn extract_nonterminal_term<'a>(term: &'a bnf::Term, ident: &str) -> Result<&'a str> {
        match term {
            bnf::Term::Terminal(t) => bail!("Expected nonterminal <{}>, got terminal {}", ident, t),
            bnf::Term::Nonterminal(node) => Ok(node.as_str()),
        }
    }

    impl Formula {
        pub(crate) fn parse_input(tree: &ParseTree) -> Result<Formula> {
            assert_nonterminal_lhs(tree, "input")?;
            let phi_node = tree.rhs_iter().next().context("Empty <input> rhs")?;
            let tree = extract_nonterminal_node(phi_node, "phi")?;
            Self::parse_phi(tree)
        }

        fn parse_phi(tree: &ParseTree) -> Result<Formula> {
            let ident = "formula";
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            let node = extract_nonterminal_term(tree.lhs, ident)?;
            match node {
                "Instant" => Self::parse_instant(tree).map(Formula::Instant),
                "Rel" => Self::parse_rel(tree).map(Formula::Rel),
                "LogOp" => Self::parse_log_op(tree).map(Formula::LogOp),
                "Quantifier" => Self::parse_quantifier(tree).map(Formula::Quantifier),
                otherwise => bail!("Expected phi variant, got \"{}\"", otherwise),
            }
        }

        fn parse_instant(tree: &ParseTree) -> Result<Instant> {
            let ident = "Instant";
            assert_nonterminal_lhs(tree, ident)?;
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            let node = extract_nonterminal_term(tree.lhs, ident)?;
            match node {
                "T" => Ok(Instant::T),
                "F" => Ok(Instant::F),
                otherwise => bail!("Expected {} variant, got {}", ident, otherwise),
            }
        }

        fn parse_rel(tree: &ParseTree) -> Result<Rel> {
            let ident = "Rel";
            assert_nonterminal_lhs(tree, ident)?;
            let rhs = extract_rhs::<5>(tree)?;
            let name = Self::parse_string(extract_nonterminal_node(rhs[2], "string")?)?;
            let terms = Self::parse_terms(extract_nonterminal_node(rhs[4], "ts")?)?;
            Ok(Rel { name, terms })
        }

        fn parse_log_op(tree: &ParseTree) -> Result<LogOp> {
            let ident = "LogOp";
            assert_nonterminal_lhs(tree, ident)?;
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            let node = extract_nonterminal_term(tree.lhs, ident)?;
            match node {
                "Not" => Self::parse_not(tree),
                "BinLogOp" => Self::parse_bin_log_op(tree).map(LogOp::Bin),
                otherwise => bail!("Expected {} variant, got {}", ident, otherwise),
            }
        }

        fn parse_not(tree: &ParseTree) -> Result<LogOp> {
            let ident = "Not";
            assert_nonterminal_lhs(tree, ident)?;
            let rhs = extract_rhs::<5>(tree)?;
            let word = extract_terminal_node(rhs[0], ident)?;
            if word != ident {
                bail!("Unexpected word")
            }
            let phi = extract_nonterminal_node(rhs[3], ident)?;
            let phi = Self::parse_phi(phi)?;
            Ok(LogOp::Not(Box::new(phi)))
        }

        fn parse_bin_log_op(tree: &ParseTree) -> Result<BinLogOp> {
            let ident = "BinLogOp";
            assert_nonterminal_lhs(tree, ident)?;
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            let kind = match extract_nonterminal_term(tree.lhs, ident)? {
                "And" => BinLogOpKind::And,
                "Or" => BinLogOpKind::Or,
                "Implies" => BinLogOpKind::Implies,
                "Iff" => BinLogOpKind::Iff,
                otherwise => bail!("Expected {} variant, got {}", ident, otherwise),
            };
            let rhs = extract_rhs::<9>(tree)?;
            // assert_eq!(extract_nonterminal_term(tree.lhs, ident)?, extract_terminal_term(rhs[0].lhs, ident)?)
            let parse_phi = |i: usize| {
                let phi = extract_nonterminal_node(rhs[i], "phi")?;
                Self::parse_phi(phi)
            };
            let phi = Box::new(parse_phi(3)?);
            let psi = Box::new(parse_phi(7)?);

            Ok(BinLogOp { kind, phi, psi })
        }

        fn parse_quantifier(tree: &ParseTree) -> Result<Quantifier> {
            let ident = "Quantifier";
            assert_nonterminal_lhs(tree, ident)?;
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            let kind = match extract_nonterminal_term(tree.lhs, ident)? {
                "Forall" => QuantifierKind::Forall,
                "Exists" => QuantifierKind::Exists,
                otherwise => bail!("Expected {} variant, got {}", ident, otherwise),
            };
            let rhs = extract_rhs::<7>(tree)?;
            let var = extract_nonterminal_node(rhs[2], ident)?;
            let var = Self::parse_string(var)?;
            let phi = extract_nonterminal_node(rhs[5], ident)?;
            let phi = Box::new(Self::parse_phi(phi)?);

            Ok(Quantifier { kind, var, phi })
        }

        fn parse_string(tree: &ParseTree) -> Result<String> {
            assert_nonterminal_lhs(tree, "string")?;
            let rhs = extract_rhs::<3>(tree)?;

            let mut buf = String::new();
            let mut seq = extract_nonterminal_node(rhs[1], "alphanumeric_seq")?;
            loop {
                assert_nonterminal_lhs(seq, "alphanumeric_seq")?;
                let alphanumeric_node = seq
                    .rhs_iter()
                    .next()
                    .context("Expected alphanumeric, got empty rhs")?;
                let alphanumeric_tree =
                    extract_nonterminal_node(alphanumeric_node, "alphanumeric")?;
                let ch = Self::parse_alphanumeric(alphanumeric_tree)?;
                buf.push(ch);
                if seq.rhs_iter().count() == 2 {
                    let rhs = extract_rhs::<2>(seq)?;
                    seq = extract_nonterminal_node(rhs[1], "alphanumeric_seq")?;
                } else {
                    break;
                }
            }
            Ok(buf)
        }

        fn parse_alphanumeric(tree: &ParseTree) -> Result<char> {
            let ident = "alphanumeric";
            assert_nonterminal_lhs(tree, ident)?;
            let sign_tree = extract_singleton_rhs(tree)?;
            let mut chars = extract_terminal_node(sign_tree, ident)?.chars();
            let fst_char = chars
                .next()
                .context("Expected nonempty string as alphanumeric")?;
            if chars.next().is_none() {
                Ok(fst_char)
            } else {
                bail!("Expected one-char string as alphanumeric")
            }
        }

        fn parse_terms(tree: &ParseTree) -> Result<Vec<Term>> {
            assert_nonterminal_lhs(tree, "ts")?;
            let mut terms = Vec::new();
            let rhs = extract_rhs::<3>(tree)?;
            let mut t_seq = extract_nonterminal_node(rhs[1], "t_seq")?;
            loop {
                let term_node = t_seq
                    .rhs_iter()
                    .next()
                    .context("t_seq can't have empty rhs")?;
                let term_tree = match term_node {
                    ParseTreeNode::Terminal(t) => {
                        if !t.is_empty() {
                            bail!("Unexpected nonempty terminal in t_seq")
                        }
                        None
                    }
                    ParseTreeNode::Nonterminal(node) => Some(node),
                };
                if let Some(term_tree) = term_tree {
                    terms.push(Self::parse_term(term_tree)?);
                }
                if let Ok(rhs_cont) = extract_rhs::<4>(tree) {
                    t_seq = extract_nonterminal_node(rhs_cont[3], "t_seq")?;
                } else {
                    break;
                }
            }

            Ok(terms)
        }

        fn parse_term(tree: &ParseTree) -> Result<Term> {
            let ident = "t";
            assert_nonterminal_lhs(tree, ident)?;
            let tree = extract_nonterminal_node(extract_singleton_rhs(tree)?, ident)?;
            match extract_nonterminal_term(tree.lhs, ident)? {
                "Var" => Self::parse_var(tree),
                "Fun" => Self::parse_fun(tree),
                otherwise => bail!("Expected {} variant, got {}", ident, otherwise),
            }
        }

        fn parse_var(tree: &ParseTree) -> Result<Term> {
            let ident = "Var";
            assert_nonterminal_lhs(tree, ident)?;
            let rhs = extract_rhs::<3>(tree)?;
            let name = Self::parse_string(extract_nonterminal_node(rhs[2], ident)?)?;
            Ok(Term::Var(name))
        }

        fn parse_fun(tree: &ParseTree) -> Result<Term> {
            let ident = "Fun";
            assert_nonterminal_lhs(tree, ident)?;
            let rhs = extract_rhs::<5>(tree)?;
            let name = Self::parse_string(extract_nonterminal_node(rhs[2], ident)?)?;
            let terms = Self::parse_terms(extract_nonterminal_node(rhs[4], ident)?)?;
            Ok(Term::Fun(name, terms))
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::{parser::Parser, tests::for_each_external_test};

        use super::*;
        use Instant::{F, T};
        use QuantifierKind::Exists;

        #[test]
        fn correct_parsing_to_formula() {
            let parser = Parser::new().unwrap();

            {
                let _drinker_paradox =
                    r#"Exists "x" (Implies (Rel "D" [Var "x"]) (Forall "y" (Rel "D" [Var "y"])))"#;

                let formulas = [
                    ("T", Formula::Instant(T)),
                    (
                        "And (T) (Exists \"xD\" (F))",
                        Formula::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::And,
                            phi: Box::new(Formula::Instant(T)),
                            psi: Box::new(Formula::Quantifier(Quantifier {
                                kind: Exists,
                                var: "xD".to_owned(),
                                phi: Box::new(Formula::Instant(F)),
                            })),
                        })),
                    ),
                    // r#"Exists "x" (T)"#,
                    // r#"Rel "D" [Var "x"]"#,
                    // r#"Forall "y" (F)"#,
                    // r#"Forall "y" (Rel "D" [Var "y"])"#,
                    // drinker_paradox,
                ];

                for (formula, expected) in formulas {
                    // let parsed_formula = parser.parse(formula).unwrap();
                    let tree = parser.parse_to_tree(formula).unwrap();
                    println!("{:#?}", tree);
                    let parsed_formula = Formula::parse_input(&tree)
                        .unwrap_or_else(|err| panic!("Backtrace: {}", err.backtrace()));
                    assert_eq!(parsed_formula, expected);
                }
            }
        }

        #[test]
        fn external_tests_are_parsed_into_formula() {
            let parser = Parser::new().unwrap();
            for_each_external_test(|input| {
                parser
                    .parse(input)
                    .unwrap_or_else(|err| panic!("Error: {};\n{}", err, err.backtrace()));
            });
        }
    }
}
