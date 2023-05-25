use std::{
    collections::HashSet,
    fmt::{Display, Write},
    hash::Hash,
};

use anyhow::{bail, Context};
use bnf::{ParseTree, ParseTreeNode};

use crate::propositional::proposition::{fresh_var, UsedVars};

use super::herbrand::display_term_name_with_terms;

pub(crate) trait Logic {}
impl Logic for Formula {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Formula {
    Instant(Instant),
    LogOp(LogOp<Formula>),
    Rel(Rel),
    Quantified(Quantifier),
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Instant(i) => i.fmt(f),
            Formula::LogOp(op) => op.fmt(f),
            Formula::Rel(rel) => rel.fmt(f),
            Formula::Quantified(q) => q.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum Instant {
    T,
    F,
}

impl Instant {
    pub(crate) fn into_bool(self) -> bool {
        match self {
            Instant::T => true,
            Instant::F => false,
        }
    }

    pub(crate) fn from_bool(b: bool) -> Self {
        if b {
            Self::T
        } else {
            Self::F
        }
    }
}

impl Display for Instant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            Instant::T => '⊤',
            Instant::F => '⊥',
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LogOp<L: Logic> {
    Not(Box<L>),
    Bin(BinLogOp<L>),
}

impl<T: Logic + Display> Display for LogOp<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogOp::Not(inner) => {
                write!(f, "~{}", inner)
            }
            LogOp::Bin(binop) => binop.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BinLogOp<L: Logic> {
    pub(crate) kind: BinLogOpKind,
    pub(crate) phi: Box<L>,
    pub(crate) psi: Box<L>,
}

impl<T: Logic + Display> Display for BinLogOp<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {} {})", self.phi, self.kind, self.psi)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BinLogOpKind {
    And,
    Or,
    Implies,
    Iff,
}

impl Display for BinLogOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            BinLogOpKind::And => '∧',
            BinLogOpKind::Or => '∨',
            BinLogOpKind::Implies => '→',
            BinLogOpKind::Iff => '↔',
        })
    }
}

type FOLogOp = LogOp<Formula>;
type FOBinLogOp = BinLogOp<Formula>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Quantifier {
    pub(crate) kind: QuantifierKind,
    pub(crate) var: String,
    pub(crate) phi: Box<Formula>,
}

impl Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;
        write!(f, "{}", self.kind)?;
        f.write_char(' ')?;
        f.write_str(self.var.as_str())?;
        f.write_char('.')?;
        write!(f, "{}", self.phi)?;
        f.write_char(')')?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum QuantifierKind {
    Exists,
    Forall,
}

impl Display for QuantifierKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            QuantifierKind::Exists => '∃',
            QuantifierKind::Forall => '∀',
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Rel {
    pub(crate) name: String,
    pub(crate) terms: Vec<Term>,
}

impl Display for Rel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_name_with_terms(f, &self.name, &self.terms)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Term {
    Var(String),
    Fun(String, Vec<Term>),
}

impl Term {
    pub(crate) fn free_vars<'a>(
        &'a self,
        free: &mut HashSet<String>,
        captured: &mut HashSet<&'a str>,
    ) {
        match self {
            Term::Var(var) => {
                if !captured.contains(var.as_str()) {
                    free.insert(var.clone());
                }
            }
            Term::Fun(_name, terms) => terms.iter().for_each(|term| term.free_vars(free, captured)),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(var) => var.fmt(f),
            Term::Fun(name, terms) => display_term_name_with_terms(f, name, terms),
        }
    }
}

impl UsedVars for Term {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S> {
        let mut vars = HashSet::new();
        self.add_used_vars(&mut vars);
        vars
    }

    fn add_used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self, vars: &mut HashSet<S>) {
        fn rec<'a, S: From<&'a String> + Eq + Hash>(vars: &mut HashSet<S>, term: &'a Term) {
            match term {
                Term::Var(v) => {
                    vars.insert(v.into());
                }
                Term::Fun(_name, terms) => terms.iter().for_each(|term| rec(vars, term)),
            }
        }
        rec(vars, self);
    }
}

pub(crate) trait RenameVar {
    fn rename(&mut self, var: &str, new_name: &String);
}

impl RenameVar for Term {
    fn rename(&mut self, var: &str, new_name: &String) {
        match self {
            Term::Var(v) => {
                if var == v {
                    *v = new_name.clone();
                }
            }
            Term::Fun(_name, terms) => terms.iter_mut().for_each(|term| term.rename(var, new_name)),
        }
    }
}

impl RenameVar for Formula {
    fn rename(&mut self, var: &str, new_name: &String) {
        match self {
            Formula::Instant(_) => (),
            Formula::LogOp(LogOp::Not(phi)) => phi.rename(var, new_name),
            Formula::LogOp(LogOp::Bin(BinLogOp { phi, psi, .. })) => {
                phi.rename(var, new_name);
                psi.rename(var, new_name);
            }
            Formula::Rel(Rel { terms, .. }) => {
                terms.iter_mut().for_each(|term| term.rename(var, new_name))
            }
            Formula::Quantified(Quantifier {
                var: quantified_var,
                phi,
                ..
            }) => {
                if var != quantified_var {
                    phi.rename(var, new_name);
                }
            }
        }
    }
}

impl UsedVars for Formula {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S> {
        let mut vars = HashSet::new();
        self.add_used_vars(&mut vars);
        vars
    }

    fn add_used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self, vars: &mut HashSet<S>) {
        match self {
            Formula::Instant(_) => (),
            Formula::LogOp(LogOp::Not(phi)) => phi.add_used_vars(vars),
            Formula::LogOp(LogOp::Bin(BinLogOp { phi, psi, .. })) => {
                phi.add_used_vars(vars);
                psi.add_used_vars(vars);
            }
            Formula::Rel(Rel { terms, .. }) => {
                terms.iter().for_each(|term| term.add_used_vars(vars))
            }
            Formula::Quantified(Quantifier { var, phi, .. }) => {
                vars.insert(var.into());
                phi.add_used_vars(vars);
            }
        }
    }
}

impl Formula {
    pub(crate) fn not(phi: Self) -> Self {
        Self::LogOp(LogOp::Not(Box::new(phi)))
    }

    fn free_vars(&self) -> HashSet<String> {
        let mut free = HashSet::new();
        let mut captured = HashSet::new();
        fn rec<'a>(
            formula: &'a Formula,
            free: &mut HashSet<String>,
            captured: &mut HashSet<&'a str>,
        ) {
            match formula {
                Formula::Instant(_) => (),
                Formula::LogOp(LogOp::Bin(BinLogOp { phi, psi, .. })) => {
                    rec(phi, free, captured);
                    rec(psi, free, captured);
                }
                Formula::LogOp(LogOp::Not(phi)) => rec(phi, free, captured),
                Formula::Rel(Rel { terms, .. }) => {
                    terms.iter().for_each(|term| term.free_vars(free, captured))
                }
                Formula::Quantified(Quantifier { var, phi, .. }) => {
                    captured.insert(var);
                    rec(phi, free, captured);
                    captured.remove(var.as_str());
                }
            }
        }
        rec(self, &mut free, &mut captured);
        free
    }

    pub(crate) fn close_universally(&mut self) {
        let mut vars = self.used_vars();
        let free_vars = self.free_vars();
        for free in free_vars {
            // Introduce fresh not to introduce name collisions on other paths.
            let fresh = fresh_var(&mut vars);
            let mut formula = std::mem::replace(self, Formula::Instant(Instant::F));
            formula.rename(&free, &fresh);
            *self = Self::Quantified(Quantifier {
                kind: QuantifierKind::Forall,
                var: fresh,
                phi: Box::new(formula),
            })
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::first_order::parser::Parser;

    const DRINKER_PARADOX: &str =
        r#"Exists "x" (Implies (Rel "D" [Var "x"]) (Forall "y" (Rel "D" [Var "y"])))"#;
    impl Formula {
        pub(crate) fn drinker_paradox() -> Self {
            let parser = Parser::new().unwrap();
            parser.parse(DRINKER_PARADOX).unwrap()
        }
    }
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
                "Quantifier" => Self::parse_quantifier(tree).map(Formula::Quantified),
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

        fn parse_log_op(tree: &ParseTree) -> Result<FOLogOp> {
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

        fn parse_not(tree: &ParseTree) -> Result<FOLogOp> {
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

        fn parse_bin_log_op(tree: &ParseTree) -> Result<FOBinLogOp> {
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
                if let Ok(rhs_cont) = extract_rhs::<4>(t_seq) {
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
        use crate::first_order::parser::Parser;
        use crate::tests::for_each_external_test;

        use super::*;
        use Instant::{F, T};
        use QuantifierKind::Exists;

        #[test]
        fn correct_parsing_to_formula() {
            let parser = Parser::new().unwrap();

            {
                let formulas = [
                    ("T", Formula::Instant(T)),
                    (
                        "And (T) (Exists \"xD\" (F))",
                        Formula::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::And,
                            phi: Box::new(Formula::Instant(T)),
                            psi: Box::new(Formula::Quantified(Quantifier {
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
