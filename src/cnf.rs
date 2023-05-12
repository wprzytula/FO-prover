use std::fmt::{Display, Write};

use crate::{
    formula::Instant,
    nnf::{NNFLogOpKind, NNFPropagated, NNFPropagatedInner, NNFVarKind, NNF},
    proposition::{MissingValuation, Valuation},
};

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(non_camel_case_types)]
#[allow(clippy::upper_case_acronyms)]
pub(crate) struct CNF(pub(crate) Vec<CNFClause>);

impl Display for CNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('[')?;
        let mut iter = self.0.iter();
        if let Some(clause) = iter.next() {
            clause.fmt(f)?;
        }
        for clause in iter {
            f.write_str(" and ")?;
            clause.fmt(f)?;
        }
        f.write_char(']')?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub(crate) struct CNFClause(pub(crate) Vec<Literal>);

impl Display for CNFClause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('(')?;
        let mut iter = self.0.iter();
        if let Some(literal) = iter.next() {
            literal.fmt(f)?;
        }
        for literal in iter {
            f.write_str(" or ")?;
            literal.fmt(f)?;
        }
        f.write_char(')')?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Literal {
    Pos(String),
    Neg(String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(self, Literal::Neg(_)) {
            f.write_char('~')?;
        }
        f.write_str(self.var())
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(match Ord::cmp(self.var(), other.var()) {
            std::cmp::Ordering::Equal => match (self, other) {
                (Literal::Pos(_), Literal::Pos(_)) | (Literal::Neg(_), Literal::Neg(_)) => {
                    std::cmp::Ordering::Equal
                }
                (Literal::Pos(_), Literal::Neg(_)) => std::cmp::Ordering::Less,
                (Literal::Neg(_), Literal::Pos(_)) => std::cmp::Ordering::Greater,
            },
            otherwise => otherwise,
        })
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        PartialOrd::partial_cmp(self, other).unwrap()
    }
}

impl Literal {
    pub(crate) fn is_opposite(&self, other: &Self) -> bool {
        match (self, other) {
            (Literal::Neg(_), Literal::Neg(_)) | (Literal::Pos(_), Literal::Pos(_)) => false,
            (Literal::Pos(s1), Literal::Neg(s2)) | (Literal::Neg(s1), Literal::Pos(s2)) => s1 == s2,
        }
    }

    pub(crate) fn make_opposite(&mut self) {
        *self = match self {
            Literal::Pos(s) => Literal::Neg(std::mem::take(s)),
            Literal::Neg(s) => Literal::Pos(std::mem::take(s)),
        }
    }
    pub(crate) fn into_var(self) -> String {
        match self {
            Literal::Pos(s) | Literal::Neg(s) => s,
        }
    }
    pub(crate) fn var(&self) -> &String {
        match self {
            Literal::Pos(s) | Literal::Neg(s) => s,
        }
    }
    pub(crate) fn has_var(&self, var: &str) -> bool {
        self.var() == var
    }

    pub(crate) fn evaluate<'a>(
        &'a self,
        valuation: &'a Valuation,
    ) -> Result<bool, MissingValuation<'a>> {
        let var_value = valuation
            .get(self.var().as_str())
            .copied()
            .ok_or(MissingValuation(self.var()))?;
        Ok(match self {
            Literal::Pos(_) => var_value,
            Literal::Neg(_) => !var_value,
        })
    }
}

impl CNF {
    pub(crate) fn evaluate<'a>(
        &'a self,
        valuation: &'a Valuation,
    ) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(true, |acc, res| res.map(|val| acc && val))
    }

    pub(crate) fn equivalent(propagated: &NNFPropagated) -> Self {
        fn rec(nnf: &NNFPropagatedInner) -> Vec<CNFClause> {
            match nnf {
                NNFPropagatedInner::Var(kind, s) => vec![CNFClause(vec![match kind {
                    NNFVarKind::Pos => Literal::Pos(s.clone()),
                    NNFVarKind::Neg => Literal::Neg(s.clone()),
                }])],
                NNFPropagatedInner::LogOp { kind, phi, psi } => {
                    let phi_vec = rec(phi);
                    let psi_vec = rec(psi);
                    match kind {
                        // go (φ `And` ψ) = go φ ++ go ψ
                        NNFLogOpKind::And => {
                            let mut vec = phi_vec;
                            vec.append(&mut rec(psi));
                            vec
                        }
                        // go (φ `Or` ψ) = [as ++ bs | as <- go φ, bs <- go ψ]
                        NNFLogOpKind::Or => phi_vec
                            .iter()
                            .map(|phi_clause| {
                                psi_vec.iter().map(|psi_clause| {
                                    CNFClause(
                                        phi_clause
                                            .0
                                            .iter()
                                            .chain(psi_clause.0.iter())
                                            .cloned()
                                            .collect::<Vec<_>>(),
                                    )
                                })
                            })
                            .flatten()
                            .collect::<Vec<_>>(),
                    }
                }
            }
        }
        match propagated {
            NNFPropagated::Instant(i) => match i {
                Instant::T => {
                    // Trivial SAT CNF
                    CNF(vec![])
                }
                Instant::F => {
                    // Trivial UNSAT CNF
                    CNF(vec![CNFClause(vec![])])
                }
            },
            NNFPropagated::Inner(ref inner) => CNF(rec(inner)),
        }
    }

    #[allow(non_snake_case)]
    pub(crate) fn ECNF(prop: NNF) -> Self {
        let propagated = prop.propagate_constants();
        // let vars =
        todo!()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn contains_empty_clause(&self) -> bool {
        self.0.iter().any(CNFClause::is_empty)
    }
}

impl CNFClause {
    pub(crate) fn sort(&mut self) {
        self.0.sort_unstable();
    }

    pub(crate) fn evaluate<'a>(
        &'a self,
        valuation: &'a Valuation,
    ) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(false, |acc, res| res.map(|val| acc || val))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn one_literal_clause(&self) -> Option<&Literal> {
        (self.0.len() == 1).then(|| &self.0[0])
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    use quickcheck::Arbitrary;

    impl Arbitrary for CNF {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let cnf = loop {
                let cnf: Vec<CNFClause> = Arbitrary::arbitrary(g);
                if cnf.len() < 10 {
                    break cnf;
                }
            };
            Self(cnf)
        }
    }

    impl Arbitrary for CNFClause {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let clause = loop {
                let clause: Vec<Literal> = Arbitrary::arbitrary(g);
                if clause.len() < 10 {
                    break clause;
                }
            };
            Self(clause)
        }
    }

    impl Arbitrary for Literal {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let mut s = String::new();
            s.push(char::arbitrary(g));

            if bool::arbitrary(g) {
                Self::Pos(s)
            } else {
                Self::Neg(s)
            }
        }
    }

    impl CNF {
        pub(crate) fn into_set(self) -> BTreeSet<BTreeSet<Literal>> {
            self.0
                .into_iter()
                .map(|clause| clause.0.into_iter().collect())
                .collect()
        }
    }
}
