use std::{
    collections::HashSet,
    fmt::{Display, Write},
};

use crate::{
    formula::{BinLogOp, BinLogOpKind, Instant, LogOp},
    nnf::{NNFLogOpKind, NNFPropagated, NNFPropagatedInner, NNFVarKind, NNF},
    proposition::{fresh_var, Evaluable, MissingValuation, Proposition, UsedVars, Valuation},
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
}

impl Evaluable for Literal {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        let var_value = valuation.valuate(self.var())?;
        Ok(match self {
            Literal::Pos(_) => var_value,
            Literal::Neg(_) => !var_value,
        })
    }
}

impl UsedVars for CNF {
    fn used_vars<'a, S: From<&'a String> + Eq + std::hash::Hash>(&'a self) -> HashSet<S> {
        self.all_literals().map(Into::into).collect()
    }
}

impl CNF {
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
                            .flat_map(|phi_clause| {
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
    pub(crate) fn ECNF(propagated: NNFPropagated) -> Self {
        let mut vars = HashSet::from_iter(propagated.vars().into_iter().map(ToOwned::to_owned));

        fn include_subformula<'a>(
            ecnf: &mut Vec<CNFClause>,
            propagated: &'a NNFPropagatedInner,
            vars: &mut HashSet<String>,
        ) -> Literal {
            match propagated {
                NNFPropagatedInner::Var(k, s) => match k {
                    NNFVarKind::Pos => Literal::Pos(s.clone()),
                    NNFVarKind::Neg => Literal::Neg(s.clone()),
                },
                NNFPropagatedInner::LogOp { kind, phi, psi } => {
                    fn proposition_for_literal(lit: Literal) -> Proposition {
                        match lit {
                            Literal::Pos(s) => {
                                Proposition::LogOp(LogOp::Not(Box::new(Proposition::Var(s))))
                            }
                            Literal::Neg(s) => Proposition::Var(s),
                        }
                    }
                    let phi = include_subformula(ecnf, phi, vars);
                    let psi = include_subformula(ecnf, psi, vars);
                    let theta = fresh_var(vars);
                    // ψi ≡ qi ↔ (qj#qk)
                    let formula = Proposition::LogOp(LogOp::Bin(BinLogOp {
                        kind: BinLogOpKind::Iff,
                        phi: Box::new(Proposition::Var(theta.clone())),
                        psi: Box::new(Proposition::LogOp(LogOp::Bin(BinLogOp {
                            kind: match kind {
                                NNFLogOpKind::And => BinLogOpKind::And,
                                NNFLogOpKind::Or => BinLogOpKind::Or,
                            },
                            phi: Box::new(proposition_for_literal(phi)),
                            psi: Box::new(proposition_for_literal(psi)),
                        }))),
                    }));
                    let formula_nnf = NNF::new(formula).propagate_constants();
                    let formula_cnf = CNF::equivalent(&formula_nnf);
                    ecnf.extend(formula_cnf.0.into_iter());

                    Literal::Pos(theta)
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
            NNFPropagated::Inner(inner) => {
                let mut ecnf: Vec<CNFClause> = vec![];
                include_subformula(&mut ecnf, &inner, &mut vars);

                CNF(ecnf)
            }
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn contains_empty_clause(&self) -> bool {
        self.0.iter().any(CNFClause::is_empty)
    }

    pub(crate) fn all_literals(&self) -> impl Iterator<Item = &String> {
        self.0
            .iter()
            .flat_map(|clause| clause.0.iter().map(Literal::var))
    }
}

impl Evaluable for CNF {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(true, |acc, res| res.map(|val| acc && val))
    }
}

impl CNFClause {
    pub(crate) fn sort(&mut self) {
        self.0.sort_unstable();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn one_literal_clause(&self) -> Option<&Literal> {
        (self.0.len() == 1).then(|| &self.0[0])
    }
}

impl Evaluable for CNFClause {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(false, |acc, res| res.map(|val| acc || val))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{
        nnf::NNF,
        proposition::{tests::randomly_check_equivalence, Proposition},
        sat_solver::tests::equisatisfiable,
    };

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

    #[test]
    fn cnf_preserves_logical_equivalence() {
        {
            // SAT
            let prop = Proposition::example_sat();
            let nnf = NNF::new(prop);
            let nnf_propagated = nnf.clone().propagate_constants();
            let cnf = CNF::equivalent(&nnf_propagated);
            assert!(randomly_check_equivalence(&nnf_propagated, &cnf));
        }
        {
            // UNSAT
            let prop = Proposition::example_unsat();
            let nnf = NNF::new(prop);
            let nnf_propagated = nnf.clone().propagate_constants();
            let cnf = CNF::equivalent(&nnf_propagated);
            assert!(randomly_check_equivalence(&nnf_propagated, &cnf));
        }
    }

    #[test]
    fn ecnf_preserves_equisatisfiability() {
        {
            // trivial SAT
            let trivial_nnf = NNFPropagated::Instant(Instant::T);
            let ecnf = CNF::ECNF(trivial_nnf.clone());
            assert!(equisatisfiable(&ecnf, &trivial_nnf));
        }
        {
            // trivial UNSAT
            let trivial_nnf = NNFPropagated::Instant(Instant::F);
            let ecnf = CNF::ECNF(trivial_nnf.clone());
            assert!(equisatisfiable(&ecnf, &trivial_nnf));
        }
        {
            // simple UNSAT
            let simple_nnf = NNFPropagated::Inner(NNFPropagatedInner::LogOp {
                kind: NNFLogOpKind::And,
                phi: Box::new(NNFPropagatedInner::Var(NNFVarKind::Pos, "p".to_owned())),
                psi: Box::new(NNFPropagatedInner::Var(NNFVarKind::Neg, "p".to_owned())),
            });
            let ecnf = CNF::ECNF(simple_nnf.clone());
            assert!(equisatisfiable(&ecnf, &simple_nnf));
        }
        {
            // SAT
            let prop = Proposition::example_sat();
            let nnf = NNF::new(prop);
            let nnf_propagated = nnf.clone().propagate_constants();
            let ecnf = CNF::ECNF(nnf_propagated.clone());
            assert!(equisatisfiable(&ecnf, &nnf_propagated));
        }
        {
            // UNSAT
            let prop = Proposition::example_unsat();
            let nnf = NNF::new(prop);
            let nnf_propagated = nnf.clone().propagate_constants();
            let ecnf = CNF::ECNF(nnf_propagated.clone());
            assert!(equisatisfiable(&ecnf, &nnf_propagated));
        }
    }
}
