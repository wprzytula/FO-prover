use std::{
    collections::HashMap,
    fmt::{Display, Write},
    vec,
};

use crate::formula::{Instant, LogOp};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Proposition {
    Instant(Instant),
    LogOp(LogOp),
    Var(String),
}

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

impl CNF {
    #[allow(non_snake_case)]
    pub(crate) fn ECNF(prop: &Proposition) -> Self {
        todo!()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn contains_empty_clause(&self) -> bool {
        self.0.iter().any(CNFClause::is_empty)
    }

    // A SAT clause is tautological if it contains some literal both positively and negatively.
    /// Removes tautological clauses.
    pub(crate) fn remove_tautologies(&mut self) -> bool {
        let clauses_before = self.0.len();
        self.0.retain_mut(|clause| !clause.remove_tautologies());
        let clauses_after = self.0.len();
        clauses_before > clauses_after
    }

    // A one-literal clause is a clause containing only one literal L. If a CNF contains a one-literal clause L,
    // say a positive literal L = p, then p must necessarily be true in any satisfying assignment (if any exists).
    // Consequently, we can remove all clauses containing p positively, and we can remove all occurrences
    // of the opposite literal ~p from all the other clauses. The same idea can be (dually) applied if L = ~p
    // is a one-literal clause.
    /// Transforms a given CNF into an equisatisfiable one without one-literal clauses.
    pub(crate) fn one_literal(&mut self) -> bool {
        let mut applied = false;
        loop {
            let mut single_literals = self
                .0
                .iter()
                .filter_map(CNFClause::one_literal_clause)
                .cloned()
                .collect::<Vec<_>>();

            if single_literals.is_empty() {
                return applied; // No more applications of the one literal rule possible.
            } else {
                applied = true;
            }
            single_literals.sort();
            {
                // check for contradicting single literal clauses
                let mut iter = single_literals.iter();
                let mut prev = iter.next().unwrap();
                for literal in iter {
                    if literal.is_opposite(prev) {
                        // The formula is unsatisfiable, so return a trivial such.
                        self.0.clear();
                        self.0.push(CNFClause(vec![]));
                        return applied;
                    }
                    prev = literal;
                }
            }

            // Remove clauses containing literals that must be true.
            self.0.retain(|clause| {
                clause
                    .0
                    .iter()
                    .all(|literal| single_literals.binary_search(literal).is_err())
            });

            let negated_single_literals = {
                single_literals.iter_mut().for_each(Literal::make_opposite);
                single_literals
            };

            // Remove literals that must be false.
            for clause in self.0.iter_mut() {
                clause
                    .0
                    .retain(|literal| negated_single_literals.binary_search(literal).is_err())
            }
        }
    }

    // Affirmative-negative rule
    // If a literal appears either only positively, or only negatively, then all clauses
    // where it occurs can be removed, preserving satisfiability.
    /// Removes all clauses containing literals which globally appear only positively, or only negatively.
    pub(crate) fn affirmative_negative(&mut self) -> bool {
        #[derive(Debug, Clone, Copy)]
        enum Appears {
            Positively,
            Negatively,
            Both,
        }
        impl Appears {
            fn positively(&mut self) {
                *self = match *self {
                    Appears::Negatively => Appears::Both,
                    a => a,
                }
            }
            fn negatively(&mut self) {
                *self = match *self {
                    Appears::Positively => Appears::Both,
                    a => a,
                }
            }
            fn only_pos_or_only_neg(&self) -> bool {
                matches!(self, Appears::Negatively | Appears::Positively)
            }
        }
        let mut literals: HashMap<String, Appears> = HashMap::new();
        let mut applied = false;
        loop {
            literals.clear();
            for clause in self.0.iter() {
                for literal in clause.0.iter() {
                    match literal {
                        Literal::Pos(s) => literals
                            .entry(s.clone())
                            .and_modify(Appears::positively)
                            .or_insert(Appears::Positively),
                        Literal::Neg(s) => literals
                            .entry(s.clone())
                            .and_modify(Appears::negatively)
                            .or_insert(Appears::Negatively),
                    };
                }
            }
            if !literals.values().any(Appears::only_pos_or_only_neg) {
                // Can no longer apply this rule.
                return applied;
            } else {
                applied = true;
            }

            self.0.retain(|clause| {
                clause
                    .0
                    .iter()
                    .all(|literal| !literals.get(literal.var()).unwrap().only_pos_or_only_neg())
            })
        }
    }
}

impl CNFClause {
    fn sort(&mut self) {
        self.0.sort_unstable();
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn remove_tautologies(&mut self) -> bool {
        self.sort();
        let literals_before = self.0.len();
        let mut nubbed = Vec::new();
        let mut last_pos: Option<String> = None;
        let mut last_neg: Option<String> = None;

        fn should_flush(
            new: &String,
            last_pos: &Option<String>,
            last_neg: &Option<String>,
        ) -> bool {
            for old in [last_pos, last_neg].into_iter().flatten() {
                assert!(old <= new);
                if old < new {
                    return true;
                }
            }
            false
        }

        fn flush(
            nubbed: &mut Vec<Literal>,
            last_pos: &mut Option<String>,
            last_neg: &mut Option<String>,
        ) {
            match (last_pos.take(), last_neg.take()) {
                (None, None) => (),
                (None, Some(neg)) => nubbed.push(Literal::Neg(neg)),
                (Some(pos), None) => nubbed.push(Literal::Pos(pos)),
                (Some(pos), Some(neg)) => match Ord::cmp(&pos, &neg) {
                    std::cmp::Ordering::Equal => {
                        // removed tautological literal
                    }
                    std::cmp::Ordering::Less => {
                        nubbed.push(Literal::Pos(pos));
                        nubbed.push(Literal::Neg(neg));
                    }
                    std::cmp::Ordering::Greater => {
                        nubbed.push(Literal::Neg(neg));
                        nubbed.push(Literal::Pos(pos));
                    }
                },
            }
        }

        for name in self.0.drain(..) {
            let var = name.var();
            if should_flush(var, &last_pos, &last_neg) {
                flush(&mut nubbed, &mut last_pos, &mut last_neg);
            }
            match name {
                Literal::Pos(s) => {
                    if last_pos.is_none() {
                        last_pos = Some(s);
                    }
                }
                Literal::Neg(s) => {
                    if last_neg.is_none() {
                        last_neg = Some(s);
                    }
                }
            }
        }
        flush(&mut nubbed, &mut last_pos, &mut last_neg);
        std::mem::swap(&mut nubbed, &mut self.0);

        let literals_after = self.0.len();
        assert!(literals_after <= literals_before);
        literals_after < literals_before
    }

    fn one_literal_clause(&self) -> Option<&Literal> {
        (self.0.len() == 1).then(|| &self.0[0])
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashSet};

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
    fn test_literal_order() {
        let tests = [(
            vec![
                Literal::Pos("x".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Pos("x".to_owned()),
                Literal::Neg("z".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Neg("x".to_owned()),
            ],
            vec![
                Literal::Pos("x".to_owned()),
                Literal::Pos("x".to_owned()),
                Literal::Neg("x".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Neg("z".to_owned()),
            ],
        )];
        for (test, expected) in tests {
            let mut clause = CNFClause(test);
            let expected = CNFClause(expected);
            clause.sort();
            assert_eq!(clause, expected);
        }
    }

    #[test]
    fn test_remove_tautologies() {
        let tests = [(
            vec![
                Literal::Pos("x".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Pos("x".to_owned()),
                Literal::Neg("z".to_owned()),
                Literal::Pos("y".to_owned()),
                Literal::Neg("x".to_owned()),
            ],
            vec![Literal::Pos("y".to_owned()), Literal::Neg("z".to_owned())],
        )];
        for (test, expected) in tests {
            let mut clause = CNFClause(test);
            let expected = CNFClause(expected);
            clause.remove_tautologies();
            assert_eq!(clause, expected);
        }
    }

    #[test]
    fn test_one_literal() {
        let tests = [
            (
                // contradictory one
                vec![
                    CNFClause(vec![Literal::Pos("x".to_owned())]),
                    CNFClause(vec![
                        Literal::Pos("x".to_owned()),
                        Literal::Pos("h".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_owned()),
                        Literal::Pos("y".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("z".to_owned()),
                        Literal::Neg("y".to_owned()),
                        Literal::Neg("x".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("z".to_owned()),
                        Literal::Pos("w".to_owned()),
                        Literal::Neg("g".to_owned()),
                    ]),
                    CNFClause(vec![Literal::Pos("z".to_owned())]),
                    CNFClause(vec![Literal::Pos("z".to_owned())]),
                ],
                vec![CNFClause(vec![])],
            ),
            (
                // All the clauses will disappear
                vec![
                    CNFClause(vec![Literal::Pos("x".to_owned())]),
                    CNFClause(vec![
                        Literal::Pos("x".to_owned()),
                        Literal::Pos("h".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_owned()),
                        Literal::Pos("y".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("z".to_owned()),
                        Literal::Neg("y".to_owned()),
                        Literal::Neg("x".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("z".to_owned()),
                        Literal::Pos("w".to_owned()),
                        Literal::Neg("y".to_owned()),
                    ]),
                ],
                vec![],
            ),
            (
                vec![
                    CNFClause(vec![Literal::Pos("x".to_owned())]),
                    CNFClause(vec![
                        Literal::Pos("x".to_owned()),
                        Literal::Pos("h".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_owned()),
                        Literal::Pos("y".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("z".to_owned()),
                        Literal::Neg("y".to_owned()),
                        Literal::Neg("x".to_owned()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("z".to_owned()),
                        Literal::Pos("w".to_owned()),
                        Literal::Pos("g".to_owned()),
                        Literal::Neg("y".to_owned()),
                    ]),
                ],
                vec![CNFClause(vec![
                    Literal::Pos("w".to_owned()),
                    Literal::Pos("g".to_owned()),
                ])],
            ),
        ];
        for (test, expected) in tests {
            let mut cnf = CNF(test);
            cnf.one_literal();
            let expected = CNF(expected);
            assert_eq!(cnf, expected);
        }
    }

    impl CNF {
        fn all_literals_both_pos_and_neg(&self) -> bool {
            let mut negs = HashSet::new();
            let mut poss = HashSet::new();
            for clause in self.0.iter() {
                for literal in clause.0.iter() {
                    match literal {
                        Literal::Pos(s) => poss.insert(s),
                        Literal::Neg(s) => negs.insert(s),
                    };
                }
            }
            negs.len() == poss.len() && negs.iter().all(|literal| poss.contains(literal))
        }
    }

    #[quickcheck]
    fn test_affirmative_negative(mut cnf: CNF) -> bool {
        cnf.affirmative_negative();
        cnf.all_literals_both_pos_and_neg()
    }
}
