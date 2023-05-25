use std::collections::HashMap;

use log::{debug, trace};

use super::cnf::{CNFClause, Literal, CNF};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SolverJudgement {
    Satisfiable,
    Unsatisfiable,
}

impl CNFClause {
    fn contains_literal_with_var(&self, p: &str) -> bool {
        self.0.iter().any(|literal| literal.var() == p)
    }

    // Removes duplicate literals as a side effect.
    // Returns whether the clause is a tautology (contains both negative and positive
    // literal of same variable) and hence can be removed.
    fn remove_duplicate_literals_and_check_if_tautology(&mut self) -> bool {
        self.sort();
        let literals_before = self.0.len();
        let mut nubbed = Vec::new();
        let mut last_pos: Option<String> = None;
        let mut last_neg: Option<String> = None;

        fn found_tautology(
            new: &Literal,
            last_pos: &Option<String>,
            last_neg: &Option<String>,
        ) -> bool {
            match new {
                Literal::Pos(s) => Some(s) == last_neg.as_ref(),
                Literal::Neg(s) => Some(s) == last_pos.as_ref(),
            }
        }

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
                        unreachable!("This case should have been handled in found_tautology()")
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

        for literal in self.0.drain(..) {
            if found_tautology(&literal, &last_pos, &last_neg) {
                trace!("Found tautology of literal {}", &literal);
                return true;
            }
            let var = literal.var();
            if should_flush(var, &last_pos, &last_neg) {
                flush(&mut nubbed, &mut last_pos, &mut last_neg);
            }
            match literal {
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
        trace!(
            "Removed {} literals from the clause",
            literals_before - literals_after
        );
        false
    }
}

impl CNF {
    fn try_trivially_solve(&self) -> Option<SolverJudgement> {
        if self.is_empty() {
            Some(SolverJudgement::Satisfiable)
        } else if self.contains_empty_clause() {
            Some(SolverJudgement::Unsatisfiable)
        } else {
            None
        }
    }

    // A SAT clause is tautological if it contains some literal both positively and negatively.
    /// Removes tautological clauses.
    pub(crate) fn remove_tautologies(&mut self) -> bool {
        let clauses_before = self.0.len();
        self.0
            .retain_mut(|clause| !clause.remove_duplicate_literals_and_check_if_tautology());
        let clauses_after = self.0.len();
        debug!(
            "Clauses before: {}, after: {} (removed {})",
            clauses_before,
            clauses_after,
            clauses_before - clauses_after
        );
        clauses_before > clauses_after
    }

    // A one-literal clause is a clause containing only one literal L. If a CNF contains a one-literal clause L,
    // say a positive literal L = p, then p must necessarily be true in any satisfying assignment (if any exists).
    // Consequently, we can remove all clauses containing p positively, and we can remove all occurrences
    // of the opposite literal ~p from all the other clauses. The same idea can be (dually) applied if L = ~p
    // is a one-literal clause.
    /// Transforms a given CNF into an equisatisfiable one without one-literal clauses.
    fn one_literal(&mut self) -> bool {
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
    fn affirmative_negative(&mut self) -> bool {
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

    fn choose_var_for_resolution(&self) -> &str {
        // We want to choose literals with min_literal(max_clause(clause_len)).
        let (p, _min_max_len_clause) = self
            .all_literals()
            .map(|p| {
                let max_len_clause = self
                    .0
                    .iter()
                    .filter(|clause| clause.contains_literal_with_var(p))
                    .max_by_key(|clause| clause.0.len())
                    .unwrap();
                (p, max_len_clause)
            })
            .min_by_key(|(_, clause)| clause.0.len())
            .unwrap();

        p
    }

    fn resolve(&mut self, p: &str) {
        // Put all affected clauses (those containing p) at the end of vec.
        self.0.sort_by(|clause1, clause2| {
            match (
                clause1.contains_literal_with_var(p),
                clause2.contains_literal_with_var(p),
            ) {
                (true, true) | (false, false) => std::cmp::Ordering::Equal,
                (true, false) => std::cmp::Ordering::Greater,
                (false, true) => std::cmp::Ordering::Less,
            }
        });

        #[cfg(debug_assertions)]
        {
            // sanity check
            let mut clause_iter = self.0.iter();
            for clause in clause_iter.by_ref() {
                if clause.contains_literal_with_var(p) {
                    break;
                }
            }
            for clause in clause_iter {
                debug_assert!(clause.contains_literal_with_var(p));
            }
        }

        // TODO: preserve poses and negs allocations across calls
        let mut poses = Vec::new();
        let mut negs = Vec::new();
        let idx_of_first_literal_containing_p = self
            .0
            .partition_point(|clause| !clause.contains_literal_with_var(p));

        for mut clause in self.0.drain(idx_of_first_literal_containing_p..) {
            let container: &mut Vec<CNFClause> =
                match clause.0.iter().find(|literal| literal.has_var(p)).unwrap() {
                    Literal::Pos(_) => &mut poses,
                    Literal::Neg(_) => &mut negs,
                };
            clause.0.retain(|literal| !literal.has_var(p));
            container.push(clause);
        }

        self.0.extend(poses.iter().flat_map(|clause_with_p_pos| {
            negs.iter().map(|clause_with_p_neg| {
                CNFClause(Vec::from_iter(
                    clause_with_p_pos
                        .0
                        .iter()
                        .chain(clause_with_p_neg.0.iter())
                        .cloned(),
                ))
            })
        }))
    }

    fn with_explicit_literal(mut self, literal: Literal) -> Self {
        self.0.push(CNFClause(vec![literal]));
        self
    }
}

pub(crate) struct SatSolver;

impl SatSolver {
    pub(crate) fn solve_by_dp(mut cnf: CNF) -> SolverJudgement {
        loop {
            let mut apply_1_5_again = true;
            while apply_1_5_again {
                apply_1_5_again = false;
                // 1. If the CNF is empty, then it is satisfiable.
                // 2. If the CNF contains an empty clause, then it is not satisfiable.
                if let Some(judgement) = cnf.try_trivially_solve() {
                    return judgement;
                }
                // 3. Remove all tautological clauses.
                apply_1_5_again |= cnf.remove_tautologies();

                // 4. Apply the one-literal rule until it can no longer be applied.
                apply_1_5_again |= cnf.one_literal();

                // 5. Apply the affirmative-negative rule until it can no longer be applied.
                apply_1_5_again |= cnf.affirmative_negative();
            }
            // 6. Only when 3., 4., and 5. above can no longer be applied, apply resolution, and start again from the beginning.
            let chosen_var = cnf.choose_var_for_resolution().to_owned();
            cnf.resolve(&chosen_var);
        }
    }

    pub(crate) fn solve_by_dpll(mut cnf: CNF) -> SolverJudgement {
        let mut apply_1_5_again = true;
        while apply_1_5_again {
            apply_1_5_again = false;
            // 1. If the CNF is empty, then it is satisfiable.
            // 2. If the CNF contains an empty clause, then it is not satisfiable.
            if let Some(judgement) = cnf.try_trivially_solve() {
                return judgement;
            }
            // 3. Remove all tautological clauses.
            apply_1_5_again |= cnf.remove_tautologies();

            // 4. Apply the one-literal rule until it can no longer be applied.
            apply_1_5_again |= cnf.one_literal();

            // 5. Apply the affirmative-negative rule until it can no longer be applied.
            apply_1_5_again |= cnf.affirmative_negative();
        }
        // 6. Only when 3., 4., and 5. above can no longer be applied, apply resolution, and start again from the beginning.
        let chosen_var = cnf.choose_var_for_resolution().to_owned();

        // Resolve positively
        if let SolverJudgement::Satisfiable = Self::solve_by_dpll(
            cnf.clone()
                .with_explicit_literal(Literal::Pos(chosen_var.clone())),
        ) {
            return SolverJudgement::Satisfiable;
        }

        // Else resolve negatively
        Self::solve_by_dpll(cnf.with_explicit_literal(Literal::Neg(chosen_var)))
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashSet;

    use quickcheck::TestResult;

    use crate::{
        first_order::formula::Instant,
        init_logger,
        propositional::{
            cnf::{CNFClause, Literal, CNF},
            nnf::NNF,
            proposition::{Evaluable, Proposition, UsedVars},
        },
    };

    use super::*;

    impl SatSolver {
        pub(crate) fn solve_by_truth_tables(
            formula: &(impl Evaluable + UsedVars),
        ) -> (SolverJudgement, Option<HashMap<&str, bool>>) {
            let mut truth_table = HashMap::new();
            let vars = Vec::from_iter(formula.used_vars().into_iter());

            fn valuate_next_var<'a: 'b, 'b>(
                formula: &(impl Evaluable + UsedVars),
                truth_table: &'b mut HashMap<&'a str, bool>,
                remaining_vars: &[&'a String],
            ) -> Option<()> {
                if let Some((next_var, remaining_vars)) = remaining_vars.split_first() {
                    truth_table.insert(next_var, true);
                    if let Some(satisfying_valuation) =
                        valuate_next_var(formula, truth_table, remaining_vars)
                    {
                        return Some(satisfying_valuation);
                    }
                    truth_table.insert(next_var, false);
                    valuate_next_var(formula, truth_table, remaining_vars)
                } else {
                    formula.evaluate(truth_table).unwrap().then_some(())
                }
            }

            match valuate_next_var(formula, &mut truth_table, &vars) {
                Some(_) => (SolverJudgement::Satisfiable, Some(truth_table.clone())),
                None => (SolverJudgement::Unsatisfiable, None),
            }
        }
    }

    #[test]
    fn test_literal_order() {
        init_logger();
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
        init_logger();
        let tests = [
            (
                vec![
                    Literal::Pos("x".to_owned()),
                    Literal::Pos("y".to_owned()),
                    Literal::Pos("x".to_owned()),
                    Literal::Neg("z".to_owned()),
                    Literal::Pos("y".to_owned()),
                    Literal::Neg("x".to_owned()),
                ],
                None,
            ),
            (
                vec![
                    Literal::Pos("x".to_owned()),
                    Literal::Neg("z".to_owned()),
                    Literal::Pos("y".to_owned()),
                    Literal::Pos("x".to_owned()),
                    Literal::Neg("z".to_owned()),
                    Literal::Pos("y".to_owned()),
                ],
                Some(vec![
                    Literal::Pos("x".to_owned()),
                    Literal::Pos("y".to_owned()),
                    Literal::Neg("z".to_owned()),
                ]),
            ),
        ];
        for (test, expected) in tests {
            let mut clause = CNFClause(test);
            let tautology = clause.remove_duplicate_literals_and_check_if_tautology();
            assert_eq!(tautology, expected.is_none());
            if let Some(expected_clause) = expected {
                let expected = CNFClause(expected_clause);
                assert_eq!(clause, expected);
            }
        }
    }

    #[test]
    fn test_one_literal() {
        init_logger();
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
    #[ignore = "Too long"]
    fn quicktest_affirmative_negative(mut cnf: CNF) -> bool {
        init_logger();
        cnf.affirmative_negative();
        cnf.all_literals_both_pos_and_neg()
    }

    #[test]
    fn best_var_is_chosen_for_resolution() {
        init_logger();
        // (p \/ r1), (p \/ ~r2), (~r1 \/ ~r4 \/ r5), (r2 \/ r4 \/ ~r5), (~p \/ r4)
        let cnf = CNF(vec![
            CNFClause(vec![
                Literal::Pos("p".to_owned()),
                Literal::Pos("r1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("r2".to_owned()),
                Literal::Pos("p".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("r1".to_owned()),
                Literal::Neg("r4".to_owned()),
                Literal::Pos("r5".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("r2".to_owned()),
                Literal::Pos("r4".to_owned()),
                Literal::Neg("r5".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("p".to_owned()),
                Literal::Pos("r4".to_owned()),
            ]),
        ]);
        assert_eq!(cnf.choose_var_for_resolution(), "p");
    }

    #[test]
    fn resolution_one_case() {
        init_logger();
        // (p \/ r1), (p \/ ~r2), (p \/ r3), (~p \/ ~q1), (~p \/ q2), rem
        let mut cnf = CNF(vec![
            CNFClause(vec![
                Literal::Pos("p".to_owned()),
                Literal::Pos("r1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("r2".to_owned()),
                Literal::Pos("p".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("x".to_owned()),
                Literal::Neg("y".to_owned()),
                Literal::Neg("z".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("p".to_owned()),
                Literal::Neg("q1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("p".to_owned()),
                Literal::Pos("r3".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("p".to_owned()),
                Literal::Pos("q2".to_owned()),
            ]),
        ]);

        // rem, (r1 \/ ~q1), (r1 \/ q2), (~r2 \/ ~q1), (~r2,\/ q2), (r3 \/ ~q1), (r3,\/ q2)
        let expected = CNF(vec![
            CNFClause(vec![
                Literal::Neg("x".to_owned()),
                Literal::Neg("y".to_owned()),
                Literal::Neg("z".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("r1".to_owned()),
                Literal::Neg("q1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("r1".to_owned()),
                Literal::Pos("q2".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("r2".to_owned()),
                Literal::Neg("q1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Neg("r2".to_owned()),
                Literal::Pos("q2".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("r3".to_owned()),
                Literal::Neg("q1".to_owned()),
            ]),
            CNFClause(vec![
                Literal::Pos("r3".to_owned()),
                Literal::Pos("q2".to_owned()),
            ]),
        ]);

        cnf.resolve("p");
        assert_eq!(cnf.into_set(), expected.into_set());
    }

    #[test]
    fn test_truth_tables() {
        init_logger();
        let trivial_unsat = NNF::Instant(Instant::F).propagate_constants();
        let trivial_sat = NNF::Instant(Instant::T).propagate_constants();
        assert_eq!(
            SatSolver::solve_by_truth_tables(&trivial_unsat).0,
            SolverJudgement::Unsatisfiable
        );
        assert_eq!(
            SatSolver::solve_by_truth_tables(&trivial_sat).0,
            SolverJudgement::Satisfiable
        );

        assert_eq!(
            SatSolver::solve_by_truth_tables(&Proposition::example_unsat()).0,
            SolverJudgement::Unsatisfiable
        );
        assert_eq!(
            SatSolver::solve_by_truth_tables(&Proposition::example_sat()).0,
            SolverJudgement::Satisfiable
        );
    }

    pub(crate) fn equisatisfiable(
        phi: &(impl Evaluable + UsedVars),
        psi: &(impl Evaluable + UsedVars),
    ) -> bool {
        SatSolver::solve_by_truth_tables(phi).0 == SatSolver::solve_by_truth_tables(psi).0
    }

    #[test]
    fn test_equisatisfiable() {
        init_logger();
        let unsat = NNF::Instant(Instant::F).propagate_constants();
        let sat = NNF::Instant(Instant::T).propagate_constants();
        assert!(!equisatisfiable(&sat, &unsat));
        assert!(equisatisfiable(&sat, &sat));
        assert!(equisatisfiable(&unsat, &unsat));
    }

    #[test]
    fn sat_solver_is_correct() {
        init_logger();
        let tests = [
            (
                CNF(vec![
                    CNFClause(vec![
                        Literal::Pos("x".to_string()),
                        Literal::Pos("y".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_string()),
                        Literal::Pos("z".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("y".to_string()),
                        Literal::Neg("z".to_string()),
                    ]),
                ]),
                SolverJudgement::Satisfiable,
            ),
            (
                CNF(vec![
                    CNFClause(vec![
                        Literal::Pos("x".to_string()),
                        Literal::Pos("y".to_string()),
                        Literal::Neg("z".to_string()),
                        Literal::Neg("w".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_string()),
                        Literal::Neg("y".to_string()),
                        Literal::Pos("z".to_string()),
                        Literal::Neg("w".to_string()),
                        Literal::Pos("v".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("x".to_string()),
                        Literal::Pos("y".to_string()),
                        Literal::Neg("v".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_string()),
                        Literal::Neg("y".to_string()),
                        Literal::Neg("z".to_string()),
                        Literal::Neg("w".to_string()),
                        Literal::Pos("v".to_string()),
                        Literal::Pos("u".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("x".to_string()),
                        Literal::Neg("y".to_string()),
                        Literal::Pos("z".to_string()),
                        Literal::Neg("u".to_string()),
                        Literal::Pos("v".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("x".to_string()),
                        Literal::Pos("z".to_string()),
                        Literal::Neg("w".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("v".to_string()),
                        Literal::Pos("y".to_string()),
                        Literal::Neg("u".to_string()),
                        Literal::Neg("z".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("v".to_string()),
                        Literal::Neg("w".to_string()),
                        Literal::Pos("z".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("x".to_string()),
                        Literal::Pos("u".to_string()),
                        Literal::Pos("v".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("y".to_string()),
                        Literal::Pos("w".to_string()),
                    ]),
                ]),
                SolverJudgement::Satisfiable,
            ),
            (
                CNF(vec![
                    CNFClause(vec![
                        Literal::Pos("C1".to_string()),
                        Literal::Pos("C2".to_string()),
                        Literal::Pos("C3".to_string()),
                        Literal::Pos("C4".to_string()),
                        Literal::Pos("C5".to_string()),
                        Literal::Pos("C6".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("C1".to_string()),
                        Literal::Neg("C2".to_string()),
                        Literal::Pos("C3".to_string()),
                        Literal::Pos("C4".to_string()),
                        Literal::Pos("C5".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("C2".to_string()),
                        Literal::Neg("C3".to_string()),
                        Literal::Pos("C4".to_string()),
                        Literal::Pos("C6".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("C3".to_string()),
                        Literal::Neg("C4".to_string()),
                        Literal::Pos("C5".to_string()),
                        Literal::Pos("C6".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("C1".to_string()),
                        Literal::Pos("C2".to_string()),
                        Literal::Pos("C4".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("C2".to_string()),
                        Literal::Pos("C3".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("C4".to_string()),
                        Literal::Neg("C5".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("C2".to_string()),
                        Literal::Neg("C3".to_string()),
                        Literal::Pos("C4".to_string()),
                        Literal::Pos("C5".to_string()),
                        Literal::Neg("C6".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Pos("C1".to_string()),
                        Literal::Neg("C3".to_string()),
                        Literal::Pos("C4".to_string()),
                        Literal::Pos("C5".to_string()),
                    ]),
                    CNFClause(vec![
                        Literal::Neg("C4".to_string()),
                        Literal::Pos("C6".to_string()),
                    ]),
                ]),
                SolverJudgement::Satisfiable,
            ),
        ];
        for (cnf, expected_judgement) in tests {
            let (truth_tables_judgement, maybe_valuation) = SatSolver::solve_by_truth_tables(&cnf);
            assert_eq!(
                expected_judgement, truth_tables_judgement,
                "Valuation: {:#?}",
                maybe_valuation
            );

            let dp_judgement = SatSolver::solve_by_dp(cnf);
            assert_eq!(dp_judgement, expected_judgement);
        }
    }

    #[test]
    fn sat_solver_integration_test() {
        init_logger();
        let tests = Proposition::tautologies()
            .into_iter()
            .zip(std::iter::repeat_with(|| SolverJudgement::Satisfiable))
            .chain(
                Proposition::unsats()
                    .zip(std::iter::repeat_with(|| SolverJudgement::Unsatisfiable)),
            );
        for ((name, proposition), expected_judgement) in tests {
            let (truth_tables_judgement, maybe_valuation) =
                SatSolver::solve_by_truth_tables(&proposition);
            assert_eq!(
                expected_judgement, truth_tables_judgement,
                "EXPECTED judgement differs from truth tables. Proposition: {}\n{:#?}\nSatisfying valuation:{:#?}",
                name,
                &proposition,
                maybe_valuation,
            );

            let nnf = NNF::new(proposition.clone()).propagate_constants();
            let cnf = CNF::ECNF(nnf);

            let dp_judgement = SatSolver::solve_by_dp(cnf.clone());
            assert_eq!(dp_judgement, expected_judgement);

            let dpll_judgement = SatSolver::solve_by_dpll(cnf);
            assert_eq!(dpll_judgement, expected_judgement);
        }
    }

    #[quickcheck]
    #[ignore = "Too long"]
    fn quicktest_sat_solver(cnf: CNF) -> TestResult {
        init_logger();
        if cnf.0.len() > 10 || cnf.0.iter().map(|clause| clause.0.len()).max() > Some(5) {
            println!("QuickCheck: discarding {}", cnf);
            return TestResult::discard();
        }
        println!("QuickChecking: {}", cnf);
        if SatSolver::solve_by_truth_tables(&cnf).0 == SatSolver::solve_by_dp(cnf) {
            println!("QuickCheck passed");
            TestResult::passed()
        } else {
            TestResult::failed()
        }
    }
}
