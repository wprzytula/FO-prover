use std::collections::{HashMap, HashSet};

use crate::proposition::{CNFClause, Literal, CNF};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SolverJudgement {
    Satisfiable,
    Unsatisfiable,
}

type Valuation<'a> = HashMap<&'a str, bool>;

impl Literal {
    fn evaluate<'a>(&'a self, valuation: &'a Valuation) -> Result<bool, MissingValuation<'a>> {
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

impl CNFClause {
    fn evaluate<'a>(&'a self, valuation: &'a Valuation) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(false, |acc, res| res.map(|val| acc || val))
    }

    fn contains_literal_with_var(&self, p: &str) -> bool {
        self.0.iter().find(|literal| literal.var() == p).is_some()
    }
}

#[derive(Debug)]
struct MissingValuation<'a>(&'a str);

impl CNF {
    fn all_literals<'a>(&'a self) -> impl Iterator<Item = &'a String> {
        self.0
            .iter()
            .map(|clause| clause.0.iter().map(Literal::var))
            .flatten()
    }

    fn evaluate<'a>(&'a self, valuation: &'a Valuation) -> Result<bool, MissingValuation<'a>> {
        self.0
            .iter()
            .map(|literal| literal.evaluate(valuation))
            .try_fold(true, |acc, res| res.map(|val| acc && val))
    }

    fn try_trivially_solve(&self) -> Option<SolverJudgement> {
        if self.is_empty() {
            Some(SolverJudgement::Satisfiable)
        } else if self.contains_empty_clause() {
            Some(SolverJudgement::Unsatisfiable)
        } else {
            None
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
            while let Some(clause) = clause_iter.next() {
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

        self.0.extend(
            poses
                .iter()
                .map(|clause_with_p_pos| {
                    negs.iter().map(|clause_with_p_neg| {
                        CNFClause(Vec::from_iter(
                            clause_with_p_pos
                                .0
                                .iter()
                                .chain(clause_with_p_neg.0.iter())
                                .cloned(),
                        ))
                    })
                })
                .flatten(),
        )
    }
}

pub(crate) struct SatSolver;

impl SatSolver {
    pub(crate) fn solve_by_truth_tables(cnf: &CNF) -> (SolverJudgement, Option<Valuation>) {
        let mut truth_table = Valuation::new();
        let vars = Vec::from_iter(HashSet::<&String>::from_iter(cnf.all_literals()).into_iter());

        fn valuate_next_var<'a: 'b, 'b>(
            cnf: &CNF,
            truth_table: &mut Valuation<'b>,
            remaining_vars: &[&'a String],
        ) -> Option<()> {
            if let Some((next_var, remaining_vars)) = remaining_vars.split_first() {
                truth_table.insert(next_var, true);
                if let Some(satisfying_valuation) =
                    valuate_next_var(cnf, truth_table, remaining_vars)
                {
                    return Some(satisfying_valuation);
                }
                truth_table.insert(next_var, false);
                valuate_next_var(cnf, truth_table, remaining_vars)
            } else {
                cnf.evaluate(truth_table).unwrap().then_some(())
            }
        }

        match valuate_next_var(&cnf, &mut truth_table, &vars) {
            Some(_) => (SolverJudgement::Satisfiable, Some(truth_table.clone())),
            None => (SolverJudgement::Unsatisfiable, None),
        }
    }

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
}

#[cfg(test)]
mod tests {
    use quickcheck::TestResult;

    use crate::proposition::{CNFClause, Literal, CNF};

    use super::{SatSolver, SolverJudgement};

    #[test]
    fn best_var_is_chosen_for_resolution() {
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
    fn sat_solver_is_correct() {
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

    #[quickcheck]
    #[ignore = "Too long"]
    fn quicktest_sat_solver(cnf: CNF) -> TestResult {
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
