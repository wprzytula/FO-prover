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

}



