use crate::proposition::{CNFClause, Literal, CNF};

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SolverJudgement {
    Satisfiable,
    Unsatisfiable,
}

pub(crate) struct SatSolver;
