use std::collections::HashMap;

use crate::propositional::{
    cnf::CNF,
    sat_solver::{
        SatSolver,
        SolverJudgement::{Satisfiable, Unsatisfiable},
    },
};

use super::{formula::Formula, pnf::SkolemisedFormula};

pub(crate) struct TautologyDecider;

impl TautologyDecider {
    pub(crate) fn is_tautology(mut formula: Formula) -> bool {
        // 1. Convert ¬ϕ to an equisatisfiable Skolem normal form ψ ≡ ∀x1 , . . . , xn · ξ,
        // with ξ quantifier-free.
        formula.close_universally();
        let negated_formula = Formula::not(formula);
        let nnf = negated_formula.into_nnf();
        let nnf_propagated = nnf.propagate_constants();
        let skolemised = nnf_propagated.skolemise();
        let signature = skolemised.signature();
        let vars = match skolemised {
            SkolemisedFormula::Instant(i) => return i.into_bool(),
            SkolemisedFormula::Inner {
                ref universally_quantified_vars,
                ..
            } => universally_quantified_vars,
        };
        if vars.is_empty() {
            // Just check satisfiability.
            let grounded_formula = skolemised.ground(&HashMap::new());
            let grounded_cnf = CNF::ECNF(grounded_formula);
            return match SatSolver::solve_by_dp(grounded_cnf) {
                Satisfiable => false,
                Unsatisfiable => true,
            };
        }

        // 2. Verify that ψ is unsatisfiable: By Herbrand’s theorem, it suffices to find n-
        // tuples of ground terms ū1 , . . . , ūm (i.e., elements of the Herbrand universe)
        // s.t.
        // ξ[x̄ 7→ ū1 ] ∧ · · · ∧ ξ[x̄ 7→ ūm ]
        // is unsatisfiable.

        let herbrands_universe = signature.herbrands_universe();
        let mut offending_conjunction = CNF::empty_satisfiable();
        for herbrand_term in herbrands_universe {
            let mapping = vars
                .iter()
                .map(|var| (var.as_str(), herbrand_term.clone()))
                .collect();
            let grounded_formula = skolemised.ground(&mapping);
            let grounded_cnf = CNF::ECNF(grounded_formula);
            offending_conjunction.append_clauses(grounded_cnf);

            match SatSolver::solve_by_dp(offending_conjunction.clone()) {
                Satisfiable => (),
                Unsatisfiable => return true,
            }
        }

        // If the universe is finite and depleted, this means that the formula is not a tautology.
        false
    }
}
