use std::{collections::HashMap, fmt::Display};

use log::{debug, info};

use crate::{
    first_order::herbrand::GroundTerm,
    propositional::{
        cnf::CNF,
        sat_solver::{
            SatSolver,
            SolverJudgement::{Satisfiable, Unsatisfiable},
        },
    },
};

use super::{formula::Formula, pnf::SkolemisedFormula};

pub(crate) struct TautologyDecider;

impl TautologyDecider {
    pub(crate) fn is_tautology(mut formula: Formula) -> bool {
        // 1. Convert ¬ϕ to an equisatisfiable Skolem normal form ψ ≡ ∀x1 , . . . , xn · ξ,
        // with ξ quantifier-free.
        formula.close_universally();
        info!("Formula closed universally: {}", &formula);
        let negated_formula = Formula::not(formula);
        info!("Formula negated: {}", &negated_formula);
        let nnf = negated_formula.into_nnf();
        info!("Formula in NNF: {}", &nnf);
        let nnf_propagated = nnf.propagate_constants();
        info!("Formula in NNFPropagated: {}", &nnf_propagated);
        let skolemised = nnf_propagated.skolemise();
        info!("Formula after Skolemisation: {}", &skolemised);
        let signature = skolemised.signature();
        let vars = match skolemised {
            SkolemisedFormula::Instant(i) => return i.into_bool(),
            SkolemisedFormula::Inner {
                ref universally_quantified_vars,
                ..
            } => universally_quantified_vars,
        };
        if vars.is_empty() {
            info!("Detected trivial case: no universally quantified variables.");
            // Just check satisfiability.
            let grounded_formula = skolemised.ground(&HashMap::new());
            // let grounded_cnf = CNF::ECNF(grounded_formula);
            let grounded_cnf = CNF::equivalent(&grounded_formula);
            return match SatSolver::solve_by_dpll(grounded_cnf) {
                Satisfiable => false,
                Unsatisfiable => true,
            };
        }

        info!("Detected nontrivial case: some universally quantified variables.");

        // 2. Verify that ψ is unsatisfiable: By Herbrand’s theorem, it suffices to find n-
        // tuples of ground terms ū1 , . . . , ūm (i.e., elements of the Herbrand universe)
        // s.t.
        // ξ[x̄ 7→ ū1 ] ∧ · · · ∧ ξ[x̄ 7→ ūm ]
        // is unsatisfiable.

        let is_universe_finite = signature.herbrands_universe_is_finite();
        let herbrands_universe = signature.herbrands_universe();
        info!("Signature: {:#?}", signature);

        if !is_universe_finite {
            info!(
                "Signature contains functional symbols, so Herbrand's universe is infinite. \
                   Being non-tautology is not provable."
            );
        } else {
            info!(
                "Signature does not contain functional symbols, so Herbrand's universe is finite. \
                   Being non-tautology is provable."
            );
        }

        let mut offending_conjunction = CNF::empty_satisfiable();

        let mut terms = Vec::new();

        let mut selector = Selector::new_for_n_vars(vars.len());
        let mut var_to_term = HashMap::new();

        for herbrand_term in herbrands_universe {
            info!(
                "Extending term set with Herbrand's term: {}",
                &herbrand_term
            );
            terms.push(herbrand_term);
            loop {
                selector.extract_mapping(&mut var_to_term, vars, &terms);
                info!("Extracted mapping: {}", MappingDisplay(&var_to_term));
                let grounded_formula = skolemised.ground(&var_to_term);
                debug!(
                    "Grounded formula\n{}, yielding\n{}",
                    &skolemised, &grounded_formula
                );
                let grounded_cnf = CNF::equivalent(&grounded_formula);
                // let grounded_cnf = CNF::ECNF(grounded_formula);
                offending_conjunction.append_clauses(grounded_cnf);
                // debug!("Conjunction: {}", &offending_conjunction);

                match SatSolver::solve_by_dpll(offending_conjunction.clone()) {
                    Satisfiable => (),
                    Unsatisfiable => {
                        info!(
                            "Found unsatisfiable conjunction (len={}). Concluding tautology.",
                            offending_conjunction.len_clauses(),
                        );
                        // debug!("Offending conjunction: {:#?}", &offending_conjunction);

                        return true;
                    }
                }

                // move to next configuration or break if depleted
                if selector.next_config(&terms).is_none() {
                    break;
                }
            }
        }

        // If the universe is finite and depleted, this means that the formula is not a tautology.
        info!("The Herbrand's universe was depleted, so we conclude that the formula is not a tautology");
        false
    }
}

struct Selector(Vec<usize>);
impl Selector {
    fn new_for_n_vars(n: usize) -> Self {
        Self(vec![0usize; n])
    }

    fn next_config(&mut self, terms: &Vec<GroundTerm>) -> Option<()> {
        assert!(!terms.is_empty());
        let newest_term_idx = terms.len() - 1;
        // increment units
        if self.0[0] + 1 < terms.len() {
            self.0[0] += 1;
            Some(())
        } else {
            self.0[0] = 0;
            // handle carry
            let mut carry_handled = false;
            for i in 1..self.0.len() {
                if self.0[i] + 1 < terms.len() {
                    self.0[i] += 1;
                    carry_handled = true;
                    break;
                } else {
                    self.0[i] = 0;
                    // next column in next iteration
                }
            }
            if carry_handled {
                if self.0.contains(&newest_term_idx) {
                Some(())
                } else {
                    debug!("Skipping already covered case: {:?}", self.0);
                    self.next_config(terms)
                }
            } else {
                None
            }
        }
    }

    fn extract_mapping<'a, 'b: 'a>(
        &self,
        var_to_term: &mut HashMap<&'a str, GroundTerm>,
        vars: &'b [String],
        terms: &[GroundTerm],
    ) {
        var_to_term.clear();
        for (var_idx, term_idx) in self.0.iter().copied().enumerate() {
            var_to_term.insert(vars[var_idx].as_str(), terms[term_idx].clone());
        }
    }
}

struct DebugWithDisplay<'a, D: Display>(&'a D);
impl<D: Display> std::fmt::Debug for DebugWithDisplay<'_, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <D as Display>::fmt(self.0, f)
    }
}

struct MappingDisplay<'a, D1: Display, D2: Display>(&'a HashMap<D1, D2>);
impl<D1: Display, D2: Display> Display for MappingDisplay<'_, D1, D2> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(
                self.0
                    .iter()
                    .map(|(k, v)| (DebugWithDisplay(k), DebugWithDisplay(v))),
            )
            .finish()
    }
}
