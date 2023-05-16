use super::formula::Formula;

pub(crate) struct TautologyDecider;

impl TautologyDecider {
    pub(crate) fn is_tautology(mut formula: Formula) -> bool {
        // 1. Convert ¬ϕ to an equisatisfiable Skolem normal form ψ ≡ ∀x1 , . . . , xn · ξ,
        // with ξ quantifier-free.
        formula.close_universally();
        let negated_formula = Formula::not(formula);
        let nnf = negated_formula.into_nnf();
        let nnf_propagated = nnf.propagate_constants();
        let _skolemised = nnf_propagated.skolemise();

        // 2. Verify that ψ is unsatisfiable: By Herbrand’s theorem, it suffices to find n-
        // tuples of ground terms ū1 , . . . , ūm (i.e., elements of the Herbrand universe)
        // s.t.
        // ξ[x̄ 7→ ū1 ] ∧ · · · ∧ ξ[x̄ 7→ ūm ]
        // is unsatisfiable.

        true // FIXME
    }
}
