use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Write},
    vec,
};

use itertools::Itertools;
use log::{debug, info, trace};

use crate::{
    first_order::{formula::Rel, pnf::NNFQuantifierFreeInner},
    propositional::nnf::{NNFPropagated, NNFPropagatedInner, NNFVarKind},
};

use super::{formula::Term, nnf::NNFRelKind, pnf::SkolemisedFormula};

type Arity = usize;

#[derive(Debug)]
pub(crate) struct Signature {
    pub(crate) per_arity: HashMap<Arity, HashSet<String>>,
}

impl Term {
    fn add_to_signature(&self, signature: &mut Signature) {
        match self {
            Term::Var(_) => (),
            Term::Fun(name, terms) => {
                signature
                    .per_arity
                    .entry(terms.len())
                    .or_default()
                    .insert(name.clone());
            }
        }
    }
}

impl SkolemisedFormula {
    pub(crate) fn signature(&self) -> Signature {
        let mut signature = Signature::empty();

        fn rec(signature: &mut Signature, ksi: &NNFQuantifierFreeInner) {
            match ksi {
                NNFQuantifierFreeInner::LogOp { phi, psi, .. } => {
                    rec(signature, phi);
                    rec(signature, psi);
                }
                NNFQuantifierFreeInner::Rel {
                    rel: Rel { terms, .. },
                    ..
                } => terms
                    .iter()
                    .for_each(|term| term.add_to_signature(signature)),
            }
        }

        match self {
            SkolemisedFormula::Instant(_) => (),
            SkolemisedFormula::Inner { ksi, .. } => rec(&mut signature, ksi),
        }

        // If there are no constants in the universe, add a dummy one.
        // FIXME: fresh fun name
        signature
            .per_arity
            .entry(0)
            .or_insert_with(|| std::iter::once("c".to_owned()).collect());

        signature
    }
}

impl Signature {
    fn empty() -> Self {
        Self {
            per_arity: HashMap::new(),
        }
    }

    fn constants(&self) -> Option<&HashSet<String>> {
        self.per_arity.get(&0)
    }

    fn arity_iter(&self) -> impl Iterator<Item = (Arity, String)> + Clone + '_ {
        self.per_arity
            .iter()
            .filter(|(arity, _)| **arity > 0)
            .flat_map(|(arity, fns)| fns.iter().map(|func| (*arity, func.clone())))
    }

    pub(crate) fn herbrands_universe_is_finite(&self) -> bool {
        self.per_arity.len() == 1
    }

    pub(crate) fn herbrands_universe(&self) -> impl Iterator<Item = GroundTerm> + '_ {
        HerbrandsUniverseIter::new(self, self.arity_iter()).unique()
    }
}

struct LowerLevelElemSelector {
    arity: usize,
    idcs: Vec<usize>,
    lower_level_terms_len: usize,
    depleted: bool,
}

impl LowerLevelElemSelector {
    fn new(arity: Arity, lower_level_terms: &Vec<GroundTerm>) -> Self {
        trace!(
            "Selector::new(arity: {}, lower_level_terms: {}",
            arity,
            GroundTermVecDisplay(lower_level_terms)
        );
        assert!(arity > 0);
        assert!(!lower_level_terms.is_empty());
        Self {
            arity,
            idcs: vec![0; arity],
            lower_level_terms_len: lower_level_terms.len(),
            depleted: false,
        }
    }

    fn select_next(&mut self, lower_level_terms: &Vec<GroundTerm>) -> Option<Vec<GroundTerm>> {
        assert_eq!(lower_level_terms.len(), self.lower_level_terms_len);
        if self.depleted {
            None
        } else {
            let res = Some({
                let mut variation = Vec::with_capacity(self.arity);
                for lower_level_term_idx in self.idcs.iter().copied() {
                    variation.push(lower_level_terms[lower_level_term_idx].clone());
                }
                debug_assert!(variation.len() == self.arity);
                trace!("Selector: selected {}", GroundTermVecDisplay(&variation));
                variation
            });
            self.increment();
            res
        }
    }

    fn increment(&mut self) {
        // increment units
        if self.idcs[0] + 1 < self.lower_level_terms_len {
            self.idcs[0] += 1;
        } else {
            self.idcs[0] = 0;
            // handle carry
            let mut carry_handled = false;
            for i in 1..self.arity {
                if self.idcs[i] + 1 < self.lower_level_terms_len {
                    self.idcs[i] += 1;
                    carry_handled = true;
                    break;
                } else {
                    self.idcs[i] = 0;
                    // next column in next iteration
                }
            }
            if !carry_handled {
                self.depleted = true;
            }
        }
        if self.depleted {
            trace!("Selector got depleted.");
        } else {
            trace!("Incremented Selector to: {:?}", &self.idcs);
        }
    }
}

enum HerbrandsUniverseIterState<ArityIter: Iterator<Item = (Arity, String)> + Clone> {
    Consts {
        next_const_idx: usize,
        consts: Vec<GroundTerm>,
    },
    Depleted,
    NextLevelTerms {
        arity_iter: ArityIter,
        curr_fn: (Arity, String),
        curr_fn_selector: LowerLevelElemSelector,
        lower_level_terms: Vec<GroundTerm>,
        this_level_terms: Vec<GroundTerm>,
    },
}

struct HerbrandsUniverseIter<'sig, ArityIter: Iterator<Item = (Arity, String)> + Clone> {
    signature: &'sig Signature,
    arity_iter_backup: ArityIter,
    state: HerbrandsUniverseIterState<ArityIter>,
}

impl<'sig, ArityIter: Iterator<Item = (Arity, String)> + Clone>
    HerbrandsUniverseIter<'sig, ArityIter>
{
    fn new(signature: &'sig Signature, arity_iter: ArityIter) -> Self {
        Self {
            signature,
            state: HerbrandsUniverseIterState::Consts {
                next_const_idx: 0,
                consts: Vec::new(),
            },
            arity_iter_backup: arity_iter,
        }
    }
}

impl<'sig, ArityIter: Iterator<Item = (Arity, String)> + Clone> Iterator
    for HerbrandsUniverseIter<'sig, ArityIter>
{
    type Item = GroundTerm;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.state {
            HerbrandsUniverseIterState::Depleted => None,
            HerbrandsUniverseIterState::Consts {
                next_const_idx,
                consts,
            } => {
                let constants = self.signature.constants().unwrap();
                if let Some(constant) = constants.iter().nth(*next_const_idx) {
                    *next_const_idx += 1;
                    let constant_term = GroundTerm::constant(constant.clone());
                    consts.push(constant_term.clone());
                    debug!("Herbrand's Universe: yielding constant {}", constant_term);
                    Some(constant_term)
                } else if self.signature.per_arity.len() > 1
                /*Functional symbols also present*/
                {
                    info!("Herbrand's Universe: proceeding to the functions level. Appending constants: {}\n", GroundTermVecDisplay(consts));
                    let mut arity_iter = self.arity_iter_backup.clone();
                    let curr_fn = arity_iter.next().unwrap();
                    debug!(
                        "Herbrand's Universe: moving to another symbol: {}/{}",
                        curr_fn.1, curr_fn.0
                    );
                    let curr_fn_selector = LowerLevelElemSelector::new(curr_fn.0, consts);
                    self.state = HerbrandsUniverseIterState::NextLevelTerms {
                        arity_iter,
                        this_level_terms: Vec::new(),
                        lower_level_terms: std::mem::take(consts),
                        curr_fn,
                        curr_fn_selector,
                    };
                    self.next()
                } else {
                    self.state = HerbrandsUniverseIterState::Depleted;
                    None
                }
            }
            HerbrandsUniverseIterState::NextLevelTerms {
                arity_iter,
                lower_level_terms,
                this_level_terms,
                curr_fn,
                curr_fn_selector,
            } => {
                if let Some(selected) = curr_fn_selector.select_next(lower_level_terms) {
                    let res = GroundTerm {
                        fun_name: curr_fn.1.clone(),
                        ground_terms: selected,
                    };
                    this_level_terms.push(res.clone());
                    debug!("Herbrand's Universe: yielding term {}", res);
                    Some(res)
                } else {
                    // Current symbol is depleted; try fetching another.
                    if let Some(new_fn) = arity_iter.next() {
                        // Set selector for the next symbol.
                        debug!(
                            "Herbrand's Universe: moving to another symbol: {}/{}",
                            new_fn.1, new_fn.0
                        );
                        *curr_fn_selector =
                            LowerLevelElemSelector::new(new_fn.0, lower_level_terms);
                        *curr_fn = new_fn;
                        self.next()
                    } else {
                        // All symbol depleted. Proceed to the next level.
                        info!("Herbrand's Universe: proceeding to the next level. Appending terms: {}\n", GroundTermVecDisplay(this_level_terms));
                        lower_level_terms.append(this_level_terms);
                        *arity_iter = self.arity_iter_backup.clone();
                        *curr_fn = arity_iter.next().unwrap();
                        debug!(
                            "Herbrand's Universe: moving to another symbol: {}/{}",
                            curr_fn.1, curr_fn.0
                        );
                        *curr_fn_selector =
                            LowerLevelElemSelector::new(curr_fn.0, lower_level_terms);

                        self.next()
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GroundTerm {
    fun_name: String,
    ground_terms: Vec<GroundTerm>,
}

pub(crate) fn display_term_name_with_terms(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    terms: &[impl Display],
) -> std::fmt::Result {
    f.write_str(name)?;
    let mut iter = terms.iter();
    if let Some(term) = iter.next() {
        f.write_char('(')?;
        write!(f, "{}", term)?;
        for term in iter {
            f.write_str(", ")?;
            write!(f, "{}", term)?;
        }
        f.write_char(')')?
    }
    Ok(())
}

pub(crate) struct TermDisplayer<'a, D: Display> {
    pub(crate) name: &'a str,
    pub(crate) terms: &'a [D],
}
impl<D: Display> Display for TermDisplayer<'_, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_name_with_terms(f, self.name, self.terms)
    }
}

impl GroundTerm {
    fn constant(name: String) -> Self {
        Self {
            fun_name: name,
            ground_terms: Vec::new(),
        }
    }
}

impl Display for GroundTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_name_with_terms(f, &self.fun_name, &self.ground_terms)
    }
}

struct DebugWithDisplay<'a, D: Display>(&'a D);
impl<D: Display> std::fmt::Debug for DebugWithDisplay<'_, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <D as Display>::fmt(self.0, f)
    }
}

struct GroundTermVecDisplay<'a>(&'a Vec<GroundTerm>);
impl Display for GroundTermVecDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0.iter().map(DebugWithDisplay))
            .finish()
    }
}

struct GroundRel<'a> {
    name: &'a str,
    ground_terms: Vec<GroundTerm>,
}

impl GroundRel<'_> {
    fn encode(&self) -> String {
        self.to_string()
    }
}

impl Display for GroundRel<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_term_name_with_terms(f, self.name, &self.ground_terms)
    }
}

impl SkolemisedFormula {
    // Grounds the formula, replacing vars (keys) with ground terms (values).
    pub(crate) fn ground(&self, mapping: &HashMap<&str, GroundTerm>) -> NNFPropagated {
        match self {
            SkolemisedFormula::Instant(i) => NNFPropagated::Instant(*i),
            SkolemisedFormula::Inner { ksi, .. } => NNFPropagated::Inner(ksi.ground(mapping)),
        }
    }
}

impl Term {
    // Grounds the term, replacing vars (keys) with ground terms (values).
    fn ground(&self, mapping: &HashMap<&str, GroundTerm>) -> GroundTerm {
        match self {
            Term::Var(var) => mapping.get(var.as_str()).unwrap().clone(),
            Term::Fun(name, terms) => GroundTerm {
                fun_name: name.clone(),
                ground_terms: terms.iter().map(|term| term.ground(mapping)).collect(),
            },
        }
    }
}

impl Rel {
    // Grounds the relation, replacing vars (keys) with ground terms (values).
    fn ground(&self, mapping: &HashMap<&str, GroundTerm>) -> GroundRel<'_> {
        GroundRel {
            name: &self.name,
            ground_terms: self.terms.iter().map(|term| term.ground(mapping)).collect(),
        }
    }
}

impl NNFQuantifierFreeInner {
    // Grounds the formula, replacing vars (keys) with ground terms (values).
    fn ground(&self, mapping: &HashMap<&str, GroundTerm>) -> NNFPropagatedInner {
        match self {
            NNFQuantifierFreeInner::LogOp { kind, phi, psi } => NNFPropagatedInner::LogOp {
                kind: *kind,
                phi: Box::new(phi.ground(mapping)),
                psi: Box::new(psi.ground(mapping)),
            },
            NNFQuantifierFreeInner::Rel { kind, rel } => NNFPropagatedInner::Var(
                match kind {
                    NNFRelKind::Pos => NNFVarKind::Pos,
                    NNFRelKind::Neg => NNFVarKind::Neg,
                },
                rel.ground(mapping).encode(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn herbrands_universe() {
        #[track_caller]
        fn assert_contains(term: &str, universe: &Vec<String>) {
            assert!(universe.contains(&term.to_owned()));
        }
        {
            // max arity 1
            let fns = [(0, &["c"][..]), (1, &["f", "g"])];
            let sig = Signature {
                per_arity: HashMap::from_iter(fns.into_iter().map(|(arity, names)| {
                    (
                        arity,
                        names.into_iter().map(|str| (*str).to_owned()).collect(),
                    )
                })),
            };
            let expected_terms = ["f(c)", "g(f(g(f(c))))"];
            let universe = Vec::from_iter(
                sig.herbrands_universe()
                    .take(100)
                    .map(|term| term.to_string()),
            );
            for expected_term in expected_terms {
                assert_contains(expected_term, &universe);
            }
        }
        {
            let fns = [
                (0, &["c", "d"][..]),
                (1, &["f", "g"]),
                (2, &["dist", "pow"]),
            ];
            let sig = Signature {
                per_arity: HashMap::from_iter(fns.into_iter().map(|(arity, names)| {
                    (
                        arity,
                        names.into_iter().map(|str| (*str).to_owned()).collect(),
                    )
                })),
            };

            let expected_terms = [
                "f(c)",
                "dist(c, c)",
                "pow(dist(d, d), c)",
                "pow(dist(d, c), f(c))",
                "f(f(c))",
            ];
            let universe = Vec::from_iter(
                sig.herbrands_universe()
                    .take(10000)
                    .map(|term| term.to_string()),
            );

            for expected_term in expected_terms {
                assert_contains(expected_term, &universe);
            }
        }
    }
}
