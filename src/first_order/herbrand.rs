use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Write},
    vec,
};

use crate::{
    first_order::{formula::Rel, pnf::NNFQuantifierFreeInner},
    propositional::nnf::{NNFPropagated, NNFPropagatedInner, NNFVarKind},
};

use super::{formula::Term, nnf::NNFRelKind, pnf::SkolemisedFormula};

type Arity = usize;

#[derive(Debug)]
struct Signature {
    per_name: HashMap<String, Arity>,
    per_arity: HashMap<Arity, HashSet<String>>,
    empty_set: HashSet<String>,
}

impl Term {
    fn add_to_signature(&self, signature: &mut Signature) {
        match self {
            Term::Var(_) => (),
            Term::Fun(name, terms) => {
                signature.per_name.insert(name.clone(), terms.len());
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
    fn signature(&self) -> Signature {
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
            per_name: HashMap::new(),
            per_arity: HashMap::new(),
            empty_set: HashSet::new(),
        }
    }

    fn constants(&self) -> Option<&HashSet<String>> {
        self.per_name
            .iter()
            .filter_map(|(name, arity)| (*arity == 0).then_some(name));
        self.per_arity.get(&0)
    }

    fn herbrands_universe_iter<'a>(&'a self) -> HerbrandsUniverseIter<'a> {
        HerbrandsUniverseIter::new(self)
    }

    fn herbrands_universe<'a>(&'a self) -> impl Iterator<Item = GroundTerm> + 'a {
        let constants = self
            .constants()
            .unwrap()
            .iter()
            .map(|constant| GroundTerm::constant(constant.clone()));

        let single_applications = self
            .constants()
            .unwrap()
            .iter()
            .map(|constant| {
                let unary_fns = self.per_arity.get(&1).unwrap_or(&self.empty_set);
                unary_fns.iter().map(|unary_fn| GroundTerm {
                    fun_name: unary_fn.clone(),
                    ground_terms: vec![GroundTerm::constant(constant.clone())],
                })
            })
            .flatten();

        let applications = (0..)
            .into_iter()
            .map(move |n| {
                single_applications.clone().map(move |mut term| {
                    for _ in 0..n {
                        term = GroundTerm {
                            fun_name: term.fun_name.clone(),
                            ground_terms: vec![term],
                        }
                    }
                    term
                })
            })
            .flatten();

        constants.chain(applications)
    }
}

enum HerbrandsUniverseIterState<'sig> {
    Consts {
        next_const_idx: usize,
        consts: Vec<GroundTerm>,
    },
    Depleted,
    NextLevelTerms {
        next_term_idx: usize,
        arity_one_iter: std::collections::hash_set::Iter<'sig, String>,
        lower_level_terms: Vec<GroundTerm>,
        this_level_terms: Vec<GroundTerm>,
    },
}

struct HerbrandsUniverseIter<'sig> {
    signature: &'sig Signature,
    state: HerbrandsUniverseIterState<'sig>,
}

impl<'sig> HerbrandsUniverseIter<'sig> {
    fn new(signature: &'sig Signature) -> Self {
        Self {
            signature,
            state: HerbrandsUniverseIterState::Consts {
                next_const_idx: 0,
                consts: Vec::new(),
            },
        }
    }
}

impl<'sig> Iterator for HerbrandsUniverseIter<'sig> {
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
                    Some(constant_term)
                } else if self.signature.per_arity.len() > 1
                /*Functional symbols also present*/
                {
                    self.state = HerbrandsUniverseIterState::NextLevelTerms {
                        next_term_idx: 0,
                        arity_one_iter: self
                            .signature
                            .per_arity
                            .get(&1)
                            .unwrap_or(&self.signature.empty_set)
                            .iter(),
                        lower_level_terms: std::mem::take(consts),
                        this_level_terms: Vec::new(),
                    };
                    self.next()
                } else {
                    self.state = HerbrandsUniverseIterState::Depleted;
                    None
                }
            }
            HerbrandsUniverseIterState::NextLevelTerms {
                arity_one_iter,
                next_term_idx,
                lower_level_terms,
                this_level_terms,
            } => {
                // Arity 1
                if let Some(lower_level_term) = lower_level_terms.get(*next_term_idx) {
                    if let Some(fn_arity_one) = arity_one_iter.next() {
                        let this_level_term = GroundTerm {
                            fun_name: fn_arity_one.clone(),
                            ground_terms: vec![lower_level_term.clone()],
                        };
                        this_level_terms.push(this_level_term.clone());
                        Some(this_level_term)
                    } else {
                        *arity_one_iter = self
                            .signature
                            .per_arity
                            .get(&1)
                            .unwrap_or(&self.signature.empty_set)
                            .iter();
                        *next_term_idx += 1;
                        self.next()
                    }
                } else {
                    std::mem::swap(lower_level_terms, this_level_terms);
                    this_level_terms.clear();
                    self.next()
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GroundTerm {
    fun_name: String,
    ground_terms: Vec<GroundTerm>,
}
impl GroundTerm {
    fn constant(name: String) -> Self {
        Self {
            fun_name: name,
            ground_terms: Vec::new(),
        }
    }

    fn encode(&self) -> String {
        self.to_string()
    }

    fn display_name_with_ground_terms(
        f: &mut std::fmt::Formatter<'_>,
        name: &str,
        terms: &Vec<impl Display>,
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
}

impl Display for GroundTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Self::display_name_with_ground_terms(f, &self.fun_name, &self.ground_terms)
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
        GroundTerm::display_name_with_ground_terms(f, self.name, &self.ground_terms)
    }
}

impl SkolemisedFormula {
    // Grounds the formula, replacing vars (keys) with ground terms (values).
    fn ground(&self, mapping: &HashMap<&str, GroundTerm>) -> NNFPropagated {
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
        let fns = [(0, &["c"][..]), (1, &["f", "g"])];
        let sig = Signature {
            per_name: HashMap::new(),
            per_arity: HashMap::from_iter(fns.into_iter().map(|(arity, names)| {
                (
                    arity,
                    names.into_iter().map(|str| (*str).to_owned()).collect(),
                )
            })),
            empty_set: HashSet::new(),
        };
        let universe5 = Vec::from_iter(sig.herbrands_universe_iter().take(11));
        universe5.iter().for_each(|elem| print!("{}, ", elem));
    }
}
