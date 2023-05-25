use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Write},
};

use log::{debug, info};

use crate::{
    first_order::herbrand::TermDisplayer,
    propositional::{nnf::NNFLogOpKind, proposition::UsedVars},
};

use super::{
    formula::{Instant, Logic, QuantifierKind, Rel, RenameVar, Term},
    nnf::{NNFPropagated, NNFPropagatedInner, NNFRelKind},
};

impl Logic for PNF {}
impl Logic for NNFQuantifierFreeInner {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PNF {
    Instant(Instant),
    Inner(PNFInner),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PNFInner {
    // Reversed: the last is the outermost.
    pub(crate) quantified_vars: Vec<(QuantifierKind, String)>,
    pub(crate) ksi: NNFQuantifierFreeInner,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNFQuantifierFreeInner {
    LogOp {
        kind: NNFLogOpKind,
        phi: Box<Self>,
        psi: Box<Self>,
    },
    Rel {
        kind: NNFRelKind,
        rel: Rel,
    },
}

impl RenameVar for NNFQuantifierFreeInner {
    fn rename(&mut self, var: &str, new_name: &String) {
        match self {
            NNFQuantifierFreeInner::LogOp { phi, psi, .. } => {
                phi.rename(var, new_name);
                psi.rename(var, new_name);
            }
            NNFQuantifierFreeInner::Rel {
                rel: Rel { terms, .. },
                ..
            } => terms.iter_mut().for_each(|term| term.rename(var, new_name)),
        }
    }
}

impl Display for NNFQuantifierFreeInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LogOp { kind, phi, psi } => write!(f, "({} {} {})", phi, kind, psi),
            Self::Rel { kind, rel } => match kind {
                NNFRelKind::Pos => Display::fmt(rel, f),
                NNFRelKind::Neg => {
                    f.write_str("~")?;
                    Display::fmt(rel, f)
                }
            },
        }
    }
}

impl NNFPropagated {
    #[allow(non_snake_case)]
    pub(crate) fn into_PNF(self) -> PNF {
        match self {
            NNFPropagated::Instant(i) => PNF::Instant(i),
            NNFPropagated::Inner(inner) => PNF::Inner(inner.into_PNF().0),
        }
    }
}

impl NNFPropagatedInner {
    #[allow(non_snake_case)]
    fn into_PNF(self) -> (PNFInner, HashSet<String>) {
        match self {
            NNFPropagatedInner::Rel {
                kind,
                name,
                mut terms,
            } => {
                let mut vars = HashSet::new();
                for term in terms.iter_mut() {
                    term.add_used_vars(&mut vars);
                }
                (
                    PNFInner {
                        quantified_vars: Vec::new(),
                        ksi: NNFQuantifierFreeInner::Rel {
                            kind,
                            rel: Rel { name, terms },
                        },
                    },
                    vars,
                )
            }
            NNFPropagatedInner::LogOp { kind, phi, psi } => {
                let (phi, phi_vars) = phi.into_PNF();
                let (psi, psi_vars) = psi.into_PNF();

                let mut all_vars = phi_vars;
                all_vars.extend(psi_vars);

                let quantified_vars = {
                    let mut quantified = phi.quantified_vars;
                    quantified.extend(psi.quantified_vars);
                    quantified
                };

                let phi = Box::new(phi.ksi);
                let psi = Box::new(psi.ksi);
                (
                    PNFInner {
                        quantified_vars,
                        ksi: NNFQuantifierFreeInner::LogOp { kind, phi, psi },
                    },
                    all_vars,
                )
            }
            NNFPropagatedInner::Quantified { kind, var, phi } => {
                let (
                    PNFInner {
                        mut quantified_vars,
                        ksi,
                    },
                    mut vars,
                ) = phi.into_PNF();
                vars.insert(var.clone());
                quantified_vars.push((kind, var));
                (
                    PNFInner {
                        quantified_vars,
                        ksi,
                    },
                    vars,
                )
            }
        }
    }
}

impl Logic for SkolemisedFormula {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SkolemisedFormula {
    Instant(Instant),
    Inner {
        // Order is irrelevant (in PNF with universal quantifiers only)
        universally_quantified_vars: Vec<String>,
        ksi: NNFQuantifierFreeInner,
    },
}

impl Display for SkolemisedFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SkolemisedFormula::Instant(i) => Display::fmt(i, f),
            SkolemisedFormula::Inner {
                universally_quantified_vars,
                ksi,
            } => {
                if !universally_quantified_vars.is_empty() {
                    f.write_char('∀')?;
                    f.write_char(' ')?;
                    for quantified in universally_quantified_vars {
                        f.write_str(quantified)?;
                        f.write_str(" ")?;
                    }
                    f.write_char('.')?;
                    f.write_char(' ')?;
                }
                Display::fmt(ksi, f)
            }
        }
    }
}

fn skolem_function(var: &str) -> String {
    format!("_sk_{}_", var)
}

impl NNFPropagated {
    pub(crate) fn skolemise(self) -> SkolemisedFormula {
        // TODO: miniscoping
        let mut miniscoped = self;
        let all_vars = miniscoped.make_vars_unique();
        info!("NNFPropagated with vars made unique: {}", &miniscoped);
        let mut universally_quantified_vars = HashSet::new();
        let mut skolem_fns = HashMap::new();
        match &mut miniscoped {
            NNFPropagated::Instant(_) => (),
            NNFPropagated::Inner(inner) => {
                inner.skolemise(&mut universally_quantified_vars, &mut skolem_fns)
            }
        };

        let pnf = miniscoped.into_PNF();
        match pnf {
            PNF::Instant(i) => SkolemisedFormula::Instant(i),
            PNF::Inner(PNFInner {
                quantified_vars,
                ksi,
            }) => {
                let universally_quantified_vars = quantified_vars
                    .into_iter()
                    .map(|(kind, var)| {
                        assert!(matches!(kind, QuantifierKind::Forall));
                        var
                    })
                    .collect();
                SkolemisedFormula::Inner {
                    universally_quantified_vars,
                    ksi,
                }
            }
        }
    }
}

impl NNFPropagatedInner {
    fn skolemise(
        &mut self,
        universally_quantified_vars: &mut HashSet<String>,
        skolem_fns: &mut HashMap<String, (String, Vec<String>)>,
    ) {
        const MOCK_REL: NNFPropagatedInner = NNFPropagatedInner::Rel {
            kind: NNFRelKind::Neg,
            name: String::new(),
            terms: Vec::new(),
        };

        match self {
            NNFPropagatedInner::LogOp { phi, psi, .. } => {
                phi.skolemise(universally_quantified_vars, skolem_fns);
                psi.skolemise(universally_quantified_vars, skolem_fns);
            }
            NNFPropagatedInner::Quantified { kind, var, phi } => {
                match kind {
                    QuantifierKind::Exists => {
                        let skolem_fn_name = skolem_function(var);
                        let terms = Vec::from_iter(universally_quantified_vars.iter().cloned());
                        debug!("Found existential variable {}, so replacing it with Skolem function: {}",
                                var, TermDisplayer{name: &skolem_fn_name, terms: &terms});
                        assert!(skolem_fns
                            .insert(var.clone(), (skolem_fn_name, terms))
                            .is_none());
                    }
                    QuantifierKind::Forall => {
                        assert!(universally_quantified_vars.insert(var.clone()));
                    }
                }
                phi.skolemise(universally_quantified_vars, skolem_fns);

                match kind {
                    QuantifierKind::Exists => {
                        // Remember to delete this soon
                        skolem_fns.remove(var);
                        let phi = std::mem::replace(phi.as_mut(), MOCK_REL);
                        *self = phi;
                    }
                    QuantifierKind::Forall => {
                        universally_quantified_vars.remove(var.as_str());
                    }
                }
            }
            NNFPropagatedInner::Rel { terms, .. } => {
                terms.iter_mut().for_each(|term| term.skolemise(skolem_fns))
            }
        }
    }
}

impl Term {
    fn skolemise(&mut self, skolem_fns: &HashMap<String, (String, Vec<String>)>) {
        match self {
            Term::Var(var) => {
                if let Some((skolem_fn, terms)) = skolem_fns.get(var) {
                    *self = Term::Fun(
                        skolem_fn.clone(),
                        Vec::from_iter(terms.iter().map(|var| Term::Var(var.clone()))),
                    );
                }
            }
            Term::Fun(_, terms) => terms.iter_mut().for_each(|term| term.skolemise(skolem_fns)),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::first_order::formula::Formula;

    use super::*;

    #[test]
    fn skolemisation() {
        // Exists "x" (Implies (Rel "D" [Var "x"]) (Forall "y" (Rel "D" [Var "y"])))
        let formula = Formula::not(Formula::drinker_paradox());
        let expected_skolem = SkolemisedFormula::Inner {
            universally_quantified_vars: vec!["x".to_owned()],
            ksi: NNFQuantifierFreeInner::LogOp {
                kind: NNFLogOpKind::And,
                phi: Box::new(NNFQuantifierFreeInner::Rel {
                    kind: NNFRelKind::Pos,
                    rel: Rel {
                        name: "D".to_owned(),
                        terms: vec![Term::Var("x".to_owned())],
                    },
                }),
                psi: Box::new(NNFQuantifierFreeInner::Rel {
                    kind: NNFRelKind::Neg,
                    rel: Rel {
                        name: "D".to_owned(),
                        terms: vec![Term::Fun(
                            skolem_function("y"),
                            vec![Term::Var("x".to_owned())],
                        )],
                    },
                }),
            },
        };
        assert_eq!(
            formula.into_nnf().propagate_constants().skolemise(),
            expected_skolem
        );
    }
}
