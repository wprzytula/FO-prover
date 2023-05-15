use std::collections::HashSet;

use crate::propositional::{nnf::NNFLogOpKind, proposition::UsedVars};

use super::{
    formula::{Instant, Logic, QuantifierKind, RenameVar, Term},
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
        name: String,
        terms: Vec<Term>,
    },
}

impl RenameVar for NNFQuantifierFreeInner {
    fn rename(&mut self, var: &str, new_name: &String) {
        match self {
            NNFQuantifierFreeInner::LogOp { phi, psi, .. } => {
                phi.rename(var, new_name);
                psi.rename(var, new_name);
            }
            NNFQuantifierFreeInner::Rel { terms, .. } => {
                terms.iter_mut().for_each(|term| term.rename(var, new_name))
            }
        }
    }
}

impl NNFPropagated {
    #[allow(non_snake_case)]
    pub(crate) fn into_PNF(mut self) -> PNF {
        let all_vars = self.make_vars_unique();
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
                        ksi: NNFQuantifierFreeInner::Rel { kind, name, terms },
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
