use std::collections::HashSet;

use crate::{
    first_order::formula::{BinLogOp, BinLogOpKind, Formula, LogOp, Quantifier},
    propositional::{nnf::NNFLogOpKind, proposition::fresh_var},
};

use super::formula::{Instant, QuantifierKind, RenameVar, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNF {
    Instant(Instant),
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
    Quantified {
        kind: QuantifierKind,
        var: String,
        phi: Box<Self>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum NNFRelKind {
    Pos,
    Neg,
}

impl Formula {
    pub(crate) fn into_nnf(self) -> NNF {
        NNF::new(self)
    }
}

impl NNF {
    pub(crate) fn new(p: Formula) -> Self {
        fn rec(phi: Formula, positive: bool) -> NNF {
            match phi {
                Formula::Instant(i) => NNF::Instant(i),
                Formula::Rel(rel) => NNF::Rel {
                    kind: if positive {
                        NNFRelKind::Pos
                    } else {
                        NNFRelKind::Neg
                    },
                    name: rel.name,
                    terms: rel.terms,
                },
                Formula::LogOp(LogOp::Not(p)) => rec(*p, !positive),
                Formula::LogOp(LogOp::Bin(BinLogOp { kind, phi, psi })) => match kind {
                    BinLogOpKind::And => NNF::LogOp {
                        kind: if positive {
                            NNFLogOpKind::And
                        } else {
                            NNFLogOpKind::Or
                        },
                        phi: Box::new(rec(*phi, positive)),
                        psi: Box::new(rec(*psi, positive)),
                    },
                    BinLogOpKind::Or => NNF::LogOp {
                        kind: if positive {
                            NNFLogOpKind::Or
                        } else {
                            NNFLogOpKind::And
                        },
                        phi: Box::new(rec(*phi, positive)),
                        psi: Box::new(rec(*psi, positive)),
                    },
                    BinLogOpKind::Implies => rec(
                        Formula::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::Or,
                            phi: Box::new(Formula::LogOp(LogOp::Not(phi))),
                            psi,
                        })),
                        positive,
                    ),
                    BinLogOpKind::Iff => rec(
                        Formula::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::Or,
                            phi: Box::new(Formula::LogOp(LogOp::Bin(BinLogOp {
                                kind: BinLogOpKind::And,
                                phi: phi.clone(),
                                psi: psi.clone(),
                            }))),
                            psi: Box::new(Formula::LogOp(LogOp::Bin(BinLogOp {
                                kind: BinLogOpKind::And,
                                phi: Box::new(Formula::LogOp(LogOp::Not(phi))),
                                psi: Box::new(Formula::LogOp(LogOp::Not(psi))),
                            }))),
                        })),
                        positive,
                    ),
                },
                Formula::Quantified(Quantifier { kind, var, phi }) => {
                    let kind = match (positive, kind) {
                        (true, QuantifierKind::Exists) | (false, QuantifierKind::Forall) => {
                            QuantifierKind::Exists
                        }
                        (true, QuantifierKind::Forall) | (false, QuantifierKind::Exists) => {
                            QuantifierKind::Forall
                        }
                    };
                    let phi = Box::new(rec(*phi, positive /*propagate*/));
                    NNF::Quantified { kind, var, phi }
                }
            }
        }
        rec(p, true)
    }

    pub(crate) fn propagate_constants(self) -> NNFPropagated {
        match self {
            NNF::Instant(i) => NNFPropagated::Instant(i),
            NNF::Rel { kind, name, terms } => {
                NNFPropagated::Inner(NNFPropagatedInner::Rel { kind, name, terms })
            }
            NNF::LogOp { kind, phi, psi } => {
                let phi = phi.propagate_constants();
                let psi = psi.propagate_constants();
                match (phi, psi) {
                    (NNFPropagated::Instant(i), NNFPropagated::Instant(j)) => {
                        NNFPropagated::Instant(Instant::from_bool(match kind {
                            NNFLogOpKind::And => i.into_bool() && j.into_bool(),
                            NNFLogOpKind::Or => i.into_bool() || j.into_bool(),
                        }))
                    }
                    (NNFPropagated::Instant(i), x) | (x, NNFPropagated::Instant(i)) => {
                        match (kind, i) {
                            (NNFLogOpKind::And, Instant::T) => x,
                            (NNFLogOpKind::And, Instant::F) => NNFPropagated::Instant(Instant::F),
                            (NNFLogOpKind::Or, Instant::T) => NNFPropagated::Instant(Instant::T),
                            (NNFLogOpKind::Or, Instant::F) => x,
                        }
                    }
                    (NNFPropagated::Inner(phi), NNFPropagated::Inner(psi)) => {
                        NNFPropagated::Inner(NNFPropagatedInner::LogOp {
                            kind,
                            phi: Box::new(phi),
                            psi: Box::new(psi),
                        })
                    }
                }
            }
            NNF::Quantified { kind, var, phi } => match phi.propagate_constants() {
                // TODO: Is this surely valid?
                n @ NNFPropagated::Instant(_) => n,
                NNFPropagated::Inner(phi) => NNFPropagated::Inner(NNFPropagatedInner::Quantified {
                    kind,
                    var,
                    phi: Box::new(phi),
                }),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNFPropagated {
    Instant(Instant),
    Inner(NNFPropagatedInner),
}
impl NNFPropagated {
    fn free_vars(&self) -> HashSet<String> {
        let mut free = HashSet::new();
        let mut captured = HashSet::new();
        match self {
            NNFPropagated::Instant(_) => (),
            NNFPropagated::Inner(inner) => inner.free_vars(&mut free, &mut captured),
        }
        free
    }

    // Returns all vars in the formula.
    pub(crate) fn make_vars_unique(&mut self) -> HashSet<String> {
        let mut vars = self.free_vars();
        match self {
            NNFPropagated::Instant(_) => (),
            NNFPropagated::Inner(inner) => inner.make_vars_unique(&mut vars),
        }
        vars
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNFPropagatedInner {
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
    Quantified {
        kind: QuantifierKind,
        var: String,
        phi: Box<Self>,
    },
}
impl NNFPropagatedInner {
    fn free_vars<'a>(&'a self, free: &mut HashSet<String>, captured: &mut HashSet<&'a str>) {
        match self {
            NNFPropagatedInner::LogOp { phi, psi, .. } => {
                phi.free_vars(free, captured);
                psi.free_vars(free, captured);
            }
            NNFPropagatedInner::Rel { terms, .. } => {
                terms.iter().for_each(|term| term.free_vars(free, captured))
            }
            NNFPropagatedInner::Quantified { var, phi, .. } => {
                captured.insert(var);
                phi.free_vars(free, captured);
                captured.remove(var.as_str());
            }
        }
    }

    fn make_vars_unique(&mut self, vars: &mut HashSet<String>) {
        match self {
            NNFPropagatedInner::Rel { .. } => (),
            NNFPropagatedInner::LogOp { phi, psi, .. } => {
                phi.make_vars_unique(vars);
                psi.make_vars_unique(vars);
            }
            NNFPropagatedInner::Quantified { var, phi, .. } => {
                if vars.contains(var) {
                    // We have to rename `var` to a fresh unique var name.
                    let fresh = fresh_var(vars);
                    phi.rename(var, &fresh);
                    *var = fresh.clone();
                    vars.insert(fresh);
                } else {
                    vars.insert(var.clone());
                }
                phi.make_vars_unique(vars);
            }
        }
    }
}

impl RenameVar for NNFPropagatedInner {
    fn rename(&mut self, var: &str, new_name: &String) {
        match self {
            NNFPropagatedInner::LogOp { phi, psi, .. } => {
                phi.rename(var, new_name);
                psi.rename(var, new_name);
            }
            NNFPropagatedInner::Rel { terms, .. } => {
                terms.iter_mut().for_each(|term| term.rename(var, new_name))
            }
            NNFPropagatedInner::Quantified {
                var: quantifier_var,
                phi,
                ..
            } => {
                if var != quantifier_var {
                    phi.rename(var, new_name);
                }
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::first_order::formula::Formula;

    use super::*;

    #[test]
    fn nnf() {
        // Exists "x" (Implies (Rel "D" [Var "x"]) (Forall "y" (Rel "D" [Var "y"])))
        let formula = Formula::drinker_paradox();
        dbg!(formula.into_nnf());

        // assert_eq!(formula.into_nnf(), expected);
    }
}
