use std::{collections::HashSet, hash::Hash};

use crate::{
    formula::{BinLogOp, BinLogOpKind, Instant, LogOp},
    proposition::{Evaluable, MissingValuation, Proposition, UsedVars, Valuation},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNF {
    Instant(Instant),
    LogOp {
        kind: NNFLogOpKind,
        phi: Box<Self>,
        psi: Box<Self>,
    },
    Var(NNFVarKind, String),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum NNFVarKind {
    Pos,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum NNFLogOpKind {
    And,
    Or,
}

impl NNFLogOpKind {
    pub(crate) fn opposite(self) -> Self {
        match self {
            NNFLogOpKind::And => NNFLogOpKind::Or,
            NNFLogOpKind::Or => NNFLogOpKind::And,
        }
    }
}

impl NNF {
    pub(crate) fn new(p: Proposition) -> Self {
        fn rec(p: Proposition, positive: bool) -> NNF {
            match p {
                Proposition::Instant(i) => NNF::Instant(i),
                Proposition::Var(s) => NNF::Var(
                    if positive {
                        NNFVarKind::Pos
                    } else {
                        NNFVarKind::Neg
                    },
                    s,
                ),
                Proposition::LogOp(LogOp::Not(p)) => rec(*p, !positive),
                Proposition::LogOp(LogOp::Bin(BinLogOp { kind, phi, psi })) => match kind {
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
                        Proposition::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::Or,
                            phi: Box::new(Proposition::LogOp(LogOp::Not(phi))),
                            psi,
                        })),
                        positive,
                    ),
                    BinLogOpKind::Iff => rec(
                        Proposition::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::Or,
                            phi: Box::new(Proposition::LogOp(LogOp::Bin(BinLogOp {
                                kind: BinLogOpKind::And,
                                phi: phi.clone(),
                                psi: psi.clone(),
                            }))),
                            psi: Box::new(Proposition::LogOp(LogOp::Bin(BinLogOp {
                                kind: BinLogOpKind::And,
                                phi: Box::new(Proposition::LogOp(LogOp::Not(phi))),
                                psi: Box::new(Proposition::LogOp(LogOp::Not(psi))),
                            }))),
                        })),
                        positive,
                    ),
                },
            }
        }
        //     nnf φ = rust φ True
        // where
        //     rust T True = T
        //     rust T False = F
        //     rust F True = F
        //     rust F False = T
        //     rust (Prop p) True = Prop p
        //     rust (Prop p) False = Not $ Prop p
        //     rust (Not φ) True = rust φ False
        //     rust (Not φ) False = rust φ True
        //     rust (And φ ψ) True = And (rust φ True) (rust ψ True)
        //     rust (And φ ψ) False = Or (rust φ False) (rust ψ False)
        //     rust (Or φ ψ) True = Or (rust φ True) (rust ψ True)
        //     rust (Or φ ψ) False = And (rust φ False) (rust ψ False)
        //     rust (Implies φ ψ) b = rust (Or (Not φ) ψ) b
        //     rust (Iff φ ψ) b = rust (Or (And φ ψ) (And (Not φ) (Not ψ))) b
        rec(p, true)
    }

    pub(crate) fn propagate_constants(self) -> NNFPropagated {
        match self {
            NNF::Instant(i) => NNFPropagated::Instant(i),
            NNF::Var(k, s) => NNFPropagated::Inner(NNFPropagatedInner::Var(k, s)),
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
        }
    }
}

impl Evaluable for NNF {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        match self {
            NNF::Instant(i) => Ok(i.into_bool()),
            NNF::Var(k, s) => {
                let s_val = valuation.valuate(s)?;
                Ok(match k {
                    NNFVarKind::Pos => s_val,
                    NNFVarKind::Neg => !s_val,
                })
            }
            NNF::LogOp { kind, phi, psi } => {
                let val_phi = phi.evaluate(valuation)?;
                let val_psi = psi.evaluate(valuation)?;
                Ok(match kind {
                    NNFLogOpKind::And => val_phi && val_psi,
                    NNFLogOpKind::Or => val_phi || val_psi,
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNFPropagated {
    Instant(Instant),
    Inner(NNFPropagatedInner),
}

impl NNFPropagated {
    pub(crate) fn vars(&self) -> HashSet<&str> {
        let mut set = HashSet::new();
        match self {
            NNFPropagated::Instant(_) => (),
            NNFPropagated::Inner(inner) => inner.vars(&mut set),
        };
        set
    }
}

impl Evaluable for NNFPropagated {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        match self {
            NNFPropagated::Instant(i) => Ok(i.into_bool()),
            NNFPropagated::Inner(inner) => inner.evaluate(valuation),
        }
    }
}

impl UsedVars for NNFPropagated {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S> {
        match self {
            NNFPropagated::Instant(_) => HashSet::new(),
            NNFPropagated::Inner(inner) => inner.used_vars(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NNFPropagatedInner {
    LogOp {
        kind: NNFLogOpKind,
        phi: Box<Self>,
        psi: Box<Self>,
    },
    Var(NNFVarKind, String),
}
impl NNFPropagatedInner {
    fn vars<'a: 'b, 'b>(&'a self, set: &mut HashSet<&'b str>) {
        match self {
            NNFPropagatedInner::LogOp { phi, psi, .. } => {
                phi.vars(set);
                psi.vars(set);
            }
            NNFPropagatedInner::Var(_, s) => {
                set.insert(s);
            }
        };
    }
}

impl Evaluable for NNFPropagatedInner {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        match self {
            Self::Var(k, s) => {
                let s_val = valuation.valuate(s)?;
                Ok(match k {
                    NNFVarKind::Pos => s_val,
                    NNFVarKind::Neg => !s_val,
                })
            }
            Self::LogOp { kind, phi, psi } => {
                let val_phi = phi.evaluate(valuation)?;
                let val_psi = psi.evaluate(valuation)?;
                Ok(match kind {
                    NNFLogOpKind::And => val_phi && val_psi,
                    NNFLogOpKind::Or => val_phi || val_psi,
                })
            }
        }
    }
}

impl UsedVars for NNFPropagatedInner {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S> {
        let mut vars = HashSet::new();
        fn rec<'a, S: From<&'a String> + Eq + Hash>(
            vars: &mut HashSet<S>,
            nnf: &'a NNFPropagatedInner,
        ) {
            match nnf {
                NNFPropagatedInner::Var(_, v) => {
                    vars.insert(v.into());
                }
                NNFPropagatedInner::LogOp { phi, psi, .. } => {
                    rec(vars, phi);
                    rec(vars, psi);
                }
            }
        }
        rec(&mut vars, self);
        vars
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        init_logger,
        proposition::{tests::randomly_check_equivalence, Proposition},
    };

    use super::*;

    #[test]
    fn nnf_preserves_logical_equivalence() {
        init_logger();
        let prop = Proposition::example_sat();
        let nnf = NNF::new(prop.clone());
        assert!(randomly_check_equivalence(&prop, &nnf));
    }

    #[test]
    fn nnf_propagated_preserves_logical_equivalence() {
        init_logger();
        let prop = Proposition::example_sat();
        let nnf = NNF::new(prop);
        let nnf_propagated = nnf.clone().propagate_constants();
        assert!(randomly_check_equivalence(&nnf, &nnf_propagated));
    }
}
