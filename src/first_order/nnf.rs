use crate::{
    first_order::formula::{BinLogOp, BinLogOpKind, Formula, LogOp, Quantifier},
    propositional::nnf::NNFLogOpKind,
};

use super::formula::{Instant, QuantifierKind, Term};

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
