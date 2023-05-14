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
}
