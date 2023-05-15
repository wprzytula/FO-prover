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
