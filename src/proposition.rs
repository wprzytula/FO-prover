use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};

use crate::formula::{BinLogOp, BinLogOpKind, Instant, LogOp, Logic};

pub(crate) fn fresh_var(vars: &HashSet<String>) -> String {
    let mut buf = String::new();
    buf.push('p');
    for i in 0.. {
        buf.truncate(1);
        write!(buf, "{}", i).unwrap();
        if !vars.contains(buf.as_str()) {
            return buf;
        }
    }
    unreachable!()
}

pub(crate) type Valuation<'a> = HashMap<&'a str, bool>;

#[derive(Debug)]
pub(crate) struct MissingValuation<'a>(pub(crate) &'a str);

pub(crate) trait Evaluable {
    fn evaluate<'a>(&'a self, valuation: &'a Valuation) -> Result<bool, MissingValuation<'a>>;
}

impl Logic for Proposition {}

type PLogOp = LogOp<Proposition>;
type PBinLogOp = BinLogOp<Proposition>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Proposition {
    Instant(Instant),
    LogOp(PLogOp),
    Var(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    use quickcheck::Arbitrary;

    impl Arbitrary for Proposition {
        fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
            todo!()

            //     arbitrary = sized f where

            //     f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

            //     f size = frequency [
            //         (1, liftM Not (f (size - 1))),
            //         (4, do
            //             size_ <- choose (0, size - 1)
            //             conn <- oneof $ map return [And, Or, Implies, Iff]
            //             left <- f size_
            //             right <- f $ size - size_ - 1
            //             return $ conn left right)
            //     ]
        }
    }
}
