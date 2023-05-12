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

// pub(crate) type Valuation<'a> = HashMap<&'a str, bool>;
pub(crate) trait Valuation {
    fn valuate<'a, 'b: 'a>(&'a self, var: &'b str) -> Result<bool, MissingValuation>;
}
impl<'s> Valuation for HashMap<&'s str, bool> {
    fn valuate<'a, 'b: 'a>(&'a self, var: &'b str) -> Result<bool, MissingValuation> {
        self.get(var).copied().ok_or(MissingValuation(var))
    }
}

#[derive(Debug)]
pub(crate) struct MissingValuation<'a>(pub(crate) &'a str);

pub(crate) trait Evaluable {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation,
    ) -> Result<bool, MissingValuation<'a>>;
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

impl Evaluable for Proposition {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation,
    ) -> Result<bool, MissingValuation<'a>> {
        match self {
            Proposition::Instant(i) => Ok(i.into_bool()),
            Proposition::Var(s) => valuation.valuate(s),
            Proposition::LogOp(log_op) => match log_op {
                LogOp::Not(p) => p.evaluate(valuation).map(|b| !b),
                LogOp::Bin(BinLogOp { kind, phi, psi }) => {
                    let val_phi = phi.evaluate(valuation)?;
                    let val_psi = psi.evaluate(valuation)?;
                    Ok(match kind {
                        BinLogOpKind::And => val_phi && val_psi,
                        BinLogOpKind::Or => val_phi || val_psi,
                        BinLogOpKind::Implies => !val_phi || val_psi,
                        BinLogOpKind::Iff => val_phi == val_psi,
                    })
                }
            },
        }
    }
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

    pub(crate) fn equivalent<'a, 'b: 'a>(
        phi: &'a impl Evaluable,
        psi: &'a impl Evaluable,
        valuation: &'b impl Valuation,
    ) -> Result<bool, MissingValuation<'a>> {
        Ok(phi.evaluate(valuation)? == psi.evaluate(valuation)?)
    }
}
