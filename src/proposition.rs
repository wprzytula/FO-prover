use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};

use crate::formula::{BinLogOp, BinLogOpKind, Instant, LogOp, Logic};

pub(crate) fn fresh_var(vars: &mut HashSet<String>) -> String {
    let mut buf = String::new();
    buf.push('p');
    for i in 0.. {
        buf.truncate(1);
        write!(buf, "{}", i).unwrap();
        if !vars.contains(buf.as_str()) {
            vars.insert(buf.clone());
            return buf;
        }
    }
    unreachable!()
}

pub(crate) trait Valuation<'s>: std::fmt::Debug {
    fn valuate<'v: 's>(&'s self, var: &'v str) -> Result<bool, MissingValuation>;
}
impl<'s> Valuation<'s> for HashMap<&'s str, bool> {
    fn valuate<'v: 's>(&'s self, var: &'v str) -> Result<bool, MissingValuation> {
        self.get(var).copied().ok_or(MissingValuation(var))
    }
}

#[derive(Debug)]
pub(crate) struct MissingValuation<'a>(pub(crate) &'a str);

pub(crate) trait Evaluable: std::fmt::Debug {
    fn evaluate<'a, 'b: 'a>(
        &'a self,
        valuation: &'b impl Valuation<'a>,
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
        valuation: &'b impl Valuation<'a>,
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
pub(crate) mod tests {
    use std::cell::RefCell;

    use super::*;

    use quickcheck::Arbitrary;
    use rand::Rng;

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

    #[derive(Debug)]
    pub(crate) struct RandomCachedValuation<'s> {
        mapping: RefCell<HashMap<&'s str, bool>>,
    }

    impl<'s> RandomCachedValuation<'s> {
        pub(crate) fn new() -> Self {
            Self {
                mapping: RefCell::new(HashMap::new()),
            }
        }
    }

    impl<'s> Valuation<'s> for RandomCachedValuation<'s> {
        fn valuate<'v: 's>(&'s self, var: &'s str) -> Result<bool, MissingValuation> {
            Ok(*self
                .mapping
                .borrow_mut()
                .entry(var)
                .or_insert_with(|| rand::thread_rng().gen_bool(0.5)))
        }
    }

    pub(crate) fn randomly_check_equivalence(phi: &impl Evaluable, psi: &impl Evaluable) -> bool {
        const REPETITIONS: u32 = 5;
        for _ in 0..REPETITIONS {
            let valuation = RandomCachedValuation::new();
            if !equivalent(phi, psi, &valuation).unwrap() {
                return false;
            }
        }
        true
    }

    pub(crate) fn equivalent<'a, 'b: 'a>(
        phi: &'a impl Evaluable,
        psi: &'a impl Evaluable,
        valuation: &'b impl Valuation<'a>,
    ) -> Result<bool, MissingValuation<'a>> {
        let phi_val = phi.evaluate(valuation)?;
        let psi_val = psi.evaluate(valuation)?;
        let res = psi_val == phi_val;
        println!(
            "Evaluated:\nphi={:#?} to {}, \npsi={:#?} to {}\nin valuation: {:#?}",
            phi, phi_val, psi, psi_val, valuation
        );
        Ok(res)
    }

    impl Proposition {
        pub(crate) fn example() -> Self {
            Self::LogOp(LogOp::Not(Box::new(Self::LogOp(LogOp::Bin(BinLogOp {
                kind: BinLogOpKind::Iff,
                phi: Box::new(Self::Var("p".to_owned())),
                psi: Box::new(Self::LogOp(LogOp::Bin(BinLogOp {
                    kind: BinLogOpKind::Implies,
                    phi: Box::new(Self::Instant(Instant::T)),
                    psi: Box::new(Self::LogOp(LogOp::Not(Box::new(Self::LogOp(LogOp::Bin(
                        BinLogOp {
                            kind: BinLogOpKind::And,
                            phi: Box::new(Self::Var("p".to_owned())),
                            psi: Box::new(Self::Var("q".to_owned())),
                        },
                    )))))),
                }))),
            })))))
        }
    }
}
