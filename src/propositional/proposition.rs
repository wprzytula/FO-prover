use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Write},
    hash::Hash,
};

use crate::first_order::formula::{BinLogOp, BinLogOpKind, Instant, LogOp, Logic};

pub(crate) fn fresh_var(vars: &mut HashSet<String>) -> String {
    let mut buf = String::new();
    buf.push('x');
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

pub(crate) trait UsedVars {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S>;
    fn add_used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self, vars: &mut HashSet<S>) {
        vars.extend(self.used_vars());
    }
}

impl Logic for Proposition {}

type PLogOp = LogOp<Proposition>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Proposition {
    #[allow(unused)]
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

impl UsedVars for Proposition {
    fn used_vars<'a, S: From<&'a String> + Eq + Hash>(&'a self) -> HashSet<S> {
        let mut vars = HashSet::new();
        fn rec<'a, S: From<&'a String> + Eq + Hash>(vars: &mut HashSet<S>, prop: &'a Proposition) {
            match prop {
                Proposition::Instant(_) => (),
                Proposition::Var(v) => {
                    vars.insert(v.into());
                }
                Proposition::LogOp(log_op) => match log_op {
                    LogOp::Not(p) => rec(vars, p),
                    LogOp::Bin(BinLogOp { phi, psi, .. }) => {
                        rec(vars, phi);
                        rec(vars, psi);
                    }
                },
            }
        }
        rec(&mut vars, self);
        vars
    }
}


impl Display for Proposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Proposition::Instant(i) => i.fmt(f),
            Proposition::LogOp(logop) => logop.fmt(f),
            Proposition::Var(v) => v.fmt(f),
        }
    }
}
#[cfg(test)]
pub(crate) mod tests {
    use std::cell::RefCell;

    use super::*;

    use log::trace;
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
        trace!(
            "Evaluated:\nphi={:#?} to {}, \npsi={:#?} to {}\nin valuation: {:#?}",
            phi,
            phi_val,
            psi,
            psi_val,
            valuation
        );
        Ok(res)
    }

    impl Proposition {
        fn binop(phi: Proposition, psi: Proposition, op: BinLogOpKind) -> Proposition {
            Proposition::LogOp(LogOp::Bin(BinLogOp {
                kind: op,
                phi: Box::new(phi),
                psi: Box::new(psi),
            }))
        }
        pub(crate) fn implies(phi: Proposition, psi: Proposition) -> Proposition {
            Self::binop(phi, psi, BinLogOpKind::Implies)
        }
        pub(crate) fn iff(phi: Proposition, psi: Proposition) -> Proposition {
            Self::binop(phi, psi, BinLogOpKind::Iff)
        }
        pub(crate) fn and(phi: Proposition, psi: Proposition) -> Proposition {
            Self::binop(phi, psi, BinLogOpKind::And)
        }
        pub(crate) fn or(phi: Proposition, psi: Proposition) -> Proposition {
            Self::binop(phi, psi, BinLogOpKind::Or)
        }
        pub(crate) fn not(phi: Proposition) -> Proposition {
            Proposition::LogOp(LogOp::Not(Box::new(phi)))
        }
        pub(crate) fn var(s: impl Into<String>) -> Proposition {
            Proposition::Var(s.into())
        }

        pub(crate) fn example_sat() -> Self {
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
        pub(crate) fn example_unsat() -> Self {
            Self::LogOp(LogOp::Not(Box::new(Self::LogOp(LogOp::Not(Box::new(
                Self::LogOp(LogOp::Bin(BinLogOp {
                    kind: BinLogOpKind::Iff,
                    phi: Box::new(Self::Var("p".to_owned())),
                    psi: Box::new(Self::LogOp(LogOp::Bin(BinLogOp {
                        kind: BinLogOpKind::Implies,
                        phi: Box::new(Self::LogOp(LogOp::Bin(BinLogOp {
                            kind: BinLogOpKind::Or,
                            phi: Box::new(Self::LogOp(LogOp::Bin(BinLogOp {
                                kind: BinLogOpKind::Or,
                                phi: Box::new(Self::Instant(Instant::F)),
                                psi: Box::new(Self::LogOp(LogOp::Not(Box::new(Self::Var(
                                    "q".to_owned(),
                                ))))),
                            }))),
                            psi: Box::new(Self::Var("q".to_owned())),
                        }))),
                        psi: Box::new(Self::LogOp(LogOp::Not(Box::new(Self::LogOp(LogOp::Bin(
                            BinLogOp {
                                kind: BinLogOpKind::And,
                                phi: Box::new(Self::Var("p".to_owned())),
                                psi: Box::new(Self::Var("p".to_owned())),
                            },
                        )))))),
                    }))),
                })),
            ))))))
        }
        pub(crate) fn tautologies() -> impl IntoIterator<Item = (&'static str, Proposition)> {
            use Proposition as P;
            [
                (
                    "contraposition",
                    P::iff(
                        P::implies(P::var("A"), P::var("B")),
                        P::implies(P::not(P::var("B")), P::not(P::var("A"))),
                    ),
                ),
                (
                    "proof by cases",
                    P::implies(
                        P::and(
                            P::or(P::var("A"), P::var("B")),
                            P::and(
                                P::implies(P::var("A"), P::var("C")),
                                P::implies(P::var("B"), P::var("C")),
                            ),
                        ),
                        P::var("C"),
                    ),
                ),
                (
                    "reductio ad absurdum",
                    P::implies(
                        P::and(
                            P::implies(P::not(P::var("A")), P::var("B")),
                            P::implies(P::not(P::var("A")), P::not(P::var("B"))),
                        ),
                        P::var("A"),
                    ),
                ),
            ]
        }

        pub(crate) fn unsats() -> impl Iterator<Item = (&'static str, Proposition)> {
            Self::tautologies()
                .into_iter()
                .map(|(name, proposition)| (name, Proposition::not(proposition)))
        }
    }
}
