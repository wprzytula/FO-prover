#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use]
extern crate quickcheck_macros;

use anyhow::Result;
use first_order::formula::Instant;
use first_order::parser::Parser;
use propositional::cnf::CNF;
use propositional::nnf::NNF;
use propositional::sat_solver::SatSolver;

use crate::first_order::decider::TautologyDecider;
use crate::first_order::formula::Formula;

pub(crate) mod first_order;
pub(crate) mod propositional;

pub(crate) fn init_logger() {
    let _ = env_logger::builder().format_timestamp(None).try_init();
}

fn main() -> Result<()> {
    init_logger();
    let parser = Parser::new()?;
    let input = {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf)?;
        buf
    };

    let formula = parser.parse(&input)?;
    let is_tautology = TautologyDecider::is_tautology(formula);
    print!("{}", is_tautology as u8);

    // Just to silence "unused":
    let cnf = CNF::ECNF(NNF::Instant(Instant::F).propagate_constants());
    SatSolver::solve_by_truth_tables(&cnf);
    SatSolver::solve_by_dp(cnf);
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{fs::read_dir, path::Path};

    use log::info;

    use super::*;

    pub(crate) fn for_each_external_test(mut run: impl FnMut(&str)) {
        let test_path = Path::new("/home/xps15/Studia/Sem8/Logika/Laby/Zal/FO-prover/tests");
        assert!(test_path.exists());

        let good_paths = ["A", "B", "C"];

        let good = good_paths
            .iter()
            .map(|&path| {
                let case_path = test_path.join(path);
                read_dir(&case_path)
                    .unwrap()
                    .map(move |entry| (case_path.clone(), entry))
            })
            .flatten();

        for (path, file) in good {
            let file = file.unwrap();
            info!("\nTest: {:?}", &file);
            let os_name = file.file_name();
            let name = os_name.to_str().unwrap();
            if file.file_type().unwrap().is_file() {
                let complete_filename = path.join(name);
                let input = std::fs::read(complete_filename).unwrap();
                let input_str = String::from_utf8(input).unwrap();
                info!("Input:\n{}", &input_str);
                run(&input_str);
            }
        }
    }

    #[test]
    fn workchain() {
        let parser = Parser::new().unwrap();
        for_each_external_test(|input| {
            let mut formula = parser.parse(&input).unwrap();
            formula.close_universally();
            let negated_formula = Formula::not(formula);
            let nnf = negated_formula.into_nnf();
            let nnf_propagated = nnf.propagate_constants();
            let _pnf = nnf_propagated.into_PNF();
        })
    }
}
