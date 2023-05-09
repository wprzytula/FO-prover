#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use]
extern crate quickcheck_macros;

use anyhow::Result;
use parser::Parser;

pub(crate) mod formula;
pub(crate) mod parser;
pub(crate) mod proposition;
pub(crate) mod sat_solver;

fn main() -> Result<()> {
    let parser = Parser::new()?;
    let input = {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf)?;
        buf
    };

    let _formula = parser.parse(&input)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{fs::read_dir, path::Path};

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
            println!("\nTest: {:?}", &file);
            let os_name = file.file_name();
            let name = os_name.to_str().unwrap();
            if file.file_type().unwrap().is_file() {
                let complete_filename = path.join(name);
                let input = std::fs::read(complete_filename).unwrap();
                let input_str = String::from_utf8(input).unwrap();
                println!("Input:\n{}", &input_str);
                run(&input_str);
            }
        }
    }
}
