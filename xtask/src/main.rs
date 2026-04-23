#[macro_use]
extern crate duct;

mod cmake;
mod install;
mod kernel;
mod run;
mod verify;

use std::path::PathBuf;

use clap::Parser;

#[derive(Debug, Parser)]
enum Command {
    /// Execute cmake in the $PROJECT_DIR/target/build and build project
    Build(kernel::BuildOptions),
    /// Install Kernel to $PROJECT_DIR/target/kernel-install
    Install(kernel::BuildOptions),
    /// Run sel4-tests
    Run(kernel::BuildOptions),
    /// Download and install the official Verus release binaries
    BootstrapVerus(verify::BootstrapOptions),
    /// Run the official Verus verification entrypoint
    Verify(verify::VerifyOptions),
    /// Clean Project
    Clean,
}

fn main() -> Result<(), anyhow::Error> {
    let opts = Command::parse();

    use Command::*;
    match opts {
        Build(opts) => kernel::build(&opts)?,
        Install(build_opts) => install::install(&build_opts)?,
        Run(run_opts) => run::run(&run_opts)?,
        BootstrapVerus(opts) => verify::bootstrap(&opts)?,
        Verify(opts) => verify::run(&opts)?,
        Clean => {
            let xtask_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            cmd!("rm", "-rf", xtask_path.join("../target").to_str().unwrap()).run()?;
        }
    }

    Ok(())
}
