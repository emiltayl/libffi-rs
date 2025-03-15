# Note

All scripts are meant to be executed from the repository's root folder.

# ci-checks.(bat|sh)

These scripts are used to make it easier to perform all lint and test tasks. The scripts require the
following targets to be installed:

* 1.85.0 (MSRV)
* stable
* nightly

These targets can be installed with the `rustup target add` command.

Currently the batch script meant for windows prints all output, while the shell script only prints
command output if a lint or test fails.

## Usage

On Windows run `scripts/ci-checks.bat`. Alternatively `scripts/ci-checks.bat LINTONLY` or
`scripts/ci-checks.bat NOLINT` for only performing lints or skipping the lints respectively.

For all other operating systems, run `scripts/ci-checks.sh`. Alternatively
`scripts/ci-checks.sh LINTONLY` or `scripts/ci-checks.sh NOLINT` for only performing lints or
skipping the lints respectively.

# targettest.sh

This script uses qemu to run tests on other CPU archs, in addition to compiling for and testing 
i686-unknown-linux-gnu. It currently only supports Debian and Ubuntu. It requires `gcc` and `rustup`
to be installed.

## Usage

Run `scripts/targettest.sh SETUP` to set up everything needed to run tests and run the tests.

If everything is already set up, this script can be executed with `scripts/targettest.sh`.