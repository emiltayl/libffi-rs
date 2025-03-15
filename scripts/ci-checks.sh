#!/bin/sh

# This script is intended to be executed from the repository's root folder like this:
# `scripts/ci-checks.sh`.
#
# The script accepts one of two optional flags: `LINTONLY` and `NOLINT`. `LINTONLY` only checks
# formatting and lints, while `NOLINT` skips straight to building the code and testing. Supply the
# flags as the first argument to this script like this: `scripts/ci-checks.sh LINTONLY` or
# `scripts/ci-checks.sh NOLINT`.

groupstart() {
    if [ -z ${CI+x} ]; then
        echo "================================================================================"
        echo "${1}"
        echo "================================================================================"
    else
        echo "::group::${1}"
    fi
}

groupend() {
    if [ -z ${CI+x} ]; then
        echo
    else
        echo "::endgroup::"
    fi
}

fail() {
    printf "%s\n" "${1}"
    if [ -z ${CI+x} ]; then
        echo "Script failed, check output"
    else
        echo "::error::Script failed, check output"
    fi
    exit 1
}

run_command() {
    echo "${@}"
    output=$(eval "$@" 2>&1) || fail "${output}"
}

export CARGO_TERM_COLOR=always

if [ "${1}" != "NOLINT" ]; then
    groupstart "Checking formatting"

    run_command cargo +nightly fmt --all --check --verbose
    run_command cargo +nightly fmt --manifest-path=examples/no_std_run/Cargo.toml --all --check --verbose

    groupend

    groupstart "Linting"

    run_command cargo +nightly clippy --all --all-targets --all-features --verbose -- -D warnings
    run_command cargo +nightly clippy --manifest-path=examples/no_std_run/Cargo.toml --all --all-features --verbose -- -D warnings
    run_command CLIPPYFLAGS="\"-D warnings\"" RUSTDOCFLAGS="\"--no-run --nocapture --test-builder scripts/clippy-driver.sh -Z unstable-options\"" cargo +nightly test --doc

    groupend

    if [ "${1}" = "LINTONLY" ]; then
        echo "Script completed successfully"
        exit 0
    fi
fi


groupstart "Building"
# For all toolchains (MSRV, Stable, Nightly), build with default targets, complex, and all features

run_command cargo +1.85.0 build --workspace --all-targets --verbose
run_command cargo +1.85.0 build --workspace --all-targets --features complex --verbose
run_command cargo +1.85.0 build --workspace --all-targets --all-features --verbose
run_command cargo +1.85.0 build --manifest-path=examples/no_std_run/Cargo.toml --verbose

run_command cargo +stable build --workspace --all-targets --verbose
run_command cargo +stable build --workspace --all-targets --features complex --verbose
run_command cargo +stable build --workspace --all-targets --all-features --verbose
run_command cargo +stable build --manifest-path=examples/no_std_run/Cargo.toml --verbose

run_command cargo +nightly build --workspace --all-targets --verbose
run_command cargo +nightly build --workspace --all-targets --features complex --verbose
run_command cargo +nightly build --workspace --all-targets --all-features --verbose
run_command cargo +nightly build --manifest-path=examples/no_std_run/Cargo.toml --verbose

groupend

groupstart "Tests"
# For all toolchains, perform tests with default features and all features

run_command cargo +1.85.0 test --workspace --verbose -- --color=always
run_command cargo +1.85.0 test --workspace --all-features --verbose -- --color=always

run_command cargo +stable test --workspace --verbose -- --color=always
run_command cargo +stable test --workspace --all-features --verbose -- --color=always

run_command cargo +nightly test --workspace --verbose -- --color=always
run_command cargo +nightly test --workspace --all-features --verbose -- --color=always

groupend

groupstart "Tests (miri)"

run_command cargo +nightly miri test --workspace --lib --verbose

groupend

groupstart "Run examples"

run_command cargo +1.85.0 run --example call_c_fn --verbose
run_command cargo +1.85.0 run --manifest-path=examples/no_std_run/Cargo.toml --verbose

run_command cargo +stable run --example call_c_fn --verbose
run_command cargo +stable run --manifest-path=examples/no_std_run/Cargo.toml --verbose

run_command cargo +nightly run --example call_c_fn --verbose
run_command cargo +nightly run --manifest-path=examples/no_std_run/Cargo.toml --verbose

groupend

echo "Script completed successfully"
exit 0