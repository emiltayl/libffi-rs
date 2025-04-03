:: This script is intended to be executed from the repository's root folder like this:
:: `scripts/ci-checks.bat`.
::
:: The script accepts one of two optional flags: `LINTONLY` and `NOLINT`. `LINTONLY` only checks
:: formatting and lints, while `NOLINT` skips straight to building the code and testing. Supply the
:: flags as the first argument to this script like this: `scripts/ci-checks.bat LINTONLY` or
:: `scripts/ci-checks.bat NOLINT`.

@IF [%1]==[NOLINT] GOTO lintfinished
@call :groupstart "Checking formatting"
cargo +nightly fmt --all --check --verbose || goto failed
cargo +nightly fmt --manifest-path=examples/no_std_run/Cargo.toml --all --check --verbose || goto failed

@call :groupend

@call :groupstart "Linting"

cargo +nightly clippy --all --all-targets --all-features --verbose -- -D warnings || goto failed
cargo +nightly clippy --manifest-path=examples/no_std_run/Cargo.toml --all --all-features --verbose -- -D warnings || goto failed
cmd /C "set CLIPPYFLAGS=-Wclippy::pedantic -Aclippy::semicolon_if_nothing_returned -Aclippy::used-underscore-items -D warnings && set RUSTDOCFLAGS=--no-run --nocapture --test-builder scripts/clippy-driver.bat -Z unstable-options && cargo +nightly test --doc" || goto failed

@call :groupend

@IF [%1]==[LINTONLY] GOTO finished

:lintfinished

@call :groupstart "Building"

cargo +1.85.0 build --workspace --all-targets --all-features --verbose || goto failed
cargo +stable build --workspace --all-targets --all-features --verbose || goto failed
cargo +nightly build --workspace --all-targets --all-features --verbose || goto failed

@call :groupend

@call :groupstart "Tests"

cargo +1.85.0 test --workspace --verbose || goto failed
cargo +stable test --workspace --verbose || goto failed
cargo +nightly test --workspace --verbose || goto failed

@call :groupend

@call :groupstart "Tests (miri)"

cargo +nightly miri test --workspace --lib --verbose || goto failed

@call :groupend

@call :groupstart "Run examples"

cargo +1.85.0 run --example call_c_fn --verbose || goto failed
cargo +1.85.0 run --example qsort --verbose || goto failed
cargo +1.85.0 run --manifest-path=examples/no_std_run/Cargo.toml --verbose || goto failed

cargo +stable run --example call_c_fn --verbose || goto failed
cargo +stable run --example qsort --verbose || goto failed
cargo +stable run --manifest-path=examples/no_std_run/Cargo.toml --verbose || goto failed

cargo +nightly run --example call_c_fn --verbose || goto failed
cargo +nightly run --example qsort --verbose || goto failed
cargo +nightly run --manifest-path=examples/no_std_run/Cargo.toml --verbose || goto failed

@call :groupend

:finished
@echo Script completed successfully
@exit 0

:groupstart
@IF DEFINED CI GOTO gsci
@echo ================================================================================
@echo %~1
@echo ================================================================================
@GOTO :eof
:gsci
@echo ::group::%~1
@GOTO :eof

:groupend
@IF DEFINED CI GOTO geci
@echo(
@GOTO :eof
:geci
@echo ::endgroup::
@GOTO :eof

:failed
@echo Script failed, check output
@exit 1