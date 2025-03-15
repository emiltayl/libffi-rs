#!/bin/bash

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
    echo "Running \`${@}\`"
    output=$(eval "$@" 2>&1) || fail "${output}"
}

run_command_noexit() {
    echo "Running \`${@}\`"
    output=$(eval "$@" 2>&1) 
    if [ $? -ne 0 ]; then
        printf "%s\n" "${output}"
        return 1
    else
        echo "Passed ✅"
    fi
}

# It is ugly setting global variables like this, but it is too tempting...
set_globals() {
    if [ "$1" == "powerpc64-unknown-linux-gnu" ]; then
        GCC_ARCH=powerpc64
        QEMU_ARCH=ppc64
        ABI=gnu
    elif [ "$1" == "powerpc64le-unknown-linux-gnu" ]; then
        GCC_ARCH=powerpc64le
        QEMU_ARCH=ppc64le
        ABI=gnu
    elif [ "$1" == "aarch64-unknown-linux-gnu" ]; then
        GCC_ARCH=aarch64
        QEMU_ARCH=aarch64
        ABI=gnu
    elif [ "$1" == "armv7-unknown-linux-gnueabihf" ]; then
        GCC_ARCH=arm
        QEMU_ARCH=arm
        ABI=gnueabihf
    elif [ "$1" == "riscv64gc-unknown-linux-gnu" ]; then
        GCC_ARCH=riscv64
        QEMU_ARCH=riscv64
        ABI=gnu
    elif [ "$1" == "s390x-unknown-linux-gnu" ]; then
        GCC_ARCH=s390x
        QEMU_ARCH=s390x
        ABI=gnu
    fi
}

FAILED=0
GCC_VERSION=$(gcc --version | grep -oE -m 1 '[0-9]+\.[0-9]+\.[0-9]+' | head -1 | cut -d . -f 1)
TARGETS=("powerpc64le-unknown-linux-gnu" "powerpc64-unknown-linux-gnu " "aarch64-unknown-linux-gnu" "armv7-unknown-linux-gnueabihf" "riscv64gc-unknown-linux-gnu" "s390x-unknown-linux-gnu")
TOOLCHAINS=("1.85.0" "stable" "nightly")
export CARGO_TERM_COLOR=always

if [ "${1}" = "SETUP" ]; then
    groupstart "Setting up dependencies"

    # We will run tests on i686-unknown-linux-gnu as well, but not using qemu
    APT_TO_INSTALL="gcc-${GCC_VERSION}-i686-linux-gnu qemu-user libffi-dev"
    RUSTUP_TARGETS_TO_ADD="i686-unknown-linux-gnu"
    for target in ${TARGETS[@]}; do
        set_globals "${target}"
        APT_TO_INSTALL="${APT_TO_INSTALL} gcc-${GCC_VERSION}-$(echo ${GCC_ARCH} | tr _ -)-linux-${ABI}"
        RUSTUP_TARGETS_TO_ADD="${RUSTUP_TARGETS_TO_ADD} ${target}"
    done

    run_command sudo apt-get update
    run_command sudo apt-get install -y ${APT_TO_INSTALL}
    for toolchain in ${TOOLCHAINS[@]}; do
        run_command rustup toolchain add "${toolchain}"
        run_command rustup target add --toolchain "${toolchain}" "${RUSTUP_TARGETS_TO_ADD}"
    done
    echo "Finished setting up dependencies"
    echo

    groupend
fi

# First test i686-unknown-linux-gnu
export CC="i686-linux-gnu-gcc-${GCC_VERSION}"
export "CARGO_TARGET_I686_UNKNOWN_LINUX_GNU_LINKER=$CC"
groupstart "Testing i686-unknown-linux-gnu"
for toolchain in ${TOOLCHAINS[@]}; do

    run_command_noexit cargo "+${toolchain}" test --target i686-unknown-linux-gnu --workspace --verbose -- --color=always
    if [ $? -ne 0 ]; then
        FAILED=$((FAILED+1))
        if [ -z ${CI+x} ]; then
            echo "Test failed"
        else
            echo "::error::Test failed"
        fi
    fi

done
groupend

for target in ${TARGETS[@]}; do
    groupstart "Testing ${target}"

    set_globals "${target}"

    TARGET_TRIPLE=$(echo "${target}" | tr - _)
    TARGET_TRIPLE=${TARGET_TRIPLE^^}
    export CC="${GCC_ARCH}-linux-${ABI}-gcc-${GCC_VERSION}"
    export "CARGO_TARGET_${TARGET_TRIPLE}_LINKER=$CC"
    export "CARGO_TARGET_${TARGET_TRIPLE}_RUNNER=qemu-$QEMU_ARCH -L /usr/$GCC_ARCH-linux-$ABI/"

    for toolchain in ${TOOLCHAINS[@]}; do
        N=2
        n=0
        passed=0
        until [ $n -ge $N ] || [ $passed -eq 1 ]; do
            if [ $n -gt 0 ]; then
                if [ -z ${CI+x} ]; then
                    echo "QEMU Test failed, retrying"
                else
                    echo "::warning::QEMU Test failed, retrying"
                fi
            fi

            run_command_noexit cargo "+${toolchain}" test --target ${target} --workspace --verbose -- --color=always
            if [ $? -eq 0 ]; then
                passed=1
            else
                n=$((n+1))
            fi
        done

        if [ $passed -ne 1 ]; then
            if [ -z ${CI+x} ]; then
                echo "${N} attempts failed, failing test"
            else
                echo "::error::${N} attempts failed, failing test"
            fi
            FAILED=$((FAILED+1))
        fi
    done

    groupend
done

if [ "${FAILED}" -gt 0 ]; then
    if [ -z ${CI+x} ]; then
        echo "${FAILED} targets failed to execute"
    else
        echo "::error::${FAILED} targets failed to execute"
    fi
    exit 101
else
    echo "All targets successfully tested"
fi