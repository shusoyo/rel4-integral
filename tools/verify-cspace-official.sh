#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERIFY_TOOLCHAIN="${VERIFY_TOOLCHAIN:-1.94.0-x86_64-unknown-linux-gnu}"
VERIFY_TARGET="${VERIFY_TARGET:-riscv64gc-unknown-none-elf}"
VERIFY_JOBS="${VERIFY_JOBS:-${CARGO_BUILD_JOBS:-1}}"
VERIFY_PACKAGE="${VERIFY_PACKAGE:-sel4_cspace}"
VERIFY_FEATURES="${VERIFY_FEATURES:-verify}"
VERIFY_MAX_ERRORS="${VERIFY_MAX_ERRORS:-1}"
PLATFORM="${PLATFORM:-spike}"
MARCOS="${MARCOS:-KERNEL_STACK_BITS=12 FASTPATH=true HAVE_FPU=true RISCV_EXT_D=true}"

CARGO_VERUS="$ROOT_DIR/tools/verus/source/target-verus/release/cargo-verus"

if [[ ! -x "$CARGO_VERUS" ]]; then
    echo "[verify-official][error] missing cargo-verus at $CARGO_VERUS" >&2
    echo "[verify-official][hint] run: ./tools/bootstrap-verus-release.sh" >&2
    exit 1
fi

cd "$ROOT_DIR"

env \
    RUSTUP_TOOLCHAIN="$VERIFY_TOOLCHAIN" \
    RUSTC_BOOTSTRAP=1 \
    PLATFORM="$PLATFORM" \
    MARCOS="$MARCOS" \
    CARGO_BUILD_TARGET="$VERIFY_TARGET" \
    CARGO_BUILD_JOBS="$VERIFY_JOBS" \
    "$CARGO_VERUS" verify -p "$VERIFY_PACKAGE" --features "$VERIFY_FEATURES" -- \
        --multiple-errors="$VERIFY_MAX_ERRORS" "$@"
