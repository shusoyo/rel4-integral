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
VERUS_RELEASE_DIR="${VERUS_RELEASE_DIR:-$ROOT_DIR/tools/verus/release}"
CARGO_VERUS="${CARGO_VERUS:-$VERUS_RELEASE_DIR/cargo-verus}"

if [[ ! -x "$CARGO_VERUS" ]]; then
    echo "[verify-official][error] missing cargo-verus at $CARGO_VERUS" >&2
    echo "[verify-official][hint] expected release tools under $VERUS_RELEASE_DIR" >&2
    echo "[verify-official][hint] run: ./tools/bootstrap-verus-release.sh" >&2
    exit 1
fi

echo "[verify-official] cargo-verus: $CARGO_VERUS"
echo "[verify-official] package=$VERIFY_PACKAGE features=$VERIFY_FEATURES target=$VERIFY_TARGET jobs=$VERIFY_JOBS"
echo "[verify-official] if output is delayed, Cargo may be waiting on lock /usr/local/cargo/.package-cache"

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
