#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_DIR="$ROOT_DIR/tools/verus"
VERUS_SOURCE_DIR="$VERUS_DIR/source"
VERUS_ACTIVATE="$VERUS_DIR/tools/activate"
VERUS_REPO_URL="${VERUS_REPO_URL:-https://github.com/verus-lang/verus.git}"
VERUS_BRANCH="${VERUS_BRANCH:-main}"
FORCE_BOOTSTRAP="${FORCE_BOOTSTRAP:-0}"
VERIFY_TOOLCHAIN="${VERIFY_TOOLCHAIN:-1.94.0-x86_64-unknown-linux-gnu}"
BOOTSTRAP_JOBS="${BOOTSTRAP_JOBS:-${CARGO_BUILD_JOBS:-1}}"
BOOTSTRAP_TARGET="${BOOTSTRAP_TARGET:-x86_64-unknown-linux-gnu}"
CARGO_VERUS="$VERUS_SOURCE_DIR/target-verus/release/cargo-verus"

log() {
    printf '[bootstrap] %s\n' "$*"
}

if [[ ! -d "$VERUS_DIR/.git" ]]; then
    log "cloning Verus ($VERUS_BRANCH) to $VERUS_DIR"
    git clone --branch "$VERUS_BRANCH" --single-branch "$VERUS_REPO_URL" "$VERUS_DIR"
else
    log "using existing Verus checkout at $VERUS_DIR"
fi

if [[ ! -f "$VERUS_ACTIVATE" ]]; then
    echo "[bootstrap][error] missing Verus activate script at $VERUS_ACTIVATE" >&2
    exit 1
fi

if [[ -x "$CARGO_VERUS" && "$FORCE_BOOTSTRAP" != "1" ]]; then
    log "cargo-verus already available at $CARGO_VERUS (set FORCE_BOOTSTRAP=1 to rebuild)"
    exit 0
fi

log "building official Verus tools (jobs=$BOOTSTRAP_JOBS, target=$BOOTSTRAP_TARGET, toolchain=$VERIFY_TOOLCHAIN)"
(
    cd "$VERUS_SOURCE_DIR"
    unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
    export RUSTUP_TOOLCHAIN="$VERIFY_TOOLCHAIN"
    export CARGO_BUILD_TARGET="$BOOTSTRAP_TARGET"
    export CARGO_BUILD_JOBS="$BOOTSTRAP_JOBS"
    # shellcheck disable=SC1091
    source "$VERUS_ACTIVATE"
    vargo build --release --features singular "$@"
    vargo build -p verusdoc "$@"
)

if [[ ! -x "$CARGO_VERUS" ]]; then
    echo "[bootstrap][error] cargo-verus not found after build: $CARGO_VERUS" >&2
    exit 1
fi

log "bootstrap complete: $CARGO_VERUS"