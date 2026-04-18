#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
INSTALL_DIR="${VERUS_INSTALL_DIR:-$ROOT_DIR/tools/verus/release}"
VERUS_RELEASE="${VERUS_RELEASE:-release/0.2026.04.12.f1166c4}"
FORCE_BOOTSTRAP="${FORCE_BOOTSTRAP:-0}"
CARGO_VERUS="$INSTALL_DIR/cargo-verus"

log() {
    printf '[bootstrap] %s\n' "$*"
}

require_cmd() {
    local cmd="$1"
    if ! command -v "$cmd" >/dev/null 2>&1; then
        echo "[bootstrap][error] missing required command: $cmd" >&2
        exit 1
    fi
}

require_cmd curl
require_cmd unzip

if [[ -x "$CARGO_VERUS" && "$FORCE_BOOTSTRAP" != "1" ]]; then
    log "cargo-verus already available at $CARGO_VERUS (set FORCE_BOOTSTRAP=1 to redownload)"
    exit 0
fi

if [[ "$VERUS_RELEASE" == "latest" ]]; then
    api_url="https://api.github.com/repos/verus-lang/verus/releases/latest"
else
    api_url="https://api.github.com/repos/verus-lang/verus/releases/tags/${VERUS_RELEASE}"
fi

release_json="$(curl -fsSL "$api_url")"
release_label="$(echo "$release_json" | grep '"tag_name"' | head -n1 | sed -E 's/.*"([^"]+)".*/\1/' || true)"
asset_url="$(echo "$release_json" | grep 'browser_download_url' | grep 'x86-linux\.zip' | head -n1 | sed -E 's/.*"(https:[^"]+)".*/\1/' || true)"

if [[ -z "${release_label:-}" ]]; then
    release_label="$VERUS_RELEASE"
fi

if [[ -z "${asset_url:-}" ]]; then
    echo "[bootstrap][error] failed to resolve Verus asset URL" >&2
    echo "[bootstrap][hint] set VERUS_RELEASE to a valid release tag or use VERUS_RELEASE=latest" >&2
    exit 1
fi

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "$tmp_dir"
}
trap cleanup EXIT

log "downloading Verus binary ($release_label, platform=x86-linux)"
log "asset: $asset_url"
asset_file="$tmp_dir/verus-x86-linux.zip"
curl -fL "$asset_url" -o "$asset_file"

log "extracting $asset_file"
unzip -q "$asset_file" -d "$tmp_dir"

asset_root="$(dirname "$(find "$tmp_dir" -type f -name cargo-verus | head -n1)")"
if [[ -z "${asset_root:-}" || ! -d "$asset_root" ]]; then
    echo "[bootstrap][error] cargo-verus not found in extracted archive" >&2
    exit 1
fi

log "installing Verus tools to $INSTALL_DIR"
rm -rf "$INSTALL_DIR"
mkdir -p "$INSTALL_DIR"
cp -a "$asset_root/." "$INSTALL_DIR/"

chmod +x "$INSTALL_DIR"/cargo-verus "$INSTALL_DIR"/rust_verify "$INSTALL_DIR"/verus || true

if [[ ! -x "$CARGO_VERUS" ]]; then
    echo "[bootstrap][error] cargo-verus not found after install: $CARGO_VERUS" >&2
    exit 1
fi

log "bootstrap complete: $CARGO_VERUS"