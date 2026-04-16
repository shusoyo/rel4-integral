//! Verus-facing specifications for `sel4_cspace`.
//!
//! This file is wired in via `#[cfg(feature = "verify")] #[path = "../specs/lib.rs"]`
//! from `src/lib.rs`, mirroring the ostd organization pattern.

#![allow(dead_code)]

use vstd::prelude::*;

/// Marker to verify the specs module is linked when `verify` is enabled.
pub const SPECS_MODULE_ENABLED: bool = true;

verus! {

pub proof fn specs_smoke_check() {
}

}
