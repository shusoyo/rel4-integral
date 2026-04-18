//! Specification-only definitions for sel4_cspace verification.

#![allow(dead_code)]

use vstd::prelude::*;

/// Marker to verify the specs module is linked when feature verus is enabled.
pub const SPECS_MODULE_ENABLED: bool = true;

verus! {

pub proof fn specs_smoke_check() {
}

}
