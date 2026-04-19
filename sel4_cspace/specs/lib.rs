//! Specification entry points for `sel4_cspace` verification.

#![allow(dead_code)]

use vstd::prelude::*;

/// Marker to verify the specs module is linked when feature verus is enabled.
pub const SPECS_MODULE_ENABLED: bool = true;

/// Contracts for trusted boundaries that remain in the TCB for the current phase.
pub mod boundary_assumptions;

/// Internal abstract CSpace model used by Stage B and later proofs.
pub mod abstract_cspace;

/// Primitive-operation specifications layered on top of the abstract CSpace model.
pub mod cspace_ops;

verus! {

pub proof fn specs_smoke_check() {
	boundary_assumptions::boundary_assumptions_smoke_check();
	abstract_cspace::abstract_cspace_smoke_check();
	cspace_ops::cspace_ops_smoke_check();
}

}
