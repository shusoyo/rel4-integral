use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::common::*;

/// Stage 6 contract for `derive_cap`.
///
/// This follows the current Rust implementation shape:
/// `self` contributes the slot-context needed by the untyped case,
/// while the returned capability is otherwise determined by the input
/// capability tag.
pub open spec fn spec_derive_cap_pre(
	state: CSpaceState,
	slot: SlotId,
	capability: CapSpec,
) -> bool
	recommends
		state.has_slot(slot),
{
	&&& state.derive_cap_wf_at(slot)
	&&& state.has_slot(slot)
	&&& state.slot_cap(slot) == capability
	&&& valid_cap(capability)
	&&& capability.kind != CapKind::ArchCap
}

pub open spec fn spec_derive_cap_returns_syscall_error(
	state: CSpaceState,
	slot: SlotId,
	capability: CapSpec,
) -> bool
	recommends
		state.has_slot(slot),
{
	capability.kind == CapKind::UntypedCap
	&& state.ensure_no_children_blocks(slot)
}

pub open spec fn spec_derive_cap_expected_cap(
	state: CSpaceState,
	slot: SlotId,
	capability: CapSpec,
) -> CapSpec
	recommends
		state.has_slot(slot),
{
	match capability.kind {
		CapKind::ZombieCap => spec_null_cap(),
		CapKind::UntypedCap =>
			if state.ensure_no_children_blocks(slot) {
				spec_null_cap()
			} else {
				capability
			},
		#[cfg(not(feature = "kernel_mcs"))]
		CapKind::ReplyCap => spec_null_cap(),
		CapKind::IRQControlCap => spec_null_cap(),
		_ => capability,
	}
}

pub open spec fn spec_derive_cap_post(
	state: CSpaceState,
	slot: SlotId,
	capability: CapSpec,
	derived_cap: CapSpec,
) -> bool
	recommends
		state.has_slot(slot),
{
	derived_cap == spec_derive_cap_expected_cap(state, slot, capability)
}

pub proof fn lemma_spec_derive_cap_post_implies_expected_cap(
	state: CSpaceState,
	slot: SlotId,
	capability: CapSpec,
	derived_cap: CapSpec,
)
	requires
		spec_derive_cap_post(state, slot, capability, derived_cap),
	ensures
		derived_cap == spec_derive_cap_expected_cap(state, slot, capability),
{
}

}
