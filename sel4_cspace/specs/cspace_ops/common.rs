use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;

pub open spec fn spec_same_object_if_present(lhs: CapSpec, rhs: CapSpec) -> bool {
	(lhs.object is Some && rhs.object is Some) ==> lhs.object == rhs.object
}

pub open spec fn spec_same_region_if_present(lhs: CapSpec, rhs: CapSpec) -> bool {
	(lhs.region_id is Some && rhs.region_id is Some) ==> lhs.region_id == rhs.region_id
}

/// A minimal Stage C notion of "the inserted cap is derivable from the source cap".
///
/// This intentionally stays weaker than a final l4v-style derivation theorem, but is already
/// strong enough to drive the first round of requires/ensures.
pub open spec fn spec_cte_insert_derivable(src_cap: CapSpec, new_cap: CapSpec) -> bool {
	&&& valid_cap(src_cap)
	&&& valid_cap(new_cap)
	&&& new_cap.kind != CapKind::NullCap
	&&& rights_subseteq(new_cap.rights, src_cap.rights)
	&&& spec_same_object_if_present(src_cap, new_cap)
	&&& spec_same_region_if_present(src_cap, new_cap)
}

pub open spec fn spec_set_untyped_cap_as_full_applies(src_cap: CapSpec, new_cap: CapSpec) -> bool {
	&&& src_cap.kind == CapKind::UntypedCap
	&&& new_cap.kind == CapKind::UntypedCap
	&&& src_cap.object is Some
	&&& new_cap.object is Some
	&&& src_cap.object == new_cap.object
	&&& src_cap.untyped is Some
	&&& new_cap.untyped is Some
	&&& src_cap.untyped->Some_0.block_size_bits == new_cap.untyped->Some_0.block_size_bits
}

/// Abstract contract for the l4v/Rust `maskedAsFull` / `setUntypedCapAsFull` effect.
///
/// We deliberately model the structural effect first and postpone the exact free-index arithmetic
/// to the next refinement step.
pub open spec fn spec_set_untyped_cap_as_full_effect(
	src_before: CapSpec,
	new_cap: CapSpec,
	src_after: CapSpec,
) -> bool {
	if spec_set_untyped_cap_as_full_applies(src_before, new_cap) {
		&&& src_after.kind == src_before.kind
		&&& src_after.object == src_before.object
		&&& src_after.region_id == src_before.region_id
		&&& src_after.rights == src_before.rights
		&&& src_after.badge == src_before.badge
		&&& src_after.cnode == src_before.cnode
		&&& src_after.untyped is Some
		&&& src_before.untyped is Some
		&&& src_after.untyped->Some_0.block_size_bits == src_before.untyped->Some_0.block_size_bits
		&&& src_after.untyped->Some_0.is_device == src_before.untyped->Some_0.is_device
		&&& src_after.untyped->Some_0.free_index >= src_before.untyped->Some_0.free_index
	} else {
		src_after == src_before
	}
}

}
