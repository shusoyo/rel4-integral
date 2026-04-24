use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::resolve::*;

pub open spec fn spec_same_object_if_present(lhs: CapSpec, rhs: CapSpec) -> bool {
	(lhs.object is Some && rhs.object is Some) ==> lhs.object == rhs.object
}

pub open spec fn spec_same_region_if_present(lhs: CapSpec, rhs: CapSpec) -> bool {
	(lhs.region_id is Some && rhs.region_id is Some) ==> lhs.region_id == rhs.region_id
}

pub open spec fn spec_null_cap() -> CapSpec {
	CapSpec {
		kind: CapKind::NullCap,
		object: None,
		region_id: None,
		rights: Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		},
		badge: None,
		cnode: None,
		untyped: None,
	}
}

pub open spec fn spec_empty_slot_entry() -> SlotEntrySpec {
	SlotEntrySpec {
		cap: spec_null_cap(),
		mdb_prev: None,
		mdb_next: None,
		mdb_revocable: false,
		mdb_first_badged: false,
	}
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
	&&& 4 <= src_cap.untyped->Some_0.block_size_bits
}

pub closed spec fn spec_sel4_min_untyped_bits() -> int {
	4
}

pub open spec fn spec_untyped_max_free_index(block_size_bits: int) -> int
	recommends
		spec_sel4_min_untyped_bits() <= block_size_bits,
{
	spec_pow2((block_size_bits - spec_sel4_min_untyped_bits()) as nat)
}

pub open spec fn spec_set_untyped_cap_as_full_result(
	src_before: CapSpec,
	new_cap: CapSpec,
) -> CapSpec {
	if spec_set_untyped_cap_as_full_applies(src_before, new_cap) {
		CapSpec {
			kind: src_before.kind,
			object: src_before.object,
			region_id: src_before.region_id,
			rights: src_before.rights,
			badge: src_before.badge,
			cnode: src_before.cnode,
			untyped: Some(UntypedCapDataSpec {
				block_size_bits: src_before.untyped->Some_0.block_size_bits,
				free_index: spec_untyped_max_free_index(src_before.untyped->Some_0.block_size_bits),
				is_device: src_before.untyped->Some_0.is_device,
			}),
		}
	} else {
		src_before
	}
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
	src_after == spec_set_untyped_cap_as_full_result(src_before, new_cap)
}

}
