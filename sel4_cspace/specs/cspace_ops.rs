use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::abstract_cspace::*;

/// Stage C skeleton for CSpace primitive specifications.
///
/// The intent mirrors the l4v `cteInsert` story:
/// 1. destination slot must be empty;
/// 2. the new entry is spliced immediately after the source slot in the MDB;
/// 3. the old `src.mdb_next`, if any, is rewired to point back to the destination slot;
/// 4. `setUntypedCapAsFull` may update the source cap before the new capability is stored.
///
/// We keep the source-cap rewrite abstract for now, but constrain its shape enough that later
/// proofs can refine it to the exact `maskedAsFull` arithmetic.

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

pub open spec fn spec_cte_insert_changed_slots(old_state: CSpaceState, src: SlotId, dest: SlotId) -> Set<SlotId>
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
{
		let base = set![src, dest];
		if old_state.slot_entry(src).mdb_next is Some {
			base.insert(old_state.slot_entry(src).mdb_next.unwrap())
		} else {
			base
		}
}

pub open spec fn spec_cte_insert_pre(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
{
		&&& old_state.wf()
		&&& src != dest
		&&& old_state.has_slot(src)
		&&& old_state.has_slot(dest)
		&&& !old_state.slot_empty(src)
		&&& old_state.slot_empty(dest)
		&&& old_state.slot_entry(dest).mdb_prev is None
		&&& old_state.slot_entry(dest).mdb_next is None
		&&& spec_cte_insert_derivable(old_state.slot_cap(src), new_cap)
}

pub open spec fn spec_cte_insert_mdb_shape(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap_is_revocable: bool,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
		let old_src = old_state.slot_entry(src);
		let new_src = new_state.slot_entry(src);
		let old_next = old_src.mdb_next;
		let new_dest = new_state.slot_entry(dest);

		&&& new_src.mdb_prev == old_src.mdb_prev
		&&& new_src.mdb_next == Some(dest)
		&&& new_src.mdb_revocable == old_src.mdb_revocable
		&&& new_src.mdb_first_badged == old_src.mdb_first_badged
		&&& new_dest.mdb_prev == Some(src)
		&&& new_dest.mdb_next == old_next
		&&& new_dest.mdb_revocable == new_cap_is_revocable
		&&& new_dest.mdb_first_badged == new_cap_is_revocable
		&&& old_next is Some ==> {
			let next = old_next.unwrap();
			&&& new_state.has_slot(next)
			&&& new_state.slot_entry(next).mdb_prev == Some(dest)
			&&& new_state.slot_cap(next) == old_state.slot_cap(next)
			&&& new_state.slot_entry(next).mdb_next == old_state.slot_entry(next).mdb_next
			&&& new_state.slot_entry(next).mdb_revocable == old_state.slot_entry(next).mdb_revocable
			&&& new_state.slot_entry(next).mdb_first_badged == old_state.slot_entry(next).mdb_first_badged
		}
}

pub open spec fn spec_cte_insert_post(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
	new_cap_is_revocable: bool,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
		let changed = spec_cte_insert_changed_slots(old_state, src, dest);

		&&& new_state.wf()
		&&& new_state.roots =~= old_state.roots
		&&& new_state.cnode_slots =~= old_state.cnode_slots
		&&& new_state.cnode_lookup =~= old_state.cnode_lookup
		&&& slots_unchanged_except(old_state, new_state, changed)
		&&& spec_set_untyped_cap_as_full_effect(
			old_state.slot_cap(src),
			new_cap,
			new_state.slot_cap(src),
		)
		&&& new_state.slot_cap(dest) == new_cap
		&&& spec_cte_insert_mdb_shape(old_state, new_state, src, dest, new_cap_is_revocable)
		&&& new_state.mdb_links(src, dest)
		&&& rights_subseteq(new_state.slot_cap(dest).rights, old_state.slot_cap(src).rights)
		&&& spec_same_object_if_present(old_state.slot_cap(src), new_state.slot_cap(dest))
		&&& spec_same_region_if_present(old_state.slot_cap(src), new_state.slot_cap(dest))
	}

pub open spec fn spec_cte_insert(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
	new_cap_is_revocable: bool,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
		&&& spec_cte_insert_pre(old_state, src, dest, new_cap)
		&&& spec_cte_insert_post(old_state, new_state, src, dest, new_cap, new_cap_is_revocable)
	}

pub open spec fn spec_cte_move_cap_compatible(
	old_state: CSpaceState,
	src: SlotId,
	new_cap: CapSpec,
) -> bool
	recommends
		old_state.has_slot(src),
{
		let old_src = old_state.slot_entry(src);
		let old_cap = old_state.slot_cap(src);

		&&& valid_cap(new_cap)
		&&& new_cap.kind != CapKind::NullCap
		&&& old_src.mdb_prev is Some && old_state.same_object(old_src.mdb_prev.unwrap(), src) ==>
			spec_same_object_if_present(old_state.slot_cap(old_src.mdb_prev.unwrap()), new_cap)
		&&& old_src.mdb_next is Some && old_state.same_object(src, old_src.mdb_next.unwrap()) ==>
			spec_same_object_if_present(new_cap, old_state.slot_cap(old_src.mdb_next.unwrap()))
		&&& old_src.mdb_prev is Some && old_state.immediate_derived(old_src.mdb_prev.unwrap(), src) ==> {
			&&& spec_same_region_if_present(old_state.slot_cap(old_src.mdb_prev.unwrap()), new_cap)
			&&& rights_subseteq(new_cap.rights, old_cap.rights)
			&&& rights_subseteq(new_cap.rights, old_state.slot_cap(old_src.mdb_prev.unwrap()).rights)
		}
		&&& old_src.mdb_next is Some && old_state.immediate_derived(src, old_src.mdb_next.unwrap()) ==> {
			&&& spec_same_region_if_present(new_cap, old_state.slot_cap(old_src.mdb_next.unwrap()))
			&&& rights_subseteq(old_state.slot_cap(old_src.mdb_next.unwrap()).rights, new_cap.rights)
		}
}

pub open spec fn spec_cte_move_changed_slots(old_state: CSpaceState, src: SlotId, dest: SlotId) -> Set<SlotId>
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
{
		let with_src_dest = set![src, dest];
		let with_prev = if old_state.slot_entry(src).mdb_prev is Some {
			with_src_dest.insert(old_state.slot_entry(src).mdb_prev.unwrap())
		} else {
			with_src_dest
		};
		if old_state.slot_entry(src).mdb_next is Some {
			with_prev.insert(old_state.slot_entry(src).mdb_next.unwrap())
		} else {
			with_prev
		}
}

pub open spec fn spec_cte_move_pre(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
{
		&&& old_state.wf()
		&&& src != dest
		&&& old_state.has_slot(src)
		&&& old_state.has_slot(dest)
		&&& !old_state.slot_empty(src)
		&&& old_state.slot_empty(dest)
		&&& old_state.slot_entry(dest).mdb_prev is None
		&&& old_state.slot_entry(dest).mdb_next is None
		&&& spec_cte_move_cap_compatible(old_state, src, new_cap)
}

pub open spec fn spec_cte_move_mdb_shape(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
		let old_src = old_state.slot_entry(src);
		let new_src = new_state.slot_entry(src);
		let new_dest = new_state.slot_entry(dest);

		&&& new_dest.mdb_prev == old_src.mdb_prev
		&&& new_dest.mdb_next == old_src.mdb_next
		&&& new_dest.mdb_revocable == old_src.mdb_revocable
		&&& new_dest.mdb_first_badged == old_src.mdb_first_badged
		&&& new_src.mdb_prev is None
		&&& new_src.mdb_next is None
		&&& !new_src.mdb_revocable
		&&& !new_src.mdb_first_badged
		&&& old_src.mdb_prev is Some ==> {
			let prev = old_src.mdb_prev.unwrap();
			&&& new_state.has_slot(prev)
			&&& new_state.slot_entry(prev).mdb_next == Some(dest)
			&&& new_state.slot_entry(prev).mdb_prev == old_state.slot_entry(prev).mdb_prev
			&&& new_state.slot_entry(prev).mdb_revocable == old_state.slot_entry(prev).mdb_revocable
			&&& new_state.slot_entry(prev).mdb_first_badged == old_state.slot_entry(prev).mdb_first_badged
			&&& new_state.slot_cap(prev) == old_state.slot_cap(prev)
		}
		&&& old_src.mdb_next is Some ==> {
			let next = old_src.mdb_next.unwrap();
			&&& new_state.has_slot(next)
			&&& new_state.slot_entry(next).mdb_prev == Some(dest)
			&&& new_state.slot_entry(next).mdb_next == old_state.slot_entry(next).mdb_next
			&&& new_state.slot_entry(next).mdb_revocable == old_state.slot_entry(next).mdb_revocable
			&&& new_state.slot_entry(next).mdb_first_badged == old_state.slot_entry(next).mdb_first_badged
			&&& new_state.slot_cap(next) == old_state.slot_cap(next)
		}
}

pub open spec fn spec_cte_move_post(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
		let changed = spec_cte_move_changed_slots(old_state, src, dest);

		&&& new_state.wf()
		&&& new_state.roots =~= old_state.roots
		&&& new_state.cnode_slots =~= old_state.cnode_slots
		&&& new_state.cnode_lookup =~= old_state.cnode_lookup
		&&& slots_unchanged_except(old_state, new_state, changed)
		&&& new_state.slot_cap(dest) == new_cap
		&&& new_state.slot_empty(src)
		&&& spec_cte_move_mdb_shape(old_state, new_state, src, dest)
}

pub open spec fn spec_cte_move(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
) -> bool
	recommends
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
{
	&&& spec_cte_move_pre(old_state, src, dest, new_cap)
	&&& spec_cte_move_post(old_state, new_state, src, dest, new_cap)
}

pub open spec fn spec_swap_slot_ref(ptr: Option<SlotId>, slot1: SlotId, slot2: SlotId) -> Option<SlotId> {
	if ptr is Some {
		let slot = ptr.unwrap();
		if slot == slot1 {
			Some(slot2)
		} else if slot == slot2 {
			Some(slot1)
		} else {
			ptr
		}
	} else {
		ptr
	}
}

pub open spec fn spec_cte_swap_root_compatible(
	old_state: CSpaceState,
	slot: SlotId,
	incoming_cap: CapSpec,
) -> bool {
	!old_state.roots.contains(slot) || incoming_cap.kind == CapKind::CNodeCap
}

pub open spec fn spec_cte_swap_changed_slots(
	old_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
) -> Set<SlotId>
	recommends
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
{
		let with_slots = set![slot1, slot2];
		let with_slot1_prev = if old_state.slot_entry(slot1).mdb_prev is Some {
			with_slots.insert(old_state.slot_entry(slot1).mdb_prev.unwrap())
		} else {
			with_slots
		};
		let with_slot1_next = if old_state.slot_entry(slot1).mdb_next is Some {
			with_slot1_prev.insert(old_state.slot_entry(slot1).mdb_next.unwrap())
		} else {
			with_slot1_prev
		};
		let with_slot2_prev = if old_state.slot_entry(slot2).mdb_prev is Some {
			with_slot1_next.insert(old_state.slot_entry(slot2).mdb_prev.unwrap())
		} else {
			with_slot1_next
		};
		if old_state.slot_entry(slot2).mdb_next is Some {
			with_slot2_prev.insert(old_state.slot_entry(slot2).mdb_next.unwrap())
		} else {
			with_slot2_prev
		}
}

pub open spec fn spec_cte_swap_pre(
	old_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
	cap1: CapSpec,
	cap2: CapSpec,
) -> bool
	recommends
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
{
		&&& old_state.wf()
		&&& slot1 != slot2
		&&& old_state.has_slot(slot1)
		&&& old_state.has_slot(slot2)
		&&& !old_state.slot_empty(slot1)
		&&& !old_state.slot_empty(slot2)
		&&& spec_cte_move_cap_compatible(old_state, slot1, cap1)
		&&& spec_cte_move_cap_compatible(old_state, slot2, cap2)
		&&& spec_cte_swap_root_compatible(old_state, slot1, cap2)
		&&& spec_cte_swap_root_compatible(old_state, slot2, cap1)
}

/// `cteSwap` exchanges two `(cap, mdb-position)` pairs.
///
/// When the swapped nodes are MDB siblings, references to the partner slot must be rewritten,
/// so we model the slot-id renaming explicitly with `spec_swap_slot_ref`.
pub open spec fn spec_cte_swap_mdb_shape(
	old_state: CSpaceState,
	new_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
) -> bool
	recommends
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
		new_state.has_slot(slot1),
		new_state.has_slot(slot2),
{
		let old_1 = old_state.slot_entry(slot1);
		let old_2 = old_state.slot_entry(slot2);
		let new_1 = new_state.slot_entry(slot1);
		let new_2 = new_state.slot_entry(slot2);

		&&& new_1.mdb_prev == spec_swap_slot_ref(old_2.mdb_prev, slot1, slot2)
		&&& new_1.mdb_next == spec_swap_slot_ref(old_2.mdb_next, slot1, slot2)
		&&& new_1.mdb_revocable == old_2.mdb_revocable
		&&& new_1.mdb_first_badged == old_2.mdb_first_badged
		&&& new_2.mdb_prev == spec_swap_slot_ref(old_1.mdb_prev, slot1, slot2)
		&&& new_2.mdb_next == spec_swap_slot_ref(old_1.mdb_next, slot1, slot2)
		&&& new_2.mdb_revocable == old_1.mdb_revocable
		&&& new_2.mdb_first_badged == old_1.mdb_first_badged
		&&& old_1.mdb_prev is Some && old_1.mdb_prev.unwrap() != slot2 ==> {
			let prev = old_1.mdb_prev.unwrap();
			&&& new_state.has_slot(prev)
			&&& new_state.slot_entry(prev).mdb_next == Some(slot2)
			&&& new_state.slot_entry(prev).mdb_prev == old_state.slot_entry(prev).mdb_prev
			&&& new_state.slot_entry(prev).mdb_revocable == old_state.slot_entry(prev).mdb_revocable
			&&& new_state.slot_entry(prev).mdb_first_badged == old_state.slot_entry(prev).mdb_first_badged
			&&& new_state.slot_cap(prev) == old_state.slot_cap(prev)
		}
		&&& old_1.mdb_next is Some && old_1.mdb_next.unwrap() != slot2 ==> {
			let next = old_1.mdb_next.unwrap();
			&&& new_state.has_slot(next)
			&&& new_state.slot_entry(next).mdb_prev == Some(slot2)
			&&& new_state.slot_entry(next).mdb_next == old_state.slot_entry(next).mdb_next
			&&& new_state.slot_entry(next).mdb_revocable == old_state.slot_entry(next).mdb_revocable
			&&& new_state.slot_entry(next).mdb_first_badged == old_state.slot_entry(next).mdb_first_badged
			&&& new_state.slot_cap(next) == old_state.slot_cap(next)
		}
		&&& old_2.mdb_prev is Some && old_2.mdb_prev.unwrap() != slot1 ==> {
			let prev = old_2.mdb_prev.unwrap();
			&&& new_state.has_slot(prev)
			&&& new_state.slot_entry(prev).mdb_next == Some(slot1)
			&&& new_state.slot_entry(prev).mdb_prev == old_state.slot_entry(prev).mdb_prev
			&&& new_state.slot_entry(prev).mdb_revocable == old_state.slot_entry(prev).mdb_revocable
			&&& new_state.slot_entry(prev).mdb_first_badged == old_state.slot_entry(prev).mdb_first_badged
			&&& new_state.slot_cap(prev) == old_state.slot_cap(prev)
		}
		&&& old_2.mdb_next is Some && old_2.mdb_next.unwrap() != slot1 ==> {
			let next = old_2.mdb_next.unwrap();
			&&& new_state.has_slot(next)
			&&& new_state.slot_entry(next).mdb_prev == Some(slot1)
			&&& new_state.slot_entry(next).mdb_next == old_state.slot_entry(next).mdb_next
			&&& new_state.slot_entry(next).mdb_revocable == old_state.slot_entry(next).mdb_revocable
			&&& new_state.slot_entry(next).mdb_first_badged == old_state.slot_entry(next).mdb_first_badged
			&&& new_state.slot_cap(next) == old_state.slot_cap(next)
		}
}

pub open spec fn spec_cte_swap_post(
	old_state: CSpaceState,
	new_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
	cap1: CapSpec,
	cap2: CapSpec,
) -> bool
	recommends
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
		new_state.has_slot(slot1),
		new_state.has_slot(slot2),
{
		let changed = spec_cte_swap_changed_slots(old_state, slot1, slot2);

		&&& new_state.wf()
		&&& new_state.roots =~= old_state.roots
		&&& new_state.cnode_slots =~= old_state.cnode_slots
		&&& new_state.cnode_lookup =~= old_state.cnode_lookup
		&&& slots_unchanged_except(old_state, new_state, changed)
		&&& new_state.slot_cap(slot1) == cap2
		&&& new_state.slot_cap(slot2) == cap1
		&&& spec_cte_swap_mdb_shape(old_state, new_state, slot1, slot2)
}

pub open spec fn spec_cte_swap(
	old_state: CSpaceState,
	new_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
	cap1: CapSpec,
	cap2: CapSpec,
) -> bool
	recommends
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
		new_state.has_slot(slot1),
		new_state.has_slot(slot2),
{
	&&& spec_cte_swap_pre(old_state, slot1, slot2, cap1, cap2)
	&&& spec_cte_swap_post(old_state, new_state, slot1, slot2, cap1, cap2)
}

pub ghost enum ResolveAddressBitsStatusSpec {
	Success,
	LookupFault,
}

pub ghost enum ResolveAddressBitsFaultSpec {
	InvalidRoot,
	GuardMismatch {
		bits_left: int,
		guard_found: int,
		guard_size: int,
	},
	DepthMismatch {
		bits_left: int,
		bits_found: int,
	},
}

#[verifier::ext_equal]
pub ghost struct ResolveAddressBitsResultSpec {
	pub status: ResolveAddressBitsStatusSpec,
	pub slot: Option<SlotId>,
	pub bits_remaining: int,
	pub fault: Option<ResolveAddressBitsFaultSpec>,
}

pub open spec fn spec_pow2(bits: nat) -> int
	decreases bits,
{
	if bits == 0 {
		1
	} else {
		2 * spec_pow2((bits - 1) as nat)
	}
}

pub open spec fn spec_extract_bits(value: int, start: int, width: int) -> int
	recommends
		0 <= value,
		0 <= start,
		0 <= width,
{
	(value / spec_pow2(start as nat)) % spec_pow2(width as nat)
}

pub open spec fn spec_cnode_level_bits(cnode_cap: CapSpec) -> int
	recommends
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
{
	cnode_cap.cnode->Some_0.guard_size + cnode_cap.cnode->Some_0.radix_bits
}

pub open spec fn spec_resolve_guard_value(
	cnode_cap: CapSpec,
	cap_ptr: int,
	bits: int,
) -> int
	recommends
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		0 <= cap_ptr,
		0 <= bits,
{
	let guard_bits = cnode_cap.cnode->Some_0.guard_size;
	if guard_bits <= bits {
		spec_extract_bits(cap_ptr, bits - guard_bits, guard_bits)
	} else {
		0
	}
}

pub open spec fn spec_resolve_guard_matches(
	cnode_cap: CapSpec,
	cap_ptr: int,
	bits: int,
) -> bool
	recommends
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		0 <= cap_ptr,
		0 <= bits,
{
	let guard_bits = cnode_cap.cnode->Some_0.guard_size;
	if guard_bits <= bits {
		spec_resolve_guard_value(cnode_cap, cap_ptr, bits) == cnode_cap.cnode->Some_0.guard
	} else {
		false
	}
}

pub open spec fn spec_resolve_address_bits_next_slot(
	state: CSpaceState,
	cnode_cap: CapSpec,
	cap_ptr: int,
	bits: int,
) -> Option<SlotId>
	recommends
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		cnode_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
{
	let level_bits = spec_cnode_level_bits(cnode_cap);
	if level_bits <= bits {
		let offset = spec_extract_bits(cap_ptr, bits - level_bits, cnode_cap.cnode->Some_0.radix_bits);
		state.cnode_slot_at(cnode_cap.object->Some_0, offset)
	} else {
		None
	}
}

/// Stage C bridge from the finite `cnode_lookup` map to l4v's total `locateSlotCap`.
///
/// We currently keep the lookup table finite in the abstract model, so `resolve_address_bits`
/// assumes every valid offset inside any visible CNode maps to some slot.
pub open spec fn spec_cnode_cap_lookup_total(
	state: CSpaceState,
	cnode_cap: CapSpec,
) -> bool
	recommends
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		cnode_cap.object is Some,
		0 <= cnode_cap.cnode->Some_0.radix_bits,
{
	forall|offset: int|
		0 <= offset < spec_pow2(cnode_cap.cnode->Some_0.radix_bits as nat) ==>
			state.cnode_cap_slot_at(cnode_cap, offset) is Some
}

pub open spec fn spec_cspace_lookup_total(state: CSpaceState) -> bool {
	forall|slot: SlotId|
		state.has_slot(slot)
		&& state.slot_cap(slot).kind == CapKind::CNodeCap
		&& state.slot_cap(slot).cnode is Some
		&& state.slot_cap(slot).object is Some
		==> spec_cnode_cap_lookup_total(state, state.slot_cap(slot))
}

/// Structural Stage C contract for `resolve_address_bits`.
///
/// This already matches the l4v/Rust control flow on:
/// 1. positive `levelBits = guard + radix`;
/// 2. exact guard matching against the unresolved prefix of `cap_ptr`;
/// 3. offset-based slot lookup inside the current CNode;
/// 4. either consuming all bits, or stopping early on the first non-CNode capability.
pub open spec fn spec_resolve_address_bits_success(
	state: CSpaceState,
	cnode_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	slot: SlotId,
	bits_left: int,
) -> bool
	recommends
		0 <= cap_ptr,
		0 <= bits,
		state.has_slot(slot),
	decreases bits,
{
	if !(cnode_cap.kind == CapKind::CNodeCap
		&& cnode_cap.cnode is Some
		&& cnode_cap.object is Some) {
		false
	} else {
		let level_bits = spec_cnode_level_bits(cnode_cap);
		let next_slot = spec_resolve_address_bits_next_slot(state, cnode_cap, cap_ptr, bits);
		if !(level_bits > 0
			&& spec_resolve_guard_matches(cnode_cap, cap_ptr, bits)
			&& level_bits <= bits
			&& next_slot is Some) {
			false
		} else {
			let next = next_slot.unwrap();
			if !(state.has_slot(next)) {
				false
			} else if bits == level_bits {
				&&& slot == next
				&&& bits_left == 0
			} else {
				let remaining = bits - level_bits;
				let next_cap = state.slot_cap(next);
				if next_cap.kind == CapKind::CNodeCap {
					spec_resolve_address_bits_success(state, next_cap, cap_ptr, remaining, slot, bits_left)
				} else {
					&&& slot == next
					&&& bits_left == remaining
				}
			}
		}
	}
}

pub open spec fn spec_resolve_address_bits_pre(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
) -> bool {
	&&& state.wf()
	&&& spec_cspace_lookup_total(state)
	&&& 0 <= cap_ptr
	&&& 0 <= bits <= cspace_word_bits()
	&&& (root_cap.kind == CapKind::CNodeCap ==> {
		&&& root_cap.cnode is Some
		&&& root_cap.object is Some
		&&& 0 < spec_cnode_level_bits(root_cap)
		&&& spec_cnode_cap_lookup_total(state, root_cap)
	})
}

pub open spec fn spec_resolve_address_bits_fault(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		0 <= cap_ptr,
		0 <= bits,
	decreases bits,
{
	if !(root_cap.kind == CapKind::CNodeCap
		&& root_cap.cnode is Some
		&& root_cap.object is Some) {
		&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
		&&& result.slot is None
		&&& result.bits_remaining == bits
		&&& result.fault == Some(ResolveAddressBitsFaultSpec::InvalidRoot)
	} else {
		let level_bits = spec_cnode_level_bits(root_cap);
		let guard_bits = root_cap.cnode->Some_0.guard_size;
		if !spec_resolve_guard_matches(root_cap, cap_ptr, bits) {
			&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
			&&& result.slot is None
			&&& result.bits_remaining == bits
			&&& result.fault == Some(ResolveAddressBitsFaultSpec::GuardMismatch {
				bits_left: bits,
				guard_found: root_cap.cnode->Some_0.guard,
				guard_size: guard_bits,
			})
		} else if !(level_bits <= bits) {
			&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
			&&& result.slot is None
			&&& result.bits_remaining == bits
			&&& result.fault == Some(ResolveAddressBitsFaultSpec::DepthMismatch {
				bits_left: bits,
				bits_found: level_bits,
			})
		} else {
			let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
			if !(level_bits > 0 && next_slot is Some) {
				false
			} else {
				let next = next_slot.unwrap();
				if !(state.has_slot(next)) {
					false
				} else if bits == level_bits {
					false
				} else {
					let remaining = bits - level_bits;
					let next_cap = state.slot_cap(next);
					if next_cap.kind == CapKind::CNodeCap {
						spec_resolve_address_bits_fault(state, next_cap, cap_ptr, remaining, result)
					} else {
						false
					}
				}
			}
		}
	}
}

pub open spec fn spec_resolve_address_bits_post(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		0 <= cap_ptr,
		0 <= bits,
{
	if result.status == ResolveAddressBitsStatusSpec::Success {
		&&& result.slot is Some
		&&& result.fault is None
		&&& state.has_slot(result.slot.unwrap())
		&&& 0 <= result.bits_remaining <= bits
		&&& spec_resolve_address_bits_success(
			state,
			root_cap,
			cap_ptr,
			bits,
			result.slot.unwrap(),
			result.bits_remaining,
		)
	} else {
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result)
	}
}

pub open spec fn spec_resolve_address_bits(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		0 <= cap_ptr,
		0 <= bits,
{
	&&& spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits)
	&&& spec_resolve_address_bits_post(state, root_cap, cap_ptr, bits, result)
}

pub proof fn cte_insert_smoke_check() {
		let no_rights = Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let rw_rights = Rights {
			can_read: true,
			can_write: true,
			can_grant: false,
			can_grant_reply: false,
		};

		let r_rights = Rights {
			can_read: true,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let root_cnode = ObjectRef {
			id: 0,
			kind: ObjectKind::CNode,
		};

		let endpoint_object = ObjectRef {
			id: 1,
			kind: ObjectKind::Endpoint,
		};

		let root_cap = CapSpec {
			kind: CapKind::CNodeCap,
			object: Some(root_cnode),
			region_id: Some(0),
			rights: no_rights,
			badge: None,
			cnode: Some(CNodeCapDataSpec {
				radix_bits: 4,
				guard: 0,
				guard_size: 0,
			}),
			untyped: None,
		};

		let src_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(1),
			rights: rw_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let inserted_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(1),
			rights: r_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let null_cap = CapSpec {
			kind: CapKind::NullCap,
			object: None,
			region_id: None,
			rights: no_rights,
			badge: None,
			cnode: None,
			untyped: None,
		};

		let old_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: src_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: null_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int
				]
			],
			roots: set![1int],
		};

		let new_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: src_cap,
					mdb_prev: None,
					mdb_next: Some(3int),
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: inserted_cap,
					mdb_prev: Some(2int),
					mdb_next: None,
					mdb_revocable: true,
					mdb_first_badged: true,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int
				]
			],
			roots: set![1int],
		};

		assert(spec_cte_insert_derivable(src_cap, inserted_cap));
		assert(spec_set_untyped_cap_as_full_effect(src_cap, inserted_cap, src_cap));
		assert(spec_cte_insert_changed_slots(old_state, 2int, 3int) =~= set![2int, 3int]);
		assert(slots_unchanged_except(old_state, new_state, set![2int, 3int]));
		assert(spec_cte_insert_mdb_shape(old_state, new_state, 2int, 3int, true));
}

pub proof fn cte_move_smoke_check() {
		let no_rights = Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let rw_rights = Rights {
			can_read: true,
			can_write: true,
			can_grant: false,
			can_grant_reply: false,
		};

		let r_rights = Rights {
			can_read: true,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let root_cnode = ObjectRef {
			id: 10,
			kind: ObjectKind::CNode,
		};

		let endpoint_object = ObjectRef {
			id: 11,
			kind: ObjectKind::Endpoint,
		};

		let root_cap = CapSpec {
			kind: CapKind::CNodeCap,
			object: Some(root_cnode),
			region_id: Some(10),
			rights: no_rights,
			badge: None,
			cnode: Some(CNodeCapDataSpec {
				radix_bits: 4,
				guard: 0,
				guard_size: 0,
			}),
			untyped: None,
		};

		let parent_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(11),
			rights: rw_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let src_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(11),
			rights: r_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let child_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(11),
			rights: r_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let null_cap = CapSpec {
			kind: CapKind::NullCap,
			object: None,
			region_id: None,
			rights: no_rights,
			badge: None,
			cnode: None,
			untyped: None,
		};

		let old_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: parent_cap,
					mdb_prev: None,
					mdb_next: Some(3int),
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: src_cap,
					mdb_prev: Some(2int),
					mdb_next: Some(4int),
					mdb_revocable: true,
					mdb_first_badged: false,
				},
				4int => SlotEntrySpec {
					cap: child_cap,
					mdb_prev: Some(3int),
					mdb_next: None,
					mdb_revocable: true,
					mdb_first_badged: false,
				},
				5int => SlotEntrySpec {
					cap: null_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int, 4int, 5int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int,
					3int => 4int,
					4int => 5int
				]
			],
			roots: set![1int],
		};

		let moved_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: parent_cap,
					mdb_prev: None,
					mdb_next: Some(5int),
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: null_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				4int => SlotEntrySpec {
					cap: child_cap,
					mdb_prev: Some(5int),
					mdb_next: None,
					mdb_revocable: true,
					mdb_first_badged: false,
				},
				5int => SlotEntrySpec {
					cap: src_cap,
					mdb_prev: Some(2int),
					mdb_next: Some(4int),
					mdb_revocable: true,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int, 4int, 5int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int,
					3int => 4int,
					4int => 5int
				]
			],
			roots: set![1int],
		};

		assert(spec_cte_move_cap_compatible(old_state, 3int, src_cap));
		assert(spec_cte_move_changed_slots(old_state, 3int, 5int) =~= set![2int, 3int, 4int, 5int]);
		assert(slots_unchanged_except(old_state, moved_state, set![2int, 3int, 4int, 5int]));
		assert(spec_cte_move_mdb_shape(old_state, moved_state, 3int, 5int));
}

pub proof fn cte_swap_smoke_check() {
		let no_rights = Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let rw_rights = Rights {
			can_read: true,
			can_write: true,
			can_grant: false,
			can_grant_reply: false,
		};

		let r_rights = Rights {
			can_read: true,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let root_cnode = ObjectRef {
			id: 20,
			kind: ObjectKind::CNode,
		};

		let endpoint_object = ObjectRef {
			id: 21,
			kind: ObjectKind::Endpoint,
		};

		let root_cap = CapSpec {
			kind: CapKind::CNodeCap,
			object: Some(root_cnode),
			region_id: Some(20),
			rights: no_rights,
			badge: None,
			cnode: Some(CNodeCapDataSpec {
				radix_bits: 4,
				guard: 0,
				guard_size: 0,
			}),
			untyped: None,
		};

		let parent_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(21),
			rights: rw_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let cap1 = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(21),
			rights: rw_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let cap2 = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(21),
			rights: r_rights,
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let old_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: parent_cap,
					mdb_prev: None,
					mdb_next: Some(3int),
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: cap1,
					mdb_prev: Some(2int),
					mdb_next: Some(4int),
					mdb_revocable: true,
					mdb_first_badged: false,
				},
				4int => SlotEntrySpec {
					cap: cap2,
					mdb_prev: Some(3int),
					mdb_next: None,
					mdb_revocable: true,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int, 4int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int,
					3int => 4int
				]
			],
			roots: set![1int],
		};

		let swapped_state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: parent_cap,
					mdb_prev: None,
					mdb_next: Some(4int),
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: cap2,
					mdb_prev: Some(4int),
					mdb_next: None,
					mdb_revocable: true,
					mdb_first_badged: false,
				},
				4int => SlotEntrySpec {
					cap: cap1,
					mdb_prev: Some(2int),
					mdb_next: Some(3int),
					mdb_revocable: true,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![1int, 2int, 3int, 4int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 1int,
					1int => 2int,
					2int => 3int,
					3int => 4int
				]
			],
			roots: set![1int],
		};

		assert(spec_cte_move_cap_compatible(old_state, 3int, cap1));
		assert(spec_cte_move_cap_compatible(old_state, 4int, cap2));
		assert(spec_cte_swap_root_compatible(old_state, 3int, cap2));
		assert(spec_cte_swap_root_compatible(old_state, 4int, cap1));
		assert(spec_cte_swap_changed_slots(old_state, 3int, 4int) =~= set![2int, 3int, 4int]);
		assert(slots_unchanged_except(old_state, swapped_state, set![2int, 3int, 4int]));
		assert(spec_cte_swap_mdb_shape(old_state, swapped_state, 3int, 4int));
}

	pub proof fn resolve_address_bits_smoke_check() {
		let no_rights = Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		};

		let root_cnode = ObjectRef {
			id: 30,
			kind: ObjectKind::CNode,
		};

		let child_cnode = ObjectRef {
			id: 31,
			kind: ObjectKind::CNode,
		};

		let endpoint_object = ObjectRef {
			id: 32,
			kind: ObjectKind::Endpoint,
		};

		let root_cap = CapSpec {
			kind: CapKind::CNodeCap,
			object: Some(root_cnode),
			region_id: Some(30),
			rights: no_rights,
			badge: None,
			cnode: Some(CNodeCapDataSpec {
				radix_bits: 1,
				guard: 0,
				guard_size: 1,
			}),
			untyped: None,
		};

		let child_cap = CapSpec {
			kind: CapKind::CNodeCap,
			object: Some(child_cnode),
			region_id: Some(31),
			rights: no_rights,
			badge: None,
			cnode: Some(CNodeCapDataSpec {
				radix_bits: 1,
				guard: 0,
				guard_size: 1,
			}),
			untyped: None,
		};

		let leaf_cap = CapSpec {
			kind: CapKind::EndpointCap,
			object: Some(endpoint_object),
			region_id: Some(32),
			rights: Rights {
				can_read: true,
				can_write: false,
				can_grant: false,
				can_grant_reply: false,
			},
			badge: Some(0),
			cnode: None,
			untyped: None,
		};

		let null_cap = CapSpec {
			kind: CapKind::NullCap,
			object: None,
			region_id: None,
			rights: no_rights,
			badge: None,
			cnode: None,
			untyped: None,
		};

		let state = CSpaceState {
			slots: map![
				1int => SlotEntrySpec {
					cap: root_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				2int => SlotEntrySpec {
					cap: child_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				3int => SlotEntrySpec {
					cap: leaf_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				4int => SlotEntrySpec {
					cap: null_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				},
				5int => SlotEntrySpec {
					cap: null_cap,
					mdb_prev: None,
					mdb_next: None,
					mdb_revocable: false,
					mdb_first_badged: false,
				}
			],
			cnode_slots: map![
				root_cnode => set![2int, 4int],
				child_cnode => set![3int, 5int]
			],
			cnode_lookup: map![
				root_cnode => map![
					0int => 2int,
					1int => 4int
				],
				child_cnode => map![
					0int => 3int,
					1int => 5int
				]
			],
			roots: set![1int],
		};

		let cap_ptr = 0int;
		let shallow_cap_ptr = 4int;
		let guard_mismatch_cap_ptr = 8int;

		let success_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::Success,
			slot: Some(3int),
			bits_remaining: 0,
			fault: None,
		};
		let shallow_success_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::Success,
			slot: Some(4int),
			bits_remaining: 2,
			fault: None,
		};
		let invalid_root_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::LookupFault,
			slot: None,
			bits_remaining: 4,
			fault: Some(ResolveAddressBitsFaultSpec::InvalidRoot),
		};
		let guard_mismatch_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::LookupFault,
			slot: None,
			bits_remaining: 4,
			fault: Some(ResolveAddressBitsFaultSpec::GuardMismatch {
				bits_left: 4,
				guard_found: 0,
				guard_size: 1,
			}),
		};
		let depth_mismatch_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::LookupFault,
			slot: None,
			bits_remaining: 1,
			fault: Some(ResolveAddressBitsFaultSpec::DepthMismatch {
				bits_left: 1,
				bits_found: 2,
			}),
		};

		assert(spec_pow2(1nat) == 2);
		assert(spec_pow2(2nat) == 4);
		assert(spec_cnode_level_bits(root_cap) == 2);
		assert(spec_cnode_level_bits(child_cap) == 2);
		assert(spec_resolve_guard_value(root_cap, cap_ptr, 4) == 0);
		assert(spec_resolve_guard_value(root_cap, guard_mismatch_cap_ptr, 4) == 1) by {
			assert(spec_extract_bits(8int, 3, 1) == 1) by (compute_only);
		}
		assert(spec_resolve_guard_matches(root_cap, cap_ptr, 4));
		assert(spec_resolve_guard_matches(child_cap, cap_ptr, 2));
		assert(!spec_resolve_guard_matches(root_cap, guard_mismatch_cap_ptr, 4));
		assert(spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, 4) == Some(2int));
		assert(state.cnode_slot_at(root_cnode, 1int) == Some(4int)) by {
			assert(state.cnode_lookup[root_cnode].dom().contains(1int));
			assert(state.cnode_lookup[root_cnode][1int] == 4int);
		}
		assert(spec_resolve_address_bits_next_slot(state, root_cap, shallow_cap_ptr, 4) == Some(4int)) by {
			assert(spec_extract_bits(4int, 2, 1) == 1) by (compute_only);
			assert(state.cnode_slot_at(root_cnode, 1int) == Some(4int));
		}
		assert(spec_resolve_address_bits_next_slot(state, child_cap, cap_ptr, 2) == Some(3int));
		assert(success_result.slot == Some(3int));
		assert(success_result.bits_remaining == 0);
		assert(spec_resolve_address_bits_success(state, child_cap, cap_ptr, 2, 3int, 0)) by {
			assert(state.has_slot(3int));
			assert(spec_resolve_address_bits_next_slot(state, child_cap, cap_ptr, 2) == Some(3int));
		}
		assert(spec_resolve_address_bits_success(state, root_cap, cap_ptr, 4, 3int, 0)) by {
			assert(state.has_slot(2int));
			assert(state.slot_cap(2int) == child_cap);
			assert(spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, 4) == Some(2int));
			assert(spec_resolve_address_bits_success(state, child_cap, cap_ptr, 2, 3int, 0));
		}
		assert(spec_resolve_address_bits_success(state, root_cap, shallow_cap_ptr, 4, 4int, 2)) by {
			assert(state.has_slot(4int));
			assert(state.slot_cap(4int) == null_cap);
			assert(spec_resolve_address_bits_next_slot(state, root_cap, shallow_cap_ptr, 4) == Some(4int));
		}
		assert(spec_resolve_address_bits_fault(state, child_cap, cap_ptr, 1, depth_mismatch_result)) by {
			assert(spec_resolve_guard_matches(child_cap, cap_ptr, 1));
			assert(spec_cnode_level_bits(child_cap) == 2);
		}
		assert(spec_resolve_address_bits_post(state, root_cap, cap_ptr, 4, success_result));
		assert(spec_resolve_address_bits_post(state, root_cap, shallow_cap_ptr, 4, shallow_success_result));
		assert(spec_resolve_address_bits_fault(state, leaf_cap, cap_ptr, 4, invalid_root_result));
		assert(spec_resolve_address_bits_fault(state, root_cap, guard_mismatch_cap_ptr, 4, guard_mismatch_result));
		assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, 3, depth_mismatch_result)) by {
			assert(state.has_slot(2int));
			assert(state.slot_cap(2int) == child_cap);
			assert(spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, 3) == Some(2int));
			assert(spec_resolve_address_bits_fault(state, child_cap, cap_ptr, 1, depth_mismatch_result));
		}
	}

pub proof fn cspace_ops_smoke_check() {
		cte_insert_smoke_check();
		cte_move_smoke_check();
		cte_swap_smoke_check();
		resolve_address_bits_smoke_check();
}

}
