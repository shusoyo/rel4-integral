use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::r#move::*;

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

pub proof fn lemma_swap_slot_ref_involution(
	ptr: Option<SlotId>,
	slot1: SlotId,
	slot2: SlotId,
)
	ensures
		spec_swap_slot_ref(spec_swap_slot_ref(ptr, slot1, slot2), slot1, slot2) == ptr,
{
	assert(spec_swap_slot_ref(spec_swap_slot_ref(ptr, slot1, slot2), slot1, slot2) == ptr);
}

pub proof fn lemma_cte_swap_changed_slots_contains_core(
	old_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
)
	requires
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
	ensures
		spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(slot1),
		spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(slot2),
{
	assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(slot1));
	assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(slot2));
}

pub proof fn lemma_cte_swap_changed_slots_contains_neighbors(
	old_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
)
	requires
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
	ensures
		old_state.slot_entry(slot1).mdb_prev is Some ==> spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot1).mdb_prev.unwrap()),
		old_state.slot_entry(slot1).mdb_next is Some ==> spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot1).mdb_next.unwrap()),
		old_state.slot_entry(slot2).mdb_prev is Some ==> spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot2).mdb_prev.unwrap()),
		old_state.slot_entry(slot2).mdb_next is Some ==> spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot2).mdb_next.unwrap()),
{
	if old_state.slot_entry(slot1).mdb_prev is Some {
		assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot1).mdb_prev.unwrap()));
	}
	if old_state.slot_entry(slot1).mdb_next is Some {
		assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot1).mdb_next.unwrap()));
	}
	if old_state.slot_entry(slot2).mdb_prev is Some {
		assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot2).mdb_prev.unwrap()));
	}
	if old_state.slot_entry(slot2).mdb_next is Some {
		assert(spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(old_state.slot_entry(slot2).mdb_next.unwrap()));
	}
}

pub proof fn lemma_cte_swap_post_preserves_untouched_slot(
	old_state: CSpaceState,
	new_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
	cap1: CapSpec,
	cap2: CapSpec,
	slot: SlotId,
)
	requires
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
		new_state.has_slot(slot1),
		new_state.has_slot(slot2),
		old_state.has_slot(slot),
		spec_cte_swap_post(old_state, new_state, slot1, slot2, cap1, cap2),
		!spec_cte_swap_changed_slots(old_state, slot1, slot2).contains(slot),
	ensures
		new_state.has_slot(slot),
		new_state.slot_entry(slot) == old_state.slot_entry(slot),
		new_state.slot_cap(slot) == old_state.slot_cap(slot),
{
	lemma_slots_unchanged_except_preserves_slot_data(
		old_state,
		new_state,
		spec_cte_swap_changed_slots(old_state, slot1, slot2),
		slot,
	);
}

pub proof fn lemma_cte_swap_pre_post_implies_contract(
	old_state: CSpaceState,
	new_state: CSpaceState,
	slot1: SlotId,
	slot2: SlotId,
	cap1: CapSpec,
	cap2: CapSpec,
)
	requires
		old_state.has_slot(slot1),
		old_state.has_slot(slot2),
		new_state.has_slot(slot1),
		new_state.has_slot(slot2),
		spec_cte_swap_pre(old_state, slot1, slot2, cap1, cap2),
		spec_cte_swap_post(old_state, new_state, slot1, slot2, cap1, cap2),
	ensures
		spec_cte_swap(old_state, new_state, slot1, slot2, cap1, cap2),
{
	assert(spec_cte_swap(old_state, new_state, slot1, slot2, cap1, cap2));
}

}
