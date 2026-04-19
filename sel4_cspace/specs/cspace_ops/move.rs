use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::common::*;

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

pub proof fn lemma_cte_move_changed_slots_contains_core(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
	ensures
		spec_cte_move_changed_slots(old_state, src, dest).contains(src),
		spec_cte_move_changed_slots(old_state, src, dest).contains(dest),
{
	assert(spec_cte_move_changed_slots(old_state, src, dest).contains(src));
	assert(spec_cte_move_changed_slots(old_state, src, dest).contains(dest));
}

pub proof fn lemma_cte_move_changed_slots_contains_neighbors(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
	ensures
		old_state.slot_entry(src).mdb_prev is Some ==> spec_cte_move_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_prev.unwrap()),
		old_state.slot_entry(src).mdb_next is Some ==> spec_cte_move_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_next.unwrap()),
{
	if old_state.slot_entry(src).mdb_prev is Some {
		assert(spec_cte_move_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_prev.unwrap()));
	}
	if old_state.slot_entry(src).mdb_next is Some {
		assert(spec_cte_move_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_next.unwrap()));
	}
}

pub proof fn lemma_cte_move_post_preserves_untouched_slot(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
	slot: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
		old_state.has_slot(slot),
		spec_cte_move_post(old_state, new_state, src, dest, new_cap),
		!spec_cte_move_changed_slots(old_state, src, dest).contains(slot),
	ensures
		new_state.has_slot(slot),
		new_state.slot_entry(slot) == old_state.slot_entry(slot),
		new_state.slot_cap(slot) == old_state.slot_cap(slot),
{
	lemma_slots_unchanged_except_preserves_slot_data(
		old_state,
		new_state,
		spec_cte_move_changed_slots(old_state, src, dest),
		slot,
	);
}

pub proof fn lemma_cte_move_pre_post_implies_contract(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
		spec_cte_move_pre(old_state, src, dest, new_cap),
		spec_cte_move_post(old_state, new_state, src, dest, new_cap),
	ensures
		spec_cte_move(old_state, new_state, src, dest, new_cap),
{
	assert(spec_cte_move(old_state, new_state, src, dest, new_cap));
}

}
