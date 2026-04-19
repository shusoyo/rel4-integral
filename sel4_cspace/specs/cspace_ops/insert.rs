use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::common::*;

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

pub proof fn lemma_cte_insert_changed_slots_contains_src_dest(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
	ensures
		spec_cte_insert_changed_slots(old_state, src, dest).contains(src),
		spec_cte_insert_changed_slots(old_state, src, dest).contains(dest),
{
	assert(spec_cte_insert_changed_slots(old_state, src, dest).contains(src));
	assert(spec_cte_insert_changed_slots(old_state, src, dest).contains(dest));
}

pub proof fn lemma_cte_insert_changed_slots_contains_old_next(
	old_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
		old_state.slot_entry(src).mdb_next is Some,
	ensures
		spec_cte_insert_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_next.unwrap()),
{
	assert(spec_cte_insert_changed_slots(old_state, src, dest).contains(old_state.slot_entry(src).mdb_next.unwrap()));
}

pub proof fn lemma_cte_insert_post_preserves_untouched_slot(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
	new_cap_is_revocable: bool,
	slot: SlotId,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
		old_state.has_slot(slot),
		spec_cte_insert_post(old_state, new_state, src, dest, new_cap, new_cap_is_revocable),
		!spec_cte_insert_changed_slots(old_state, src, dest).contains(slot),
	ensures
		new_state.has_slot(slot),
		new_state.slot_entry(slot) == old_state.slot_entry(slot),
		new_state.slot_cap(slot) == old_state.slot_cap(slot),
{
	lemma_slots_unchanged_except_preserves_slot_data(
		old_state,
		new_state,
		spec_cte_insert_changed_slots(old_state, src, dest),
		slot,
	);
}

pub proof fn lemma_cte_insert_pre_post_implies_contract(
	old_state: CSpaceState,
	new_state: CSpaceState,
	src: SlotId,
	dest: SlotId,
	new_cap: CapSpec,
	new_cap_is_revocable: bool,
)
	requires
		old_state.has_slot(src),
		old_state.has_slot(dest),
		new_state.has_slot(src),
		new_state.has_slot(dest),
		spec_cte_insert_pre(old_state, src, dest, new_cap),
		spec_cte_insert_post(old_state, new_state, src, dest, new_cap, new_cap_is_revocable),
	ensures
		spec_cte_insert(old_state, new_state, src, dest, new_cap, new_cap_is_revocable),
{
	assert(spec_cte_insert(old_state, new_state, src, dest, new_cap, new_cap_is_revocable));
}

}
