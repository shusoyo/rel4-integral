use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;

pub open spec fn spec_is_mdb_parent_of_pre(
	state: CSpaceState,
	parent: SlotId,
	child: SlotId,
) -> bool {
	&&& state.mdb_cte_wf_at(parent)
	&&& state.has_slot(child)
}

pub open spec fn spec_is_mdb_parent_of_post(
	state: CSpaceState,
	parent: SlotId,
	child: SlotId,
	ret: bool,
) -> bool
	recommends
		state.has_slot(parent),
		state.has_slot(child),
{
	ret == state.mdb_parent_of(parent, child)
}

pub open spec fn spec_is_final_cap_pre(state: CSpaceState, slot: SlotId) -> bool {
	state.is_final_cap_wf_at(slot)
}

pub open spec fn spec_is_final_cap_post(
	state: CSpaceState,
	slot: SlotId,
	ret: bool,
) -> bool
	recommends
		state.has_slot(slot),
{
	ret == state.is_final_cap(slot)
}

pub open spec fn spec_is_long_running_delete_pre(state: CSpaceState, slot: SlotId) -> bool {
	state.is_final_cap_wf_at(slot)
}

pub open spec fn spec_is_long_running_delete_post(
	state: CSpaceState,
	slot: SlotId,
	ret: bool,
) -> bool
	recommends
		state.has_slot(slot),
{
	ret == state.slot_cap_long_running_delete(slot)
}

pub open spec fn spec_ensure_no_children_pre(state: CSpaceState, slot: SlotId) -> bool {
	state.ensure_no_children_wf_at(slot)
}

pub open spec fn spec_ensure_no_children_expected_error(
	state: CSpaceState,
	slot: SlotId,
) -> bool
	recommends
		state.has_slot(slot),
{
	state.ensure_no_children_blocks(slot)
}

}
