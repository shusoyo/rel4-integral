use vstd::prelude::*;

verus! {

// Phase A keeps low-level implementation details abstract and carries only
// the witness facts that later proofs are allowed to rely on.

// Contract model for convert_to_mut_type_ref.
pub open spec fn assume_convert_to_mut_type_ref_contract(
	addr: usize,
	addr_is_aligned: bool,
	points_to_live_object: bool,
	no_conflicting_mut_alias: bool,
	returned_ref_addr: usize,
) -> bool {
	let pre =
		addr != 0
		&& addr_is_aligned
		&& points_to_live_object
		&& no_conflicting_mut_alias;
	pre ==> returned_ref_addr == addr
}

// Contract model for convert_to_option_mut_type_ref.
pub open spec fn assume_convert_to_option_mut_type_ref_contract(
	addr: usize,
	addr_is_aligned_if_nonzero: bool,
	points_to_live_object_if_nonzero: bool,
	no_conflicting_mut_alias_if_nonzero: bool,
	has_ref: bool,
	returned_ref_addr: usize,
) -> bool {
	if addr == 0 {
		!has_ref
	} else {
		let pre =
			addr_is_aligned_if_nonzero
			&& points_to_live_object_if_nonzero
			&& no_conflicting_mut_alias_if_nonzero;
		pre ==> has_ref && returned_ref_addr == addr
	}
}

// Assumption model for maskVMRights: output rights may not escalate.
pub open spec fn assume_mask_vm_rights_non_escalation(
	in_can_read: bool,
	in_can_write: bool,
	req_read: bool,
	req_write: bool,
	out_can_read: bool,
	out_can_write: bool,
) -> bool {
	&&& out_can_write ==> out_can_read
	&&& out_can_read ==> in_can_read && req_read
	&&& out_can_write ==> in_can_write && req_write
}

// Assumption model for finalise_cap pairing contract.
pub open spec fn assume_finalise_cap_pairing(
	capability_matches_callsite: bool,
	final_flag_matches_callsite: bool,
	exposed_flag_matches_callsite: bool,
	remainder_matches_delete_flow: bool,
	cleanup_info_matches_delete_flow: bool,
	remainder_cleanup_paired: bool,
) -> bool {
	let pre =
		capability_matches_callsite
		&& final_flag_matches_callsite
		&& exposed_flag_matches_callsite;
	pre ==> (
		remainder_matches_delete_flow
		&& cleanup_info_matches_delete_flow
		&& remainder_cleanup_paired
	)
}

// Assumption model for post_cap_deletion origin contract.
pub open spec fn assume_post_cap_deletion_origin(
	cleanup_from_corresponding_finalise: bool,
	cleanup_info_origin_tracked: bool,
	deletion_side_effect_only: bool,
	no_extra_cap_mutation: bool,
) -> bool {
	let pre = cleanup_from_corresponding_finalise && cleanup_info_origin_tracked;
	pre ==> deletion_side_effect_only && no_extra_cap_mutation
}

// Assumption model for preemption_point progress contract.
pub open spec fn assume_preemption_point_progress(
	in_preemptible_loop: bool,
	caller_handles_non_none_status: bool,
	status_is_none: bool,
	status_is_recoverable_preempt: bool,
) -> bool {
	let pre = in_preemptible_loop && caller_handles_non_none_status;
	pre ==> (status_is_none || status_is_recoverable_preempt)
}

pub proof fn boundary_assumptions_smoke_check() {
	assert(assume_convert_to_mut_type_ref_contract(16, true, true, true, 16));
	assert(assume_convert_to_option_mut_type_ref_contract(0, false, false, false, false, 0));
	assert(assume_convert_to_option_mut_type_ref_contract(16, true, true, true, true, 16));
	assert(assume_mask_vm_rights_non_escalation(true, true, true, true, true, true));
	assert(assume_finalise_cap_pairing(true, true, true, true, true, true));
	assert(assume_post_cap_deletion_origin(true, true, true, true));
	assert(assume_preemption_point_progress(true, true, true, false));
}

}
