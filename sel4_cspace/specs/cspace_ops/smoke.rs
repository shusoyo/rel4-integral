use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;
#[allow(unused_imports)]
use super::common::*;
#[allow(unused_imports)]
use super::insert::*;
#[allow(unused_imports)]
use super::r#move::*;
#[allow(unused_imports)]
use super::resolve::*;
#[allow(unused_imports)]
use super::swap::*;

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
	lemma_cte_insert_changed_slots_contains_src_dest(old_state, 2int, 3int);
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
	lemma_cte_move_changed_slots_contains_core(old_state, 3int, 5int);
	lemma_cte_move_changed_slots_contains_neighbors(old_state, 3int, 5int);
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
	lemma_swap_slot_ref_involution(Some(3int), 3int, 4int);
	lemma_cte_swap_changed_slots_contains_core(old_state, 3int, 4int);
	lemma_cte_swap_changed_slots_contains_neighbors(old_state, 3int, 4int);
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
	assert(state.cnode_lookup_wf());
	assert(spec_cnode_cap_lookup_total(state, root_cap)) by {
		assert(root_cap.cnode->Some_0.radix_bits == 1);
		assert(spec_pow2(1nat) == 2) by (compute_only);
		assert forall|offset: int|
			0 <= offset < spec_pow2(root_cap.cnode->Some_0.radix_bits as nat) ==> state.cnode_cap_slot_at(root_cap, offset) is Some by {
			if 0 <= offset < spec_pow2(root_cap.cnode->Some_0.radix_bits as nat) {
				assert(offset == 0 || offset == 1);
				if offset == 0 {
					assert(state.cnode_cap_slot_at(root_cap, offset) == Some(2int));
				} else {
					assert(state.cnode_cap_slot_at(root_cap, offset) == Some(4int));
				}
			}
		}
	}
	assert(spec_cnode_cap_lookup_total(state, child_cap)) by {
		assert(child_cap.cnode->Some_0.radix_bits == 1);
		assert(spec_pow2(1nat) == 2) by (compute_only);
		assert forall|offset: int|
			0 <= offset < spec_pow2(child_cap.cnode->Some_0.radix_bits as nat) ==> state.cnode_cap_slot_at(child_cap, offset) is Some by {
			if 0 <= offset < spec_pow2(child_cap.cnode->Some_0.radix_bits as nat) {
				assert(offset == 0 || offset == 1);
				if offset == 0 {
					assert(state.cnode_cap_slot_at(child_cap, offset) == Some(3int));
				} else {
					assert(state.cnode_cap_slot_at(child_cap, offset) == Some(5int));
				}
			}
		}
	}
	lemma_cnode_lookup_total_implies_slot_at_exists(state, root_cap, 0int);
	lemma_resolve_known_offset_implies_next_slot_exists(state, root_cap, 0int, 4, 0int);
	assert(spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, 4) == Some(2int));
	assert(state.cnode_slot_at(root_cnode, 1int) == Some(4int)) by {
		assert(state.cnode_lookup[root_cnode].dom().contains(1int));
		assert(state.cnode_lookup[root_cnode][1int] == 4int);
	}
	assert(spec_resolve_address_bits_next_slot(state, root_cap, shallow_cap_ptr, 4) == Some(4int)) by {
		assert(spec_extract_bits(4int, 2, 1) == 1) by (compute_only);
		assert(state.cnode_slot_at(root_cnode, 1int) == Some(4int));
	}
	assert(spec_resolve_guard_matches(root_cap, shallow_cap_ptr, 4)) by {
		assert(spec_extract_bits(4int, 3, 1) == 0) by (compute_only);
	}
	lemma_cnode_lookup_total_implies_slot_at_exists(state, root_cap, 1int);
	lemma_resolve_known_offset_implies_next_slot_exists(state, root_cap, 4int, 4, 1int);
	assert(spec_resolve_address_bits_next_slot(state, child_cap, cap_ptr, 2) == Some(3int));
	lemma_cnode_lookup_total_implies_slot_at_exists(state, child_cap, 0int);
	lemma_resolve_known_offset_implies_next_slot_exists(state, child_cap, 0int, 2, 0int);
	assert(success_result.slot == Some(3int));
	assert(success_result.bits_remaining == 0);
	lemma_resolve_address_bits_exact_success(state, child_cap, cap_ptr, 2, 3int);
	lemma_resolve_address_bits_recursive_success(state, root_cap, cap_ptr, 4, 2int, 3int, 0);
	lemma_resolve_address_bits_early_stop_success(state, root_cap, shallow_cap_ptr, 4, 4int);
	assert(spec_resolve_depth_mismatch_fault(child_cap, 1, depth_mismatch_result)) by {
		assert(spec_cnode_level_bits(child_cap) == 2);
	}
	assert(spec_resolve_guard_matches(child_cap, cap_ptr, 1));
	lemma_resolve_depth_mismatch_fault_implies_fault(state, child_cap, cap_ptr, 1, depth_mismatch_result);
	lemma_resolve_address_bits_success_result_implies_post(state, root_cap, cap_ptr, 4, 3int, 0);
	lemma_resolve_address_bits_success_result_implies_post(state, root_cap, shallow_cap_ptr, 4, 4int, 2);
	assert(spec_resolve_invalid_root_fault(leaf_cap, 4, invalid_root_result));
	lemma_resolve_invalid_root_fault_implies_fault(state, leaf_cap, cap_ptr, 4, invalid_root_result);
	assert(spec_resolve_guard_mismatch_fault(root_cap, guard_mismatch_cap_ptr, 4, guard_mismatch_result));
	lemma_resolve_guard_mismatch_fault_implies_fault(
		state,
		root_cap,
		guard_mismatch_cap_ptr,
		4,
		guard_mismatch_result,
	);
	lemma_resolve_address_bits_recursive_fault(state, root_cap, cap_ptr, 3, 2int, depth_mismatch_result);
	lemma_resolve_address_bits_fault_result_implies_post(state, leaf_cap, cap_ptr, 4, invalid_root_result);
	lemma_resolve_address_bits_fault_result_implies_post(state, root_cap, guard_mismatch_cap_ptr, 4, guard_mismatch_result);
	lemma_resolve_address_bits_fault_result_implies_post(state, root_cap, cap_ptr, 3, depth_mismatch_result);
}

pub proof fn cspace_ops_smoke_check() {
	cte_insert_smoke_check();
	cte_move_smoke_check();
	cte_swap_smoke_check();
	resolve_address_bits_smoke_check();
}

}
