use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use super::super::abstract_cspace::*;

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

pub open spec fn spec_resolve_invalid_root_fault(
	root_cap: CapSpec,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		0 <= bits,
{
	&&& !(root_cap.kind == CapKind::CNodeCap
		&& root_cap.cnode is Some
		&& root_cap.object is Some)
	&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
	&&& result.slot is None
	&&& result.bits_remaining == bits
	&&& result.fault == Some(ResolveAddressBitsFaultSpec::InvalidRoot)
}

pub open spec fn spec_resolve_guard_mismatch_fault(
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
{
	let guard_bits = root_cap.cnode->Some_0.guard_size;
	&&& !spec_resolve_guard_matches(root_cap, cap_ptr, bits)
	&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
	&&& result.slot is None
	&&& result.bits_remaining == bits
	&&& result.fault == Some(ResolveAddressBitsFaultSpec::GuardMismatch {
		bits_left: bits,
		guard_found: root_cap.cnode->Some_0.guard,
		guard_size: guard_bits,
	})
}

pub open spec fn spec_resolve_depth_mismatch_fault(
	root_cap: CapSpec,
	bits: int,
	result: ResolveAddressBitsResultSpec,
) -> bool
	recommends
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= bits,
{
	let level_bits = spec_cnode_level_bits(root_cap);
	&&& level_bits > bits
	&&& result.status == ResolveAddressBitsStatusSpec::LookupFault
	&&& result.slot is None
	&&& result.bits_remaining == bits
	&&& result.fault == Some(ResolveAddressBitsFaultSpec::DepthMismatch {
		bits_left: bits,
		bits_found: level_bits,
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
		spec_resolve_invalid_root_fault(root_cap, bits, result)
	} else {
		let level_bits = spec_cnode_level_bits(root_cap);
		if !spec_resolve_guard_matches(root_cap, cap_ptr, bits) {
			spec_resolve_guard_mismatch_fault(root_cap, cap_ptr, bits, result)
		} else if !(level_bits <= bits) {
			spec_resolve_depth_mismatch_fault(root_cap, bits, result)
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

pub proof fn lemma_resolve_invalid_root_fault_implies_fault(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		spec_resolve_invalid_root_fault(root_cap, bits, result),
	ensures
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
{
	assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_guard_mismatch_fault_implies_fault(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		spec_resolve_guard_mismatch_fault(root_cap, cap_ptr, bits, result),
	ensures
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
{
	assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_depth_mismatch_fault_implies_fault(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		spec_resolve_guard_matches(root_cap, cap_ptr, bits),
		spec_resolve_depth_mismatch_fault(root_cap, bits, result),
	ensures
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
{
	assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_cspace_lookup_total_implies_cnode_lookup_total(
	state: CSpaceState,
	slot: SlotId,
)
	requires
		state.has_slot(slot),
		spec_cspace_lookup_total(state),
		state.slot_cap(slot).kind == CapKind::CNodeCap,
		state.slot_cap(slot).cnode is Some,
		state.slot_cap(slot).object is Some,
	ensures
		spec_cnode_cap_lookup_total(state, state.slot_cap(slot)),
{
	assert(spec_cnode_cap_lookup_total(state, state.slot_cap(slot)));
}

pub proof fn lemma_resolve_pre_implies_root_lookup_total(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
)
	requires
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		root_cap.kind == CapKind::CNodeCap,
	ensures
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_cap_lookup_total(state, root_cap),
{
}

pub proof fn lemma_cnode_slot_at_some_implies_has_slot(
	state: CSpaceState,
	obj: ObjectRef,
	offset: int,
	slot: SlotId,
)
	requires
		state.cnode_lookup_wf(),
		state.cnode_slot_at(obj, offset) == Some(slot),
	ensures
		state.has_slot(slot),
{
	assert(state.cnode_lookup.dom().contains(obj));
	assert(state.cnode_lookup[obj].dom().contains(offset));
	assert(state.cnode_lookup[obj][offset] == slot);
	assert(state.has_slot(slot));
}

pub proof fn lemma_cnode_lookup_total_implies_slot_at_exists(
	state: CSpaceState,
	cnode_cap: CapSpec,
	offset: int,
)
	requires
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		cnode_cap.object is Some,
		0 <= cnode_cap.cnode->Some_0.radix_bits,
		state.cnode_lookup_wf(),
		spec_cnode_cap_lookup_total(state, cnode_cap),
		0 <= offset < spec_pow2(cnode_cap.cnode->Some_0.radix_bits as nat),
	ensures
		state.cnode_cap_slot_at(cnode_cap, offset) is Some,
		state.cnode_slot_at(cnode_cap.object->Some_0, offset) is Some,
		state.has_slot(state.cnode_slot_at(cnode_cap.object->Some_0, offset).unwrap()),
{
	assert(state.cnode_cap_slot_at(cnode_cap, offset) is Some);
	assert(state.cnode_cap_slot_at(cnode_cap, offset) == state.cnode_slot_at(cnode_cap.object->Some_0, offset));
	assert(state.cnode_slot_at(cnode_cap.object->Some_0, offset) is Some);
	lemma_cnode_slot_at_some_implies_has_slot(
		state,
		cnode_cap.object->Some_0,
		offset,
		state.cnode_slot_at(cnode_cap.object->Some_0, offset).unwrap(),
	);
}

pub proof fn lemma_resolve_known_offset_implies_next_slot_exists(
	state: CSpaceState,
	cnode_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	offset: int,
)
	requires
		cnode_cap.kind == CapKind::CNodeCap,
		cnode_cap.cnode is Some,
		cnode_cap.object is Some,
		0 <= cnode_cap.cnode->Some_0.radix_bits,
		state.cnode_lookup_wf(),
		spec_cnode_cap_lookup_total(state, cnode_cap),
		0 <= cap_ptr,
		0 <= bits,
		spec_cnode_level_bits(cnode_cap) <= bits,
		offset == spec_extract_bits(cap_ptr, bits - spec_cnode_level_bits(cnode_cap), cnode_cap.cnode->Some_0.radix_bits),
		0 <= offset < spec_pow2(cnode_cap.cnode->Some_0.radix_bits as nat),
	ensures
		spec_resolve_address_bits_next_slot(state, cnode_cap, cap_ptr, bits) == state.cnode_slot_at(cnode_cap.object->Some_0, offset),
		spec_resolve_address_bits_next_slot(state, cnode_cap, cap_ptr, bits) is Some,
		state.has_slot(spec_resolve_address_bits_next_slot(state, cnode_cap, cap_ptr, bits).unwrap()),
{
	let next_slot = spec_resolve_address_bits_next_slot(state, cnode_cap, cap_ptr, bits);

	lemma_cnode_lookup_total_implies_slot_at_exists(state, cnode_cap, offset);
	assert(next_slot == state.cnode_slot_at(cnode_cap.object->Some_0, offset));
	assert(next_slot is Some);
	assert(state.cnode_slot_at(cnode_cap.object->Some_0, offset) == Some(next_slot.unwrap()));
	lemma_cnode_slot_at_some_implies_has_slot(
		state,
		cnode_cap.object->Some_0,
		offset,
		next_slot.unwrap(),
	);
}

pub proof fn lemma_resolve_address_bits_exact_success(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	slot: SlotId,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		state.has_slot(slot),
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_level_bits(root_cap) == bits,
		spec_resolve_guard_matches(root_cap, cap_ptr, bits),
		spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits) == Some(slot),
	ensures
		spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, 0),
{
	assert(spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, 0));
}

pub proof fn lemma_resolve_address_bits_early_stop_success(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	slot: SlotId,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		state.has_slot(slot),
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_level_bits(root_cap) < bits,
		spec_resolve_guard_matches(root_cap, cap_ptr, bits),
		spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits) == Some(slot),
		state.slot_cap(slot).kind != CapKind::CNodeCap,
	ensures
		spec_resolve_address_bits_success(
			state,
			root_cap,
			cap_ptr,
			bits,
			slot,
			bits - spec_cnode_level_bits(root_cap),
		),
{
	assert(spec_resolve_address_bits_success(
		state,
		root_cap,
		cap_ptr,
		bits,
		slot,
		bits - spec_cnode_level_bits(root_cap),
	));
}

pub proof fn lemma_resolve_address_bits_recursive_success(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	next: SlotId,
	slot: SlotId,
	bits_left: int,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		state.has_slot(next),
		state.has_slot(slot),
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_level_bits(root_cap) < bits,
		spec_resolve_guard_matches(root_cap, cap_ptr, bits),
		spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits) == Some(next),
		state.slot_cap(next).kind == CapKind::CNodeCap,
		spec_resolve_address_bits_success(
			state,
			state.slot_cap(next),
			cap_ptr,
			bits - spec_cnode_level_bits(root_cap),
			slot,
			bits_left,
		),
	ensures
		spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, bits_left),
{
	assert(spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, bits_left));
}

pub proof fn lemma_resolve_address_bits_recursive_fault(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	next: SlotId,
	result: ResolveAddressBitsResultSpec,
)
	requires
		root_cap.kind == CapKind::CNodeCap,
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 <= cap_ptr,
		0 <= bits,
		state.has_slot(next),
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_level_bits(root_cap) < bits,
		spec_resolve_guard_matches(root_cap, cap_ptr, bits),
		spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits) == Some(next),
		state.slot_cap(next).kind == CapKind::CNodeCap,
		spec_resolve_address_bits_fault(
			state,
			state.slot_cap(next),
			cap_ptr,
			bits - spec_cnode_level_bits(root_cap),
			result,
		),
	ensures
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
{
	assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_address_bits_success_result_implies_post(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	slot: SlotId,
	bits_left: int,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		0 <= bits_left <= bits,
		state.has_slot(slot),
		spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, bits_left),
	ensures
		spec_resolve_address_bits_post(
			state,
			root_cap,
			cap_ptr,
			bits,
			ResolveAddressBitsResultSpec {
				status: ResolveAddressBitsStatusSpec::Success,
				slot: Some(slot),
				bits_remaining: bits_left,
				fault: None,
			},
		),
{
	let result = ResolveAddressBitsResultSpec {
		status: ResolveAddressBitsStatusSpec::Success,
		slot: Some(slot),
		bits_remaining: bits_left,
		fault: None,
	};
	assert(spec_resolve_address_bits_post(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_address_bits_fault_result_implies_post(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		result.status == ResolveAddressBitsStatusSpec::LookupFault,
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
	ensures
		spec_resolve_address_bits_post(state, root_cap, cap_ptr, bits, result),
{
	assert(spec_resolve_address_bits_post(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_address_bits_success_result_implies_contract(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	slot: SlotId,
	bits_left: int,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		0 <= bits_left <= bits,
		state.has_slot(slot),
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, bits_left),
	ensures
		spec_resolve_address_bits(
			state,
			root_cap,
			cap_ptr,
			bits,
			ResolveAddressBitsResultSpec {
				status: ResolveAddressBitsStatusSpec::Success,
				slot: Some(slot),
				bits_remaining: bits_left,
				fault: None,
			},
		),
{
	let result = ResolveAddressBitsResultSpec {
		status: ResolveAddressBitsStatusSpec::Success,
		slot: Some(slot),
		bits_remaining: bits_left,
		fault: None,
	};
	lemma_resolve_address_bits_success_result_implies_post(
		state,
		root_cap,
		cap_ptr,
		bits,
		slot,
		bits_left,
	);
	assert(spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result));
}

pub proof fn lemma_resolve_address_bits_fault_result_implies_contract(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		result.status == ResolveAddressBitsStatusSpec::LookupFault,
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result),
	ensures
		spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result),
{
	lemma_resolve_address_bits_fault_result_implies_post(state, root_cap, cap_ptr, bits, result);
	assert(spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result));
}

}
