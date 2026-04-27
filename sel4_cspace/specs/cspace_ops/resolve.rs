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

#[verifier::ext_equal]
pub ghost struct ResolveAddressBitsRetCoreSpec {
	pub status: ResolveAddressBitsStatusSpec,
	pub slot: Option<SlotId>,
	pub bits_remaining: int,
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

pub proof fn lemma_spec_pow2_positive(bits: nat)
	ensures
		0 < spec_pow2(bits),
	decreases bits,
{
	if bits == 0 {
	} else {
		lemma_spec_pow2_positive((bits - 1) as nat);
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

pub proof fn lemma_extract_bits_range(
	value: int,
	start: int,
	width: int,
)
	requires
		0 <= value,
		0 <= start,
		0 <= width,
	ensures
		0 <= spec_extract_bits(value, start, width) < spec_pow2(width as nat),
{
	lemma_spec_pow2_positive(width as nat);
	vstd::arithmetic::div_mod::lemma_mod_bound(
		value / spec_pow2(start as nat),
		spec_pow2(width as nat),
	);
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
	forall|slot: SlotId| #![auto]
		state.has_slot(slot)
		&& state.slot_cap(slot).kind == CapKind::CNodeCap
		&& state.slot_cap(slot).cnode is Some
		&& state.slot_cap(slot).object is Some
		==> spec_cnode_cap_lookup_total(state, state.slot_cap(slot))
}

pub open spec fn spec_resolve_address_bits_state_wf(state: CSpaceState) -> bool {
	&&& state.cspace_lookup_wf()
	&&& spec_cspace_lookup_total(state)
}

pub open spec fn refines_resolve_address_bits_ret(
	concrete_view: ResolveAddressBitsRetCoreSpec,
	abstract_result: ResolveAddressBitsResultSpec,
) -> bool {
	&&& concrete_view.status == abstract_result.status
	&&& concrete_view.slot == abstract_result.slot
	&&& concrete_view.bits_remaining == abstract_result.bits_remaining
	&&& (concrete_view.status == ResolveAddressBitsStatusSpec::Success ==> abstract_result.fault is None)
	&&& (concrete_view.status == ResolveAddressBitsStatusSpec::LookupFault ==> abstract_result.fault is Some)
}

pub open spec fn project_resolve_address_bits_result_core(
	abstract_result: ResolveAddressBitsResultSpec,
) -> ResolveAddressBitsRetCoreSpec {
	ResolveAddressBitsRetCoreSpec {
		status: abstract_result.status,
		slot: abstract_result.slot,
		bits_remaining: abstract_result.bits_remaining,
	}
}

pub open spec fn resolve_address_bits_fault_core(
	bits_remaining: int,
) -> ResolveAddressBitsRetCoreSpec {
	ResolveAddressBitsRetCoreSpec {
		status: ResolveAddressBitsStatusSpec::LookupFault,
		slot: None,
		bits_remaining,
	}
}

pub open spec fn resolve_address_bits_success_core(
	slot: SlotId,
	bits_remaining: int,
) -> ResolveAddressBitsRetCoreSpec {
	ResolveAddressBitsRetCoreSpec {
		status: ResolveAddressBitsStatusSpec::Success,
		slot: Some(slot),
		bits_remaining,
	}
}

pub open spec fn resolve_address_bits_expected_core_from_cap(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
) -> ResolveAddressBitsRetCoreSpec
	decreases bits,
{
	if !(root_cap.kind == CapKind::CNodeCap
		&& root_cap.cnode is Some
		&& root_cap.object is Some) {
		resolve_address_bits_fault_core(bits)
	} else {
		let level_bits = spec_cnode_level_bits(root_cap);
		if !(0 <= cap_ptr
			&& 0 <= bits
			&& 0 <= root_cap.cnode->Some_0.radix_bits
			&& 0 <= root_cap.cnode->Some_0.guard_size
			&& 0 < level_bits) {
			resolve_address_bits_fault_core(bits)
		} else {
			let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
			if !spec_resolve_guard_matches(root_cap, cap_ptr, bits) {
				resolve_address_bits_fault_core(bits)
			} else if level_bits > bits {
				resolve_address_bits_fault_core(bits)
			} else if next_slot is Some {
				let next = next_slot.unwrap();
				if !state.has_slot(next) {
					resolve_address_bits_fault_core(bits)
				} else if bits == level_bits {
					resolve_address_bits_success_core(next, 0)
				} else {
					let remaining = bits - level_bits;
					let next_cap = state.slot_cap(next);
					if next_cap.kind == CapKind::CNodeCap {
						resolve_address_bits_expected_core_from_cap(state, next_cap, cap_ptr, remaining)
					} else {
						resolve_address_bits_success_core(next, remaining)
					}
				}
			} else {
				resolve_address_bits_fault_core(bits)
			}
		}
	}
}

pub open spec fn resolve_address_bits_core_refines_cap(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	concrete_view: ResolveAddressBitsRetCoreSpec,
) -> bool {
	exists|abstract_result: ResolveAddressBitsResultSpec| #![auto]
		spec_resolve_address_bits(
			state,
			root_cap,
			cap_ptr,
			bits,
			abstract_result,
		) && refines_resolve_address_bits_ret(concrete_view, abstract_result)
}

pub proof fn lemma_projected_resolve_address_bits_result_refines(
	abstract_result: ResolveAddressBitsResultSpec,
)
	requires
		abstract_result.status == ResolveAddressBitsStatusSpec::Success ==> abstract_result.fault is None,
		abstract_result.status == ResolveAddressBitsStatusSpec::LookupFault ==> abstract_result.fault is Some,
	ensures
		refines_resolve_address_bits_ret(
			project_resolve_address_bits_result_core(abstract_result),
			abstract_result,
		),
{
	assert(refines_resolve_address_bits_ret(
		project_resolve_address_bits_result_core(abstract_result),
		abstract_result,
	));
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
	&&& spec_resolve_address_bits_state_wf(state)
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

/// Reusable Stage C entrypoint: unpack `resolve_address_bits` preconditions into the
/// global invariants and lookup-totality facts needed by later proofs.
pub proof fn lemma_resolve_pre_implies_base_invariants(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
)
	requires
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
	ensures
		spec_resolve_address_bits_state_wf(state),
		state.cspace_lookup_wf(),
		state.valid_slots(),
		spec_cspace_lookup_total(state),
		state.cnode_lookup_wf(),
{
	assert(state.cspace_lookup_wf());
	assert(state.valid_slots());
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

/// Reusable Stage C helper: when the root is a `CNodeCap`, the resolve precondition already
/// packages every lookup-side fact needed to start a refinement proof.
pub proof fn lemma_resolve_pre_implies_root_lookup_ready(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
)
	requires
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		root_cap.kind == CapKind::CNodeCap,
	ensures
		state.cnode_lookup_wf(),
		root_cap.cnode is Some,
		root_cap.object is Some,
		0 < spec_cnode_level_bits(root_cap),
		spec_cnode_cap_lookup_total(state, root_cap),
{
	lemma_resolve_pre_implies_base_invariants(state, root_cap, cap_ptr, bits);
	lemma_resolve_pre_implies_root_lookup_total(state, root_cap, cap_ptr, bits);
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

pub proof fn lemma_resolve_address_bits_success_implies_bits_left_in_range(
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
		state.has_slot(slot),
		spec_resolve_address_bits_success(state, root_cap, cap_ptr, bits, slot, bits_left),
	ensures
		0 <= bits_left <= bits,
	decreases bits,
{
	if !(root_cap.kind == CapKind::CNodeCap
		&& root_cap.cnode is Some
		&& root_cap.object is Some) {
		assert(false);
	} else {
		let level_bits = spec_cnode_level_bits(root_cap);
		let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
		assert(0 < level_bits);
		assert(spec_resolve_guard_matches(root_cap, cap_ptr, bits));
		assert(level_bits <= bits);
		assert(next_slot is Some);
		let next = next_slot.unwrap();
		assert(state.has_slot(next));
		if bits == level_bits {
			assert(bits_left == 0);
		} else {
			let remaining = bits - level_bits;
			assert(0 <= remaining < bits);
			let next_cap = state.slot_cap(next);
			if next_cap.kind == CapKind::CNodeCap {
				lemma_resolve_address_bits_success_implies_bits_left_in_range(
					state,
					next_cap,
					cap_ptr,
					remaining,
					slot,
					bits_left,
				);
			} else {
				assert(bits_left == remaining);
			}
		}
	}
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

pub proof fn lemma_resolve_address_bits_expected_core_refines_cap(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
)
	requires
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		valid_cap(root_cap),
	ensures
		resolve_address_bits_core_refines_cap(
			state,
			root_cap,
			cap_ptr,
			bits,
			resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits),
		),
	decreases bits,
{
	let expected = resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits);
	if !(root_cap.kind == CapKind::CNodeCap
		&& root_cap.cnode is Some
		&& root_cap.object is Some) {
		let abstract_result = ResolveAddressBitsResultSpec {
			status: ResolveAddressBitsStatusSpec::LookupFault,
			slot: None,
			bits_remaining: bits,
			fault: Some(ResolveAddressBitsFaultSpec::InvalidRoot),
		};
		assert(expected == project_resolve_address_bits_result_core(abstract_result));
		lemma_projected_resolve_address_bits_result_refines(abstract_result);
		assert(spec_resolve_invalid_root_fault(root_cap, bits, abstract_result));
		lemma_resolve_invalid_root_fault_implies_fault(
			state,
			root_cap,
			cap_ptr,
			bits,
			abstract_result,
		);
		lemma_resolve_address_bits_fault_result_implies_contract(
			state,
			root_cap,
			cap_ptr,
			bits,
			abstract_result,
		);
		assert(resolve_address_bits_core_refines_cap(
			state,
			root_cap,
			cap_ptr,
			bits,
			expected,
		));
	} else {
		lemma_resolve_pre_implies_root_lookup_ready(state, root_cap, cap_ptr, bits);
		let level_bits = spec_cnode_level_bits(root_cap);
		if !spec_resolve_guard_matches(root_cap, cap_ptr, bits) {
			let abstract_result = ResolveAddressBitsResultSpec {
				status: ResolveAddressBitsStatusSpec::LookupFault,
				slot: None,
				bits_remaining: bits,
				fault: Some(ResolveAddressBitsFaultSpec::GuardMismatch {
					bits_left: bits,
					guard_found: root_cap.cnode.unwrap().guard,
					guard_size: root_cap.cnode.unwrap().guard_size,
				}),
			};
			assert(expected == project_resolve_address_bits_result_core(abstract_result));
			lemma_projected_resolve_address_bits_result_refines(abstract_result);
			assert(spec_resolve_guard_mismatch_fault(root_cap, cap_ptr, bits, abstract_result));
			lemma_resolve_guard_mismatch_fault_implies_fault(
				state,
				root_cap,
				cap_ptr,
				bits,
				abstract_result,
			);
			lemma_resolve_address_bits_fault_result_implies_contract(
				state,
				root_cap,
				cap_ptr,
				bits,
				abstract_result,
			);
			assert(resolve_address_bits_core_refines_cap(
				state,
				root_cap,
				cap_ptr,
				bits,
				expected,
			));
		} else if level_bits > bits {
			let abstract_result = ResolveAddressBitsResultSpec {
				status: ResolveAddressBitsStatusSpec::LookupFault,
				slot: None,
				bits_remaining: bits,
				fault: Some(ResolveAddressBitsFaultSpec::DepthMismatch {
					bits_left: bits,
					bits_found: level_bits,
				}),
			};
			assert(expected == project_resolve_address_bits_result_core(abstract_result));
			lemma_projected_resolve_address_bits_result_refines(abstract_result);
			assert(spec_resolve_depth_mismatch_fault(root_cap, bits, abstract_result));
			lemma_resolve_depth_mismatch_fault_implies_fault(
				state,
				root_cap,
				cap_ptr,
				bits,
				abstract_result,
			);
			lemma_resolve_address_bits_fault_result_implies_contract(
				state,
				root_cap,
				cap_ptr,
				bits,
				abstract_result,
			);
			assert(resolve_address_bits_core_refines_cap(
				state,
				root_cap,
				cap_ptr,
				bits,
				expected,
			));
		} else {
			let offset = spec_extract_bits(
				cap_ptr,
				bits - level_bits,
				root_cap.cnode->Some_0.radix_bits,
			);
			lemma_extract_bits_range(
				cap_ptr,
				bits - level_bits,
				root_cap.cnode->Some_0.radix_bits,
			);
			lemma_resolve_known_offset_implies_next_slot_exists(
				state,
				root_cap,
				cap_ptr,
				bits,
				offset,
			);
			let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
			assert(next_slot is Some);
			let next = next_slot.unwrap();
			assert(state.has_slot(next));
			if bits == level_bits {
				let abstract_result = ResolveAddressBitsResultSpec {
					status: ResolveAddressBitsStatusSpec::Success,
					slot: Some(next),
					bits_remaining: 0,
					fault: None,
				};
				assert(expected == project_resolve_address_bits_result_core(abstract_result));
				lemma_projected_resolve_address_bits_result_refines(abstract_result);
				lemma_resolve_address_bits_exact_success(
					state,
					root_cap,
					cap_ptr,
					bits,
					next,
				);
				lemma_resolve_address_bits_success_result_implies_contract(
					state,
					root_cap,
					cap_ptr,
					bits,
					next,
					0,
				);
				assert(resolve_address_bits_core_refines_cap(
					state,
					root_cap,
					cap_ptr,
					bits,
					expected,
				));
			} else {
				let remaining = bits - level_bits;
				let next_cap = state.slot_cap(next);
				if next_cap.kind == CapKind::CNodeCap {
					let child_core = resolve_address_bits_expected_core_from_cap(
						state,
						next_cap,
						cap_ptr,
						remaining,
					);
					lemma_resolve_pre_implies_base_invariants(state, root_cap, cap_ptr, bits);
					lemma_cspace_lookup_wf_implies_valid_slot_entry(state, next);
					assert(valid_cap(next_cap));
					assert(next_cap.cnode is Some);
					assert(next_cap.object is Some);
					assert(0 < spec_cnode_level_bits(next_cap));
					assert(0 <= remaining <= cspace_word_bits());
					lemma_cspace_lookup_total_implies_cnode_lookup_total(state, next);
					assert(spec_resolve_address_bits_pre(state, next_cap, cap_ptr, remaining));
					assert(expected == child_core);
					lemma_resolve_address_bits_expected_core_refines_cap(
						state,
						next_cap,
						cap_ptr,
						remaining,
					);
					let child_result = choose|child_result: ResolveAddressBitsResultSpec|
						spec_resolve_address_bits(
							state,
							next_cap,
							cap_ptr,
							remaining,
							child_result,
						) && refines_resolve_address_bits_ret(child_core, child_result);
					assert(spec_resolve_address_bits(
						state,
						next_cap,
						cap_ptr,
						remaining,
						child_result,
					));
					assert(refines_resolve_address_bits_ret(child_core, child_result));
					assert(child_result.status == child_core.status);
					assert(child_result.slot == child_core.slot);
					assert(child_result.bits_remaining == child_core.bits_remaining);
					if child_core.status == ResolveAddressBitsStatusSpec::Success {
						let slot = child_result.slot.unwrap();
						let bits_left = child_result.bits_remaining;
						assert(child_result.fault is None);
						assert(state.has_slot(slot));
						assert(spec_resolve_address_bits_success(
							state,
							next_cap,
							cap_ptr,
							remaining,
							slot,
							bits_left,
						));
						lemma_resolve_address_bits_recursive_success(
							state,
							root_cap,
							cap_ptr,
							bits,
							next,
							slot,
							bits_left,
						);
						lemma_resolve_address_bits_success_result_implies_contract(
							state,
							root_cap,
							cap_ptr,
							bits,
							slot,
							bits_left,
						);
						assert(child_result == ResolveAddressBitsResultSpec {
							status: ResolveAddressBitsStatusSpec::Success,
							slot: Some(slot),
							bits_remaining: bits_left,
							fault: None,
						});
						assert(spec_resolve_address_bits(state, root_cap, cap_ptr, bits, child_result));
					} else {
						assert(child_result.status == ResolveAddressBitsStatusSpec::LookupFault);
						assert(child_result.fault is Some);
						assert(spec_resolve_address_bits_fault(
							state,
							next_cap,
							cap_ptr,
							remaining,
							child_result,
						));
						lemma_resolve_address_bits_recursive_fault(
							state,
							root_cap,
							cap_ptr,
							bits,
							next,
							child_result,
						);
						lemma_resolve_address_bits_fault_result_implies_contract(
							state,
							root_cap,
							cap_ptr,
							bits,
							child_result,
						);
					}
					assert(resolve_address_bits_core_refines_cap(
						state,
						root_cap,
						cap_ptr,
						bits,
						expected,
					));
				} else {
					let abstract_result = ResolveAddressBitsResultSpec {
						status: ResolveAddressBitsStatusSpec::Success,
						slot: Some(next),
						bits_remaining: remaining,
						fault: None,
					};
					assert(expected == project_resolve_address_bits_result_core(abstract_result));
					lemma_projected_resolve_address_bits_result_refines(abstract_result);
					lemma_resolve_address_bits_early_stop_success(
						state,
						root_cap,
						cap_ptr,
						bits,
						next,
					);
					lemma_resolve_address_bits_success_result_implies_contract(
						state,
						root_cap,
						cap_ptr,
						bits,
						next,
						remaining,
					);
					assert(resolve_address_bits_core_refines_cap(
						state,
						root_cap,
						cap_ptr,
						bits,
						expected,
					));
				}
			}
		}
	}
}

pub proof fn lemma_resolve_address_bits_result_projects_to_expected_core_from_cap(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	result: ResolveAddressBitsResultSpec,
)
	requires
		0 <= cap_ptr,
		0 <= bits,
		valid_cap(root_cap),
		spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result),
	ensures
		project_resolve_address_bits_result_core(result)
			== resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits),
	decreases bits,
{
	let expected = resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits);
	assert(spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits));
	if result.status == ResolveAddressBitsStatusSpec::Success {
		assert(result.slot is Some);
		assert(result.fault is None);
		let slot = result.slot.unwrap();
		let bits_left = result.bits_remaining;
		assert(state.has_slot(slot));
		assert(spec_resolve_address_bits_success(
			state,
			root_cap,
			cap_ptr,
			bits,
			slot,
			bits_left,
		));
		if !(root_cap.kind == CapKind::CNodeCap
			&& root_cap.cnode is Some
			&& root_cap.object is Some) {
			assert(false);
		} else {
			let level_bits = spec_cnode_level_bits(root_cap);
			let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
			assert(0 <= root_cap.cnode->Some_0.radix_bits);
			assert(0 <= root_cap.cnode->Some_0.guard_size);
			assert(0 < level_bits);
			assert(spec_resolve_guard_matches(root_cap, cap_ptr, bits));
			assert(level_bits <= bits);
			assert(next_slot is Some);
			let next = next_slot.unwrap();
			assert(state.has_slot(next));
			if bits == level_bits {
				assert(slot == next);
				assert(bits_left == 0);
				assert(expected == resolve_address_bits_success_core(next, 0));
			} else {
				let remaining = bits - level_bits;
				let next_cap = state.slot_cap(next);
				if next_cap.kind == CapKind::CNodeCap {
					lemma_resolve_pre_implies_base_invariants(state, root_cap, cap_ptr, bits);
					lemma_cspace_lookup_wf_implies_valid_slot_entry(state, next);
					assert(valid_cap(next_cap));
					assert(next_cap.cnode is Some);
					assert(next_cap.object is Some);
					assert(0 < spec_cnode_level_bits(next_cap));
					assert(0 <= remaining <= cspace_word_bits());
					lemma_cspace_lookup_total_implies_cnode_lookup_total(state, next);
					lemma_resolve_address_bits_success_implies_bits_left_in_range(
						state,
						next_cap,
						cap_ptr,
						remaining,
						slot,
						bits_left,
					);
					assert(spec_resolve_address_bits_pre(state, next_cap, cap_ptr, remaining));
					lemma_resolve_address_bits_success_result_implies_contract(
						state,
						next_cap,
						cap_ptr,
						remaining,
						slot,
						bits_left,
					);
					assert(result == ResolveAddressBitsResultSpec {
						status: ResolveAddressBitsStatusSpec::Success,
						slot: Some(slot),
						bits_remaining: bits_left,
						fault: None,
					});
					assert(spec_resolve_address_bits(state, next_cap, cap_ptr, remaining, result));
					lemma_resolve_address_bits_result_projects_to_expected_core_from_cap(
						state,
						next_cap,
						cap_ptr,
						remaining,
						result,
					);
					assert(expected == resolve_address_bits_expected_core_from_cap(
						state,
						next_cap,
						cap_ptr,
						remaining,
					));
				} else {
					assert(slot == next);
					assert(bits_left == remaining);
					assert(expected == resolve_address_bits_success_core(next, remaining));
				}
			}
		}
	} else {
		assert(result.status == ResolveAddressBitsStatusSpec::LookupFault);
		assert(spec_resolve_address_bits_fault(state, root_cap, cap_ptr, bits, result));
		if !(root_cap.kind == CapKind::CNodeCap
			&& root_cap.cnode is Some
			&& root_cap.object is Some) {
			assert(expected == resolve_address_bits_fault_core(bits));
		} else {
			let level_bits = spec_cnode_level_bits(root_cap);
			let next_slot = spec_resolve_address_bits_next_slot(state, root_cap, cap_ptr, bits);
			assert(0 <= root_cap.cnode->Some_0.radix_bits);
			assert(0 <= root_cap.cnode->Some_0.guard_size);
			assert(0 < level_bits);
			if !spec_resolve_guard_matches(root_cap, cap_ptr, bits) {
				assert(expected == resolve_address_bits_fault_core(bits));
			} else if level_bits > bits {
				assert(expected == resolve_address_bits_fault_core(bits));
			} else {
				assert(next_slot is Some);
				let next = next_slot.unwrap();
				assert(state.has_slot(next));
				if bits == level_bits {
					assert(false);
				} else {
					let remaining = bits - level_bits;
					let next_cap = state.slot_cap(next);
					if next_cap.kind == CapKind::CNodeCap {
						lemma_resolve_pre_implies_base_invariants(state, root_cap, cap_ptr, bits);
						lemma_cspace_lookup_wf_implies_valid_slot_entry(state, next);
						assert(valid_cap(next_cap));
						assert(next_cap.cnode is Some);
						assert(next_cap.object is Some);
						assert(0 < spec_cnode_level_bits(next_cap));
						assert(0 <= remaining <= cspace_word_bits());
						lemma_cspace_lookup_total_implies_cnode_lookup_total(state, next);
						assert(spec_resolve_address_bits_pre(state, next_cap, cap_ptr, remaining));
						lemma_resolve_address_bits_fault_result_implies_contract(
							state,
							next_cap,
							cap_ptr,
							remaining,
							result,
						);
						lemma_resolve_address_bits_result_projects_to_expected_core_from_cap(
							state,
							next_cap,
							cap_ptr,
							remaining,
							result,
						);
						assert(expected == resolve_address_bits_expected_core_from_cap(
							state,
							next_cap,
							cap_ptr,
							remaining,
						));
					} else {
						assert(false);
					}
				}
			}
		}
	}
	assert(project_resolve_address_bits_result_core(result) == expected);
}

pub proof fn lemma_resolve_address_bits_core_refines_cap_implies_expected_core_from_cap(
	state: CSpaceState,
	root_cap: CapSpec,
	cap_ptr: int,
	bits: int,
	concrete_view: ResolveAddressBitsRetCoreSpec,
)
	requires
		valid_cap(root_cap),
		spec_resolve_address_bits_pre(state, root_cap, cap_ptr, bits),
		resolve_address_bits_core_refines_cap(state, root_cap, cap_ptr, bits, concrete_view),
	ensures
		concrete_view == resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits),
{
	let result = choose|result: ResolveAddressBitsResultSpec|
		spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result)
			&& refines_resolve_address_bits_ret(concrete_view, result);
	assert(spec_resolve_address_bits(state, root_cap, cap_ptr, bits, result));
	assert(refines_resolve_address_bits_ret(concrete_view, result));
	lemma_resolve_address_bits_result_projects_to_expected_core_from_cap(
		state,
		root_cap,
		cap_ptr,
		bits,
		result,
	);
	assert(concrete_view == project_resolve_address_bits_result_core(result));
	assert(concrete_view == resolve_address_bits_expected_core_from_cap(state, root_cap, cap_ptr, bits));
}

}
