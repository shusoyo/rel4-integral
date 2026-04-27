use vstd::prelude::*;

verus! {

pub type SlotId = int;

pub open spec fn cspace_word_bits() -> int {
	64
}

pub open spec fn cspace_endpoint_bits() -> int {
	4
}

pub open spec fn cspace_notification_bits() -> int {
	5
}

pub open spec fn cspace_slot_bits() -> int {
	5
}

pub open spec fn cspace_tcb_bits() -> int {
	10
}

pub open spec fn cspace_min_untyped_bits() -> int {
	4
}

pub ghost enum ObjectKind {
	Untyped,
	Endpoint,
	Notification,
	CNode,
	Thread,
	Reply,
	IRQ,
	Arch,
	Zombie,
	Opaque,
}

pub ghost enum CapKind {
	NullCap,
	UntypedCap,
	EndpointCap,
	NotificationCap,
	CNodeCap,
	ThreadCap,
	ReplyCap,
	IRQControlCap,
	IRQHandlerCap,
	ZombieCap,
	ArchCap,
}

#[verifier::ext_equal]
pub ghost struct ObjectRef {
	pub id: int,
	pub kind: ObjectKind,
}

#[verifier::ext_equal]
pub ghost struct Rights {
	pub can_read: bool,
	pub can_write: bool,
	pub can_grant: bool,
	pub can_grant_reply: bool,
}

#[verifier::ext_equal]
pub ghost struct CNodeCapDataSpec {
	pub radix_bits: int,
	pub guard: int,
	pub guard_size: int,
}

#[verifier::ext_equal]
pub ghost struct UntypedCapDataSpec {
	pub block_size_bits: int,
	pub free_index: int,
	pub is_device: bool,
}

#[verifier::ext_equal]
pub ghost struct CapSpec {
	pub kind: CapKind,
	pub object: Option<ObjectRef>,
	pub region_id: Option<int>,
	pub rights: Rights,
	pub badge: Option<int>,
	pub cnode: Option<CNodeCapDataSpec>,
	pub untyped: Option<UntypedCapDataSpec>,
}

#[verifier::ext_equal]
pub ghost struct SlotEntrySpec {
	pub cap: CapSpec,
	pub mdb_prev: Option<SlotId>,
	pub mdb_next: Option<SlotId>,
	pub mdb_revocable: bool,
	pub mdb_first_badged: bool,
}

#[verifier::ext_equal]
pub ghost struct CSpaceState {
	pub slots: Map<SlotId, SlotEntrySpec>,
	pub cnode_slots: Map<ObjectRef, Set<SlotId>>,
	pub cnode_lookup: Map<ObjectRef, Map<int, SlotId>>,
	pub roots: Set<SlotId>,
}

pub open spec fn cspace_spec_pow2(bits: nat) -> int
	decreases bits,
{
	if bits == 0 {
		1
	} else {
		2 * cspace_spec_pow2((bits - 1) as nat)
	}
}

pub open spec fn spec_is_physical_cap(cap: CapSpec) -> bool {
	match cap.kind {
		CapKind::NullCap
		| CapKind::IRQControlCap
		| CapKind::IRQHandlerCap
		| CapKind::ReplyCap => false,
		CapKind::ArchCap => spec_arch_is_physical_cap(cap),
		_ => true,
	}
}

pub open spec fn spec_arch_is_physical_cap(cap: CapSpec) -> bool {
	let _ = cap;
	false
}

pub open spec fn spec_same_object_ref(lhs: CapSpec, rhs: CapSpec) -> bool {
	lhs.object is Some
	&& rhs.object is Some
	&& lhs.object == rhs.object
}

pub open spec fn spec_cap_size_bits(cap: CapSpec) -> int {
	match cap.kind {
		CapKind::UntypedCap =>
			if cap.untyped is Some {
				cap.untyped.unwrap().block_size_bits
			} else {
				0
			},
		CapKind::EndpointCap => cspace_endpoint_bits(),
		CapKind::NotificationCap => cspace_notification_bits(),
		CapKind::CNodeCap =>
			if cap.cnode is Some {
				cap.cnode.unwrap().radix_bits + cspace_slot_bits()
			} else {
				0
			},
		CapKind::ThreadCap => cspace_tcb_bits(),
		CapKind::ZombieCap => 0,
		CapKind::ArchCap => 0,
		_ => 0,
	}
}

pub open spec fn spec_cap_range_top(cap: CapSpec) -> int {
	if cap.object is Some {
		let base = cap.object.unwrap().id;
		let bits = spec_cap_size_bits(cap);
		if 0 <= bits {
			base + cspace_spec_pow2(bits as nat) - 1
		} else {
			base - 1
		}
	} else {
		-1
	}
}

pub open spec fn spec_arch_same_region_as_caps(lhs: CapSpec, rhs: CapSpec) -> bool {
	let _ = lhs;
	let _ = rhs;
	false
}

pub open spec fn spec_arch_same_object_as_caps(lhs: CapSpec, rhs: CapSpec) -> bool {
	let _ = lhs;
	let _ = rhs;
	false
}

pub open spec fn spec_untyped_cap_contains_cap(lhs: CapSpec, rhs: CapSpec) -> bool {
	&&& lhs.kind == CapKind::UntypedCap
	&&& lhs.object is Some
	&&& lhs.untyped is Some
	&&& cspace_min_untyped_bits() <= lhs.untyped.unwrap().block_size_bits
	&&& spec_is_physical_cap(rhs)
	&&& rhs.object is Some
	&&& {
		let base = lhs.object.unwrap().id;
		let top = base + cspace_spec_pow2(lhs.untyped.unwrap().block_size_bits as nat) - 1;
		let rhs_base = rhs.object.unwrap().id;
		let rhs_top = spec_cap_range_top(rhs);
		&&& base <= rhs_base
		&&& rhs_base <= rhs_top
		&&& rhs_top <= top
	}
}

pub open spec fn spec_same_region_as_caps(lhs: CapSpec, rhs: CapSpec) -> bool {
	match lhs.kind {
		CapKind::UntypedCap => spec_untyped_cap_contains_cap(lhs, rhs),
		CapKind::EndpointCap => {
			lhs.kind == rhs.kind
			&& spec_same_object_ref(lhs, rhs)
		}
		CapKind::NotificationCap => {
			lhs.kind == rhs.kind
			&& spec_same_object_ref(lhs, rhs)
		}
		CapKind::CNodeCap => {
			&&& rhs.kind == CapKind::CNodeCap
			&&& spec_same_object_ref(lhs, rhs)
			&&& lhs.cnode is Some
			&&& rhs.cnode is Some
			&&& lhs.cnode.unwrap().radix_bits == rhs.cnode.unwrap().radix_bits
		}
		CapKind::ThreadCap => {
			lhs.kind == rhs.kind
			&& spec_same_object_ref(lhs, rhs)
		}
		CapKind::ReplyCap => {
			lhs.kind == rhs.kind
			&& spec_same_object_ref(lhs, rhs)
		}
		CapKind::IRQControlCap => {
			rhs.kind == CapKind::IRQControlCap
			|| rhs.kind == CapKind::IRQHandlerCap
		}
		CapKind::IRQHandlerCap => {
			rhs.kind == CapKind::IRQHandlerCap
			&& spec_same_object_ref(lhs, rhs)
		}
		CapKind::ArchCap => {
			rhs.kind == CapKind::ArchCap
			&& spec_arch_same_region_as_caps(lhs, rhs)
		}
		_ => false,
	}
}

pub open spec fn spec_same_object_as_caps(lhs: CapSpec, rhs: CapSpec) -> bool {
	if lhs.kind == CapKind::UntypedCap || lhs.kind == CapKind::IRQControlCap {
		false
	} else if lhs.kind == CapKind::ArchCap && rhs.kind == CapKind::ArchCap {
		spec_arch_same_object_as_caps(lhs, rhs)
	} else {
		spec_same_region_as_caps(lhs, rhs)
	}
}

pub open spec fn spec_is_cap_revocable(new_cap: CapSpec, src_cap: CapSpec) -> bool {
	match new_cap.kind {
		CapKind::EndpointCap => {
			src_cap.kind == CapKind::EndpointCap
			&& new_cap.badge != src_cap.badge
		}
		CapKind::NotificationCap => {
			src_cap.kind == CapKind::NotificationCap
			&& new_cap.badge != src_cap.badge
		}
		CapKind::IRQHandlerCap => src_cap.kind == CapKind::IRQControlCap,
		CapKind::UntypedCap => true,
		_ => false,
	}
}

pub open spec fn spec_is_arch_mdb_parent_of(
	parent_cap: CapSpec,
	child_cap: CapSpec,
	child_first_badged: bool,
) -> bool {
	let _ = child_first_badged;
	if parent_cap.kind == CapKind::ArchCap || child_cap.kind == CapKind::ArchCap {
		parent_cap.kind == CapKind::ArchCap && child_cap.kind == CapKind::ArchCap
	} else {
		true
	}
}

pub open spec fn spec_mdb_parent_badge_compatible_caps(
	parent_cap: CapSpec,
	child_cap: CapSpec,
	child_first_badged: bool,
) -> bool {
	if parent_cap.kind == CapKind::EndpointCap
		&& parent_cap.badge is Some
		&& parent_cap.badge.unwrap() != 0
	{
		&&& child_cap.kind == CapKind::EndpointCap
		&&& child_cap.badge == parent_cap.badge
		&&& !child_first_badged
	} else if parent_cap.kind == CapKind::NotificationCap
		&& parent_cap.badge is Some
		&& parent_cap.badge.unwrap() != 0
	{
		&&& child_cap.kind == CapKind::NotificationCap
		&&& child_cap.badge == parent_cap.badge
		&&& !child_first_badged
	} else {
		true
	}
}

pub open spec fn spec_mdb_parent_of_caps(
	parent_cap: CapSpec,
	parent_revocable: bool,
	child_cap: CapSpec,
	child_first_badged: bool,
) -> bool {
	&&& parent_revocable
	&&& spec_same_region_as_caps(parent_cap, child_cap)
	&&& spec_is_arch_mdb_parent_of(parent_cap, child_cap, child_first_badged)
	&&& spec_mdb_parent_badge_compatible_caps(parent_cap, child_cap, child_first_badged)
}

pub open spec fn rights_subseteq(lhs: Rights, rhs: Rights) -> bool {
	&&& lhs.can_read ==> rhs.can_read
	&&& lhs.can_write ==> rhs.can_write
	&&& lhs.can_grant ==> rhs.can_grant
	&&& lhs.can_grant_reply ==> rhs.can_grant_reply
}

pub open spec fn object_kind_matches_cap_kind(cap_kind: CapKind, obj_kind: ObjectKind) -> bool {
	match cap_kind {
		CapKind::UntypedCap => obj_kind == ObjectKind::Untyped,
		CapKind::EndpointCap => obj_kind == ObjectKind::Endpoint,
		CapKind::NotificationCap => obj_kind == ObjectKind::Notification,
		CapKind::CNodeCap => obj_kind == ObjectKind::CNode,
		CapKind::ThreadCap => obj_kind == ObjectKind::Thread,
		CapKind::ReplyCap => obj_kind == ObjectKind::Reply,
		CapKind::IRQHandlerCap => obj_kind == ObjectKind::IRQ,
		CapKind::ZombieCap => obj_kind == ObjectKind::Zombie,
		CapKind::ArchCap => obj_kind == ObjectKind::Arch,
		_ => obj_kind == ObjectKind::Opaque,
	}
}

pub open spec fn rights_compatible_with_kind(cap: CapSpec) -> bool {
	match cap.kind {
		CapKind::NullCap
		| CapKind::UntypedCap
		| CapKind::CNodeCap
		| CapKind::ThreadCap
		| CapKind::IRQControlCap
		| CapKind::IRQHandlerCap
		| CapKind::ZombieCap => {
			&&& !cap.rights.can_read
			&&& !cap.rights.can_write
			&&& !cap.rights.can_grant
			&&& !cap.rights.can_grant_reply
		}
		CapKind::NotificationCap => {
			&&& !cap.rights.can_grant
			&&& !cap.rights.can_grant_reply
		}
		CapKind::ArchCap | CapKind::EndpointCap | CapKind::ReplyCap => true,
	}
}

pub open spec fn valid_cap(cap: CapSpec) -> bool {
	&&& rights_compatible_with_kind(cap)
	&&& match cap.kind {
		CapKind::NullCap => {
			&&& cap.object is None
			&&& cap.region_id is None
			&&& cap.badge is None
			&&& cap.cnode is None
			&&& cap.untyped is None
		}
		CapKind::IRQControlCap => {
			&&& cap.object is None
			&&& cap.cnode is None
			&&& cap.untyped is None
		}
		CapKind::CNodeCap => {
			&&& cap.object is Some
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.cnode is Some
			&&& cap.untyped is None
			&&& 0 <= cap.cnode.unwrap().radix_bits
			&&& 0 <= cap.cnode.unwrap().guard_size
			&&& 0 < cap.cnode.unwrap().guard_size + cap.cnode.unwrap().radix_bits
			&&& cap.cnode.unwrap().guard_size + cap.cnode.unwrap().radix_bits <= cspace_word_bits()
			&&& cap.cnode.unwrap().radix_bits + cspace_slot_bits() < cspace_word_bits()
		}
		CapKind::UntypedCap => {
			&&& cap.object is Some
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.untyped is Some
			&&& cap.cnode is None
			&&& cspace_min_untyped_bits() <= cap.untyped.unwrap().block_size_bits
			&&& 0 <= cap.untyped.unwrap().block_size_bits
			&&& cap.untyped.unwrap().block_size_bits < cspace_word_bits()
			&&& 0 <= cap.untyped.unwrap().free_index <= cap.untyped.unwrap().block_size_bits
		}
		_ => {
			&&& cap.object is Some
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.cnode is None
			&&& cap.untyped is None
		}
	}
}

impl CSpaceState {
	pub open spec fn slot_dom(self) -> Set<SlotId> {
		self.slots.dom()
	}

	pub open spec fn has_slot(self, slot: SlotId) -> bool {
		self.slot_dom().contains(slot)
	}

	pub open spec fn slot_entry(self, slot: SlotId) -> SlotEntrySpec
		recommends
			self.has_slot(slot),
	{
		self.slots[slot]
	}

	pub open spec fn slot_cap(self, slot: SlotId) -> CapSpec
		recommends
			self.has_slot(slot),
	{
		self.slot_entry(slot).cap
	}

	pub open spec fn slot_empty(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		self.slot_cap(slot).kind == CapKind::NullCap
	}

	pub open spec fn same_object(self, left: SlotId, right: SlotId) -> bool
		recommends
			self.has_slot(left),
			self.has_slot(right),
	{
		self.slot_cap(left).object is Some
		&& self.slot_cap(right).object is Some
		&& self.slot_cap(left).object == self.slot_cap(right).object
	}

	pub open spec fn same_region(self, left: SlotId, right: SlotId) -> bool
		recommends
			self.has_slot(left),
			self.has_slot(right),
	{
		spec_same_region_as_caps(self.slot_cap(left), self.slot_cap(right))
	}

	pub open spec fn mdb_links(self, parent: SlotId, child: SlotId) -> bool
		recommends
			self.has_slot(parent),
			self.has_slot(child),
	{
		&&& self.slot_entry(parent).mdb_next == Some(child)
		&&& self.slot_entry(child).mdb_prev == Some(parent)
	}

	pub open spec fn immediate_derived(self, parent: SlotId, child: SlotId) -> bool
		recommends
			self.has_slot(parent),
			self.has_slot(child),
	{
		&&& self.mdb_links(parent, child)
		&&& self.slot_entry(child).mdb_revocable
		&&& self.same_region(parent, child)
		&&& rights_subseteq(self.slot_cap(child).rights, self.slot_cap(parent).rights)
	}

	pub open spec fn mdb_parent_badge_compatible(self, parent: SlotId, child: SlotId) -> bool
		recommends
			self.has_slot(parent),
			self.has_slot(child),
	{
		spec_mdb_parent_badge_compatible_caps(
			self.slot_cap(parent),
			self.slot_cap(child),
			self.slot_entry(child).mdb_first_badged,
		)
	}

	pub open spec fn mdb_parent_of(self, parent: SlotId, child: SlotId) -> bool
		recommends
			self.has_slot(parent),
			self.has_slot(child),
	{
		spec_mdb_parent_of_caps(
			self.slot_cap(parent),
			self.slot_entry(parent).mdb_revocable,
			self.slot_cap(child),
			self.slot_entry(child).mdb_first_badged,
		)
	}

	pub open spec fn same_object_as(self, left: SlotId, right: SlotId) -> bool
		recommends
			self.has_slot(left),
			self.has_slot(right),
	{
		spec_same_object_as_caps(self.slot_cap(left), self.slot_cap(right))
	}

	pub open spec fn is_final_cap(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		let prev_same_obj = if self.slot_entry(slot).mdb_prev is Some {
			self.same_object_as(self.slot_entry(slot).mdb_prev.unwrap(), slot)
		} else {
			false
		};

		let next_same_obj = if self.slot_entry(slot).mdb_next is Some {
			self.same_object_as(slot, self.slot_entry(slot).mdb_next.unwrap())
		} else {
			false
		};

		&&& !prev_same_obj
		&&& !next_same_obj
	}

	pub open spec fn slot_cap_long_running_delete(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		&&& self.slot_cap(slot).kind != CapKind::NullCap
		&&& self.is_final_cap(slot)
		&&& (
			self.slot_cap(slot).kind == CapKind::ThreadCap
			|| self.slot_cap(slot).kind == CapKind::ZombieCap
			|| self.slot_cap(slot).kind == CapKind::CNodeCap
		)
	}

	pub open spec fn ensure_no_children_blocks(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		self.slot_entry(slot).mdb_next is Some
		&& self.mdb_parent_of(slot, self.slot_entry(slot).mdb_next.unwrap())
	}

	pub open spec fn cnode_targets(self, slot: SlotId) -> Set<SlotId>
		recommends
			self.has_slot(slot),
		{
			if self.slot_cap(slot).kind == CapKind::CNodeCap
				&& self.slot_cap(slot).object is Some
				&& self.cnode_lookup.dom().contains(self.slot_cap(slot).object.unwrap())
			{
				let obj = self.slot_cap(slot).object.unwrap();
				Set::new(|dst: SlotId|
					exists|offset: int| #![auto]
						self.cnode_lookup[obj].dom().contains(offset)
						&& self.cnode_lookup[obj][offset] == dst)
			} else {
				Set::empty()
			}
	}

	pub open spec fn cspace_edge(self, src: SlotId, dst: SlotId) -> bool
		recommends
			self.has_slot(src),
			self.has_slot(dst),
	{
		self.cnode_targets(src).contains(dst)
	}

	pub open spec fn cnode_slot_at(self, obj: ObjectRef, offset: int) -> Option<SlotId> {
		if self.cnode_lookup.dom().contains(obj) && self.cnode_lookup[obj].dom().contains(offset) {
			Some(self.cnode_lookup[obj][offset])
		} else {
			None
		}
	}

	pub open spec fn cnode_cap_slot_at(self, cap: CapSpec, offset: int) -> Option<SlotId> {
		if cap.kind == CapKind::CNodeCap && cap.object is Some {
			self.cnode_slot_at(cap.object.unwrap(), offset)
		} else {
			None
		}
	}

	pub open spec fn reachable_slot_from(self, root: SlotId, target: SlotId, fuel: nat) -> bool
		recommends
			self.has_slot(root),
			self.has_slot(target),
		decreases fuel,
		{
			if fuel == 0 {
				root == target
			} else {
				root == target
				|| self.cspace_edge(root, target)
				|| exists|mid: SlotId| #![auto]
					self.has_slot(mid)
					&& self.cspace_edge(root, mid)
					&& self.reachable_slot_from(mid, target, (fuel - 1) as nat)
			}
		}

	pub open spec fn valid_slot_entry(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		let entry = self.slot_entry(slot);
		&&& valid_cap(entry.cap)
		&&& entry.mdb_prev is Some ==> self.has_slot(entry.mdb_prev.unwrap())
		&&& entry.mdb_next is Some ==> self.has_slot(entry.mdb_next.unwrap())
	}

	pub open spec fn valid_slots(self) -> bool {
		forall|slot: SlotId| #![auto] self.has_slot(slot) ==> self.valid_slot_entry(slot)
	}

	pub open spec fn mdb_cte_wf_at(self, slot: SlotId) -> bool {
		&&& self.has_slot(slot)
		&&& if self.has_slot(slot) {
			self.valid_slot_entry(slot)
		} else {
			false
		}
	}

	pub open spec fn is_final_cap_wf_at(self, slot: SlotId) -> bool {
		self.mdb_cte_wf_at(slot)
	}

	pub open spec fn ensure_no_children_wf_at(self, slot: SlotId) -> bool {
		self.mdb_cte_wf_at(slot)
	}

	pub open spec fn derive_cap_wf_at(self, slot: SlotId) -> bool {
		self.ensure_no_children_wf_at(slot)
	}

	pub open spec fn mdb_prev_next_consistent(self) -> bool {
		forall|slot: SlotId| #![auto]
			self.has_slot(slot) ==> {
				&&& self.slot_entry(slot).mdb_prev is Some ==>
					self.slot_entry(self.slot_entry(slot).mdb_prev.unwrap()).mdb_next == Some(slot)
				&&& self.slot_entry(slot).mdb_next is Some ==>
					self.slot_entry(self.slot_entry(slot).mdb_next.unwrap()).mdb_prev == Some(slot)
			}
	}

	pub open spec fn badge_derivation_wf(self) -> bool {
		forall|parent: SlotId, child: SlotId| #![auto]
			self.has_slot(parent) && self.has_slot(child) && self.immediate_derived(parent, child)
				==> spec_mdb_parent_badge_compatible_caps(
					self.slot_cap(parent),
					self.slot_cap(child),
					self.slot_entry(child).mdb_first_badged,
				)
	}

	pub open spec fn mdb_state_wf(self) -> bool {
		&&& self.valid_slots()
		&&& self.mdb_prev_next_consistent()
		&&& self.badge_derivation_wf()
	}

	pub open spec fn cnode_slots_wf(self) -> bool {
		&&& forall|obj: ObjectRef| #![auto]
			self.cnode_slots.dom().contains(obj) ==> {
				&&& obj.kind == ObjectKind::CNode
				&&& forall|slot: SlotId| #![auto]
					self.cnode_slots[obj].contains(slot) ==> self.has_slot(slot)
			}
		&&& forall|obj1: ObjectRef, obj2: ObjectRef, slot: SlotId| #![auto]
			self.cnode_slots.dom().contains(obj1)
			&& self.cnode_slots.dom().contains(obj2)
			&& self.cnode_slots[obj1].contains(slot)
			&& self.cnode_slots[obj2].contains(slot) ==> obj1 == obj2
	}

	pub open spec fn cnode_lookup_wf(self) -> bool {
		&&& self.cnode_slots.dom() =~= self.cnode_lookup.dom()
		&&& forall|obj: ObjectRef| #![auto]
			self.cnode_lookup.dom().contains(obj) ==> {
				&&& obj.kind == ObjectKind::CNode
				&&& forall|offset: int| #![auto]
					self.cnode_lookup[obj].dom().contains(offset) ==> {
						let slot = self.cnode_lookup[obj][offset];
						&&& self.has_slot(slot)
						&&& self.cnode_slots[obj].contains(slot)
					}
			}
	}

	pub open spec fn cspace_roots_wf(self) -> bool {
		forall|slot: SlotId| #![auto]
			self.roots.contains(slot) ==> {
				&&& self.has_slot(slot)
				&&& self.slot_cap(slot).kind == CapKind::CNodeCap
			}
	}

	pub open spec fn cspace_graph_wf(self) -> bool {
		forall|slot: SlotId| #![auto]
			self.has_slot(slot) && self.slot_cap(slot).kind == CapKind::CNodeCap ==> {
				&&& self.slot_cap(slot).object is Some
				&&& self.cnode_slots.dom().contains(self.slot_cap(slot).object.unwrap())
				&&& self.cnode_lookup.dom().contains(self.slot_cap(slot).object.unwrap())
			}
	}

	pub open spec fn cspace_lookup_wf(self) -> bool {
		&&& self.valid_slots()
		&&& self.cnode_slots_wf()
		&&& self.cnode_lookup_wf()
		&&& self.cspace_graph_wf()
	}

	pub open spec fn wf(self) -> bool {
		&&& self.mdb_state_wf()
		&&& self.cspace_lookup_wf()
		&&& self.cspace_roots_wf()
	}
}

/// Reusable Stage C entrypoint: unpack the `wf` bundle into the invariants later proofs need.
pub proof fn lemma_wf_implies_core_invariants(state: CSpaceState)
	requires
		state.wf(),
	ensures
		state.mdb_state_wf(),
		state.cspace_lookup_wf(),
		state.valid_slots(),
		state.mdb_prev_next_consistent(),
		state.badge_derivation_wf(),
		state.cnode_slots_wf(),
		state.cnode_lookup_wf(),
		state.cspace_roots_wf(),
		state.cspace_graph_wf(),
{
}

pub proof fn lemma_mdb_cte_wf_at_implies_valid_slot_entry(
	state: CSpaceState,
	slot: SlotId,
)
	requires
		state.mdb_cte_wf_at(slot),
	ensures
		state.has_slot(slot),
		state.valid_slot_entry(slot),
{
}

pub proof fn lemma_wf_implies_mdb_cte_wf_at(
	state: CSpaceState,
	slot: SlotId,
)
	requires
		state.wf(),
		state.has_slot(slot),
	ensures
		state.mdb_cte_wf_at(slot),
		state.is_final_cap_wf_at(slot),
		state.ensure_no_children_wf_at(slot),
		state.derive_cap_wf_at(slot),
{
	lemma_wf_implies_core_invariants(state);
	assert(state.valid_slots());
}

pub proof fn lemma_cspace_lookup_wf_implies_valid_slot_entry(
	state: CSpaceState,
	slot: SlotId,
)
	requires
		state.cspace_lookup_wf(),
		state.has_slot(slot),
	ensures
		state.valid_slot_entry(slot),
{
	assert(state.valid_slots());
}

/// Reusable Stage C helper for proving properties about a single slot under `wf`.
pub proof fn lemma_wf_implies_valid_slot_entry(
	state: CSpaceState,
	slot: SlotId,
)
	requires
		state.wf(),
		state.has_slot(slot),
	ensures
		state.valid_slot_entry(slot),
{
	lemma_wf_implies_mdb_cte_wf_at(state, slot);
	lemma_mdb_cte_wf_at_implies_valid_slot_entry(state, slot);
}

pub open spec fn slots_unchanged_except(
	old_state: CSpaceState,
	new_state: CSpaceState,
	changed: Set<SlotId>,
) -> bool {
	&&& old_state.slots.dom() =~= new_state.slots.dom()
	&&& forall|slot: SlotId| #![auto]
		old_state.slots.dom().contains(slot) && !changed.contains(slot) ==> new_state.slots[slot] == old_state.slots[slot]
}

pub proof fn lemma_slots_unchanged_except_preserves_slot_data(
	old_state: CSpaceState,
	new_state: CSpaceState,
	changed: Set<SlotId>,
	slot: SlotId,
)
	requires
		slots_unchanged_except(old_state, new_state, changed),
		old_state.has_slot(slot),
		!changed.contains(slot),
	ensures
		new_state.has_slot(slot),
		new_state.slot_entry(slot) == old_state.slot_entry(slot),
		new_state.slot_cap(slot) == old_state.slot_cap(slot),
		new_state.slot_empty(slot) == old_state.slot_empty(slot),
{
	assert(old_state.slots.dom().contains(slot));
	assert(new_state.slots.dom().contains(slot));
	assert(new_state.slots[slot] == old_state.slots[slot]);
}

pub proof fn abstract_cspace_smoke_check() {
	let no_rights = Rights {
		can_read: false,
		can_write: false,
		can_grant: false,
		can_grant_reply: false,
	};

	let endpoint_rights = Rights {
		can_read: true,
		can_write: true,
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

	let ep_parent_cap = CapSpec {
		kind: CapKind::EndpointCap,
		object: Some(endpoint_object),
		region_id: Some(1),
		rights: endpoint_rights,
		badge: Some(0),
		cnode: None,
		untyped: None,
	};

	let ep_child_cap = CapSpec {
		kind: CapKind::EndpointCap,
		object: Some(endpoint_object),
		region_id: Some(1),
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

	let cnode_same_region = CapSpec {
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

	let cnode_different_region = CapSpec {
		kind: CapKind::CNodeCap,
		object: Some(root_cnode),
		region_id: Some(0),
		rights: no_rights,
		badge: None,
		cnode: Some(CNodeCapDataSpec {
			radix_bits: 5,
			guard: 0,
			guard_size: 0,
		}),
		untyped: None,
	};

	let irq_control_cap = CapSpec {
		kind: CapKind::IRQControlCap,
		object: None,
		region_id: None,
		rights: no_rights,
		badge: None,
		cnode: None,
		untyped: None,
	};

	let irq_handler_cap = CapSpec {
		kind: CapKind::IRQHandlerCap,
		object: Some(ObjectRef {
			id: 7,
			kind: ObjectKind::IRQ,
		}),
		region_id: Some(7),
		rights: no_rights,
		badge: None,
		cnode: None,
		untyped: None,
	};

	let badged_endpoint_parent = CapSpec {
		kind: CapKind::EndpointCap,
		object: Some(endpoint_object),
		region_id: Some(1),
		rights: endpoint_rights,
		badge: Some(9),
		cnode: None,
		untyped: None,
	};

	let badged_endpoint_child = CapSpec {
		kind: CapKind::EndpointCap,
		object: Some(endpoint_object),
		region_id: Some(1),
		rights: endpoint_rights,
		badge: Some(9),
		cnode: None,
		untyped: None,
	};

	let rebadged_endpoint_child = CapSpec {
		kind: CapKind::EndpointCap,
		object: Some(endpoint_object),
		region_id: Some(1),
		rights: endpoint_rights,
		badge: Some(10),
		cnode: None,
		untyped: None,
	};

	let contained_cnode_cap = CapSpec {
		kind: CapKind::CNodeCap,
		object: Some(ObjectRef {
			id: 16,
			kind: ObjectKind::CNode,
		}),
		region_id: Some(16),
		rights: no_rights,
		badge: None,
		cnode: Some(CNodeCapDataSpec {
			radix_bits: 0,
			guard: 0,
			guard_size: 1,
		}),
		untyped: None,
	};

	let oversized_cnode_cap = CapSpec {
		kind: CapKind::CNodeCap,
		object: Some(ObjectRef {
			id: 48,
			kind: ObjectKind::CNode,
		}),
		region_id: Some(48),
		rights: no_rights,
		badge: None,
		cnode: Some(CNodeCapDataSpec {
			radix_bits: 5,
			guard: 0,
			guard_size: 0,
		}),
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
				cap: ep_parent_cap,
				mdb_prev: None,
				mdb_next: Some(3int),
				mdb_revocable: true,
				mdb_first_badged: false,
			},
			3int => SlotEntrySpec {
				cap: ep_child_cap,
				mdb_prev: Some(2int),
				mdb_next: None,
				mdb_revocable: true,
				mdb_first_badged: false,
			}
		],
		cnode_slots: map![
			root_cnode => set![2int, 3int]
		],
		cnode_lookup: map![
			root_cnode => map![
				0int => 2int,
				1int => 3int
			]
		],
		roots: set![1int],
	};

	assert(valid_cap(root_cap));
	assert(valid_cap(ep_parent_cap));
	assert(valid_cap(ep_child_cap));
	assert(valid_cap(cnode_same_region));
	assert(valid_cap(cnode_different_region));
	assert(valid_cap(irq_control_cap));
	assert(valid_cap(irq_handler_cap));
	assert(valid_cap(badged_endpoint_parent));
	assert(valid_cap(badged_endpoint_child));
	assert(valid_cap(rebadged_endpoint_child));
	assert(valid_cap(contained_cnode_cap));
	assert(valid_cap(oversized_cnode_cap));
	assert(spec_same_region_as_caps(ep_parent_cap, ep_child_cap));
	assert(spec_same_object_as_caps(ep_parent_cap, ep_child_cap));
	assert(spec_same_region_as_caps(cnode_same_region, root_cap));
	assert(!spec_same_region_as_caps(cnode_different_region, root_cap));
	assert(!spec_is_physical_cap(irq_handler_cap));
	assert(spec_same_region_as_caps(irq_control_cap, irq_handler_cap));
	assert(!spec_same_object_as_caps(irq_control_cap, irq_control_cap));
	assert(!spec_same_object_as_caps(irq_control_cap, irq_handler_cap));
	assert(spec_is_cap_revocable(irq_handler_cap, irq_control_cap));
	assert(!spec_mdb_parent_badge_compatible_caps(
		badged_endpoint_parent,
		badged_endpoint_child,
		true,
	));
	assert(spec_mdb_parent_badge_compatible_caps(
		badged_endpoint_parent,
		badged_endpoint_child,
		false,
	));
	assert(spec_is_cap_revocable(rebadged_endpoint_child, badged_endpoint_parent));
	assert(state.wf());
	assert(state.mdb_state_wf());
	assert(state.cspace_lookup_wf());
	assert(state.is_final_cap_wf_at(2int));
	assert(state.ensure_no_children_wf_at(2int));
	assert(state.cnode_cap_slot_at(root_cap, 0int) == Some(2int));
	assert(state.cnode_cap_slot_at(root_cap, 1int) == Some(3int));
	assert(state.cspace_edge(1int, 2int)) by {
		assert(state.cnode_lookup[root_cnode].dom().contains(0int));
		assert(state.cnode_lookup[root_cnode][0int] == 2int);
	}
	assert(state.cspace_edge(1int, 3int)) by {
		assert(state.cnode_lookup[root_cnode].dom().contains(1int));
		assert(state.cnode_lookup[root_cnode][1int] == 3int);
	}
	assert(state.reachable_slot_from(1int, 3int, 1));
	assert(state.immediate_derived(2int, 3int));
	assert(state.ensure_no_children_blocks(2int));
	assert(!state.is_final_cap(2int));
	assert(!state.is_final_cap(3int));
	assert(slots_unchanged_except(state, state, set![]));

	let untyped_object = ObjectRef {
		id: 10,
		kind: ObjectKind::Untyped,
	};

	let untyped_cap = CapSpec {
		kind: CapKind::UntypedCap,
		object: Some(untyped_object),
		region_id: Some(10),
		rights: Rights {
			can_read: false,
			can_write: false,
			can_grant: false,
			can_grant_reply: false,
		},
		badge: None,
		cnode: None,
		untyped: Some(UntypedCapDataSpec {
			block_size_bits: 6,
			free_index: 0,
			is_device: false,
		}),
	};

	let untyped_child_state = CSpaceState {
		slots: map![
			1int => SlotEntrySpec {
				cap: root_cap,
				mdb_prev: None,
				mdb_next: None,
				mdb_revocable: false,
				mdb_first_badged: false,
			},
			4int => SlotEntrySpec {
				cap: untyped_cap,
				mdb_prev: None,
				mdb_next: Some(5int),
				mdb_revocable: true,
				mdb_first_badged: false,
			},
			5int => SlotEntrySpec {
				cap: untyped_cap,
				mdb_prev: Some(4int),
				mdb_next: None,
				mdb_revocable: true,
				mdb_first_badged: false,
			}
		],
		cnode_slots: map![
			root_cnode => set![4int, 5int]
		],
		cnode_lookup: map![
			root_cnode => map![
				0int => 4int,
				1int => 5int
			]
		],
		roots: set![1int],
	};

	assert(valid_cap(untyped_cap));
	assert(spec_cap_size_bits(contained_cnode_cap) == 5);
	assert(cspace_spec_pow2(6nat) == 64) by (compute_only);
	assert(cspace_spec_pow2(5nat) == 32) by (compute_only);
	assert(spec_same_region_as_caps(untyped_cap, contained_cnode_cap)) by {
		assert(10 <= 16);
		assert(16 <= 16 + cspace_spec_pow2(5nat) - 1);
		assert(16 + cspace_spec_pow2(5nat) - 1 <= 10 + cspace_spec_pow2(6nat) - 1);
	};
	assert(spec_cap_size_bits(oversized_cnode_cap) == 10);
	assert(cspace_spec_pow2(10nat) == 1024) by (compute_only);
	assert(!spec_same_region_as_caps(untyped_cap, oversized_cnode_cap)) by {
		assert(48 <= 48 + cspace_spec_pow2(10nat) - 1);
		assert(!(48 + cspace_spec_pow2(10nat) - 1 <= 10 + cspace_spec_pow2(6nat) - 1));
	};
	assert(untyped_child_state.wf());
	assert(untyped_child_state.mdb_state_wf());
	assert(untyped_child_state.derive_cap_wf_at(4int));
	assert(untyped_child_state.same_object(4int, 5int));
	assert(!untyped_child_state.same_object_as(4int, 5int));
	assert(untyped_child_state.is_final_cap(4int));
	assert(!untyped_child_state.slot_cap_long_running_delete(4int));
}

}
