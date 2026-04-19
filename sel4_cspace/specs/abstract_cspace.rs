use vstd::prelude::*;

verus! {

pub type SlotId = int;

pub closed spec fn cspace_word_bits() -> int {
	64
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
			&&& cap.object.is_None()
			&&& cap.region_id.is_None()
			&&& cap.badge.is_None()
			&&& cap.cnode.is_None()
			&&& cap.untyped.is_None()
		}
		CapKind::IRQControlCap => {
			&&& cap.object.is_None()
			&&& cap.cnode.is_None()
			&&& cap.untyped.is_None()
		}
		CapKind::CNodeCap => {
			&&& cap.object.is_Some()
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.cnode.is_Some()
			&&& cap.untyped.is_None()
			&&& 0 <= cap.cnode.unwrap().radix_bits
			&&& 0 <= cap.cnode.unwrap().guard_size
			&&& cap.cnode.unwrap().guard_size + cap.cnode.unwrap().radix_bits <= cspace_word_bits()
		}
		CapKind::UntypedCap => {
			&&& cap.object.is_Some()
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.untyped.is_Some()
			&&& cap.cnode.is_None()
			&&& 0 <= cap.untyped.unwrap().block_size_bits
			&&& 0 <= cap.untyped.unwrap().free_index <= cap.untyped.unwrap().block_size_bits
		}
		_ => {
			&&& cap.object.is_Some()
			&&& object_kind_matches_cap_kind(cap.kind, cap.object.unwrap().kind)
			&&& cap.cnode.is_None()
			&&& cap.untyped.is_None()
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
		self.slot_cap(left).object.is_Some()
		&& self.slot_cap(right).object.is_Some()
		&& self.slot_cap(left).object == self.slot_cap(right).object
	}

	pub open spec fn same_region(self, left: SlotId, right: SlotId) -> bool
		recommends
			self.has_slot(left),
			self.has_slot(right),
	{
		self.slot_cap(left).region_id.is_Some()
		&& self.slot_cap(right).region_id.is_Some()
		&& self.slot_cap(left).region_id == self.slot_cap(right).region_id
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

	pub open spec fn is_final_cap(self, slot: SlotId) -> bool
		recommends
			self.has_slot(slot),
	{
		let prev_same_obj = if self.slot_entry(slot).mdb_prev.is_Some() {
			self.same_object(self.slot_entry(slot).mdb_prev.unwrap(), slot)
		} else {
			false
		};

		let next_same_obj = if self.slot_entry(slot).mdb_next.is_Some() {
			self.same_object(slot, self.slot_entry(slot).mdb_next.unwrap())
		} else {
			false
		};

		&&& !prev_same_obj
		&&& !next_same_obj
	}

	pub open spec fn cnode_targets(self, slot: SlotId) -> Set<SlotId>
		recommends
			self.has_slot(slot),
	{
		if self.slot_cap(slot).kind == CapKind::CNodeCap
			&& self.slot_cap(slot).object.is_Some()
			&& self.cnode_slots.dom().contains(self.slot_cap(slot).object.unwrap())
		{
			self.cnode_slots[self.slot_cap(slot).object.unwrap()]
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
		if cap.kind == CapKind::CNodeCap && cap.object.is_Some() {
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
			|| exists|mid: SlotId|
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
		&&& entry.mdb_prev.is_Some() ==> self.has_slot(entry.mdb_prev.unwrap())
		&&& entry.mdb_next.is_Some() ==> self.has_slot(entry.mdb_next.unwrap())
	}

	pub open spec fn valid_slots(self) -> bool {
		forall|slot: SlotId| self.has_slot(slot) ==> self.valid_slot_entry(slot)
	}

	pub open spec fn mdb_prev_next_consistent(self) -> bool {
		forall|slot: SlotId|
			self.has_slot(slot) ==> {
				&&& self.slot_entry(slot).mdb_prev.is_Some() ==>
					self.slot_entry(self.slot_entry(slot).mdb_prev.unwrap()).mdb_next == Some(slot)
				&&& self.slot_entry(slot).mdb_next.is_Some() ==>
					self.slot_entry(self.slot_entry(slot).mdb_next.unwrap()).mdb_prev == Some(slot)
			}
	}

	pub open spec fn badge_derivation_wf(self) -> bool {
		forall|parent: SlotId, child: SlotId|
			self.has_slot(parent) && self.has_slot(child) && self.immediate_derived(parent, child) ==> {
				if self.slot_cap(parent).kind == CapKind::EndpointCap
					|| self.slot_cap(parent).kind == CapKind::NotificationCap {
					if self.slot_cap(parent).badge.is_Some() && self.slot_cap(parent).badge.unwrap() != 0 {
						&&& self.slot_cap(child).badge == self.slot_cap(parent).badge
						&&& !self.slot_entry(child).mdb_first_badged
					} else {
						true
					}
				} else {
					true
				}
			}
	}

	pub open spec fn cnode_slots_wf(self) -> bool {
		&&& forall|obj: ObjectRef|
			self.cnode_slots.dom().contains(obj) ==> {
				&&& obj.kind == ObjectKind::CNode
				&&& forall|slot: SlotId| self.cnode_slots[obj].contains(slot) ==> self.has_slot(slot)
			}
		&&& forall|obj1: ObjectRef, obj2: ObjectRef, slot: SlotId|
			self.cnode_slots.dom().contains(obj1)
			&& self.cnode_slots.dom().contains(obj2)
			&& self.cnode_slots[obj1].contains(slot)
			&& self.cnode_slots[obj2].contains(slot) ==> obj1 == obj2
	}

	pub open spec fn cnode_lookup_wf(self) -> bool {
		forall|obj: ObjectRef|
			self.cnode_lookup.dom().contains(obj) ==> {
				&&& obj.kind == ObjectKind::CNode
				&&& self.cnode_slots.dom().contains(obj)
				&&& forall|offset: int|
					self.cnode_lookup[obj].dom().contains(offset) ==> {
						let slot = self.cnode_lookup[obj][offset];
						&&& self.has_slot(slot)
						&&& self.cnode_slots[obj].contains(slot)
					}
			}
	}

	pub open spec fn cspace_roots_wf(self) -> bool {
		forall|slot: SlotId|
			self.roots.contains(slot) ==> {
				&&& self.has_slot(slot)
				&&& self.slot_cap(slot).kind == CapKind::CNodeCap
			}
	}

	pub open spec fn cspace_graph_wf(self) -> bool {
		forall|slot: SlotId|
			self.has_slot(slot) && self.slot_cap(slot).kind == CapKind::CNodeCap ==> {
				&&& self.slot_cap(slot).object.is_Some()
				&&& self.cnode_slots.dom().contains(self.slot_cap(slot).object.unwrap())
				&&& self.cnode_lookup.dom().contains(self.slot_cap(slot).object.unwrap())
			}
	}

	pub open spec fn wf(self) -> bool {
		&&& self.valid_slots()
		&&& self.mdb_prev_next_consistent()
		&&& self.badge_derivation_wf()
		&&& self.cnode_slots_wf()
		&&& self.cnode_lookup_wf()
		&&& self.cspace_roots_wf()
		&&& self.cspace_graph_wf()
	}
}

pub open spec fn slots_unchanged_except(
	old_state: CSpaceState,
	new_state: CSpaceState,
	changed: Set<SlotId>,
) -> bool {
	&&& old_state.slots.dom() =~= new_state.slots.dom()
	&&& forall|slot: SlotId|
		old_state.slots.dom().contains(slot) && !changed.contains(slot) ==> new_state.slots[slot] == old_state.slots[slot]
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
				mdb_revocable: false,
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
			root_cnode => set![1int, 2int, 3int]
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
	assert(state.wf());
	assert(state.cspace_edge(1int, 2int));
	assert(state.cspace_edge(1int, 3int));
	assert(state.cnode_cap_slot_at(root_cap, 0int) == Some(2int));
	assert(state.reachable_slot_from(1int, 3int, 1));
	assert(state.immediate_derived(2int, 3int));
	assert(!state.is_final_cap(2int));
	assert(!state.is_final_cap(3int));
	assert(slots_unchanged_except(state, state, set![]));
}

}
