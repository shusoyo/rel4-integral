#![allow(dead_code)]

use crate::cte::{cte_t, deriveCap_ret};
use crate::structures::resolveAddressBits_ret_t;
use sel4_common::structures::exception_t;
use sel4_common::structures_gen::{cap, cap_null_cap, cap_tag};
use sel4_common::utils::convert_to_type_ref;
use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use crate::specs::abstract_cspace::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::common::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::derive::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::insert::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::r#move::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::resolve::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::swap::*;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCap(cap);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCte(cte_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExResolveAddressBitsRet(resolveAddressBits_ret_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExException(exception_t);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDeriveCapRet(deriveCap_ret);

pub uninterp spec fn trusted_exception_is_none(status: exception_t) -> bool;

pub uninterp spec fn trusted_exception_is_syscall_error(status: exception_t) -> bool;

pub uninterp spec fn trusted_derive_cap_ret_is_none(ret: &deriveCap_ret) -> bool;

pub uninterp spec fn trusted_derive_cap_ret_is_syscall_error(ret: &deriveCap_ret) -> bool;

pub uninterp spec fn trusted_view_derive_cap_ret_capability(ret: &deriveCap_ret) -> CapSpec;

#[verifier::external_body]
pub fn trusted_make_derive_cap_ret(status: exception_t, capability: &cap) -> (ret: deriveCap_ret)
    ensures
        trusted_view_derive_cap_ret_capability(&ret) == trusted_view_cap(capability),
        trusted_derive_cap_ret_is_none(&ret) == trusted_exception_is_none(status),
        trusted_derive_cap_ret_is_syscall_error(&ret) == trusted_exception_is_syscall_error(status),
{
    deriveCap_ret {
        status,
        capability: capability.clone(),
    }
}

#[verifier::external_body]
pub fn trusted_make_exception_none() -> (ret: exception_t)
    ensures
        trusted_exception_is_none(ret),
        !trusted_exception_is_syscall_error(ret),
{
    exception_t::EXCEPTION_NONE
}

#[verifier::external_body]
pub fn trusted_make_exception_syscall_error() -> (ret: exception_t)
    ensures
        trusted_exception_is_syscall_error(ret),
        !trusted_exception_is_none(ret),
{
    exception_t::EXCEPTION_SYSCALL_ERROR
}

#[verifier::external_body]
pub fn trusted_check_exception_is_none(status: exception_t) -> (ret: bool)
    ensures
        ret == trusted_exception_is_none(status),
{
    status == exception_t::EXCEPTION_NONE
}

#[verifier::external_body]
pub fn trusted_check_exception_is_syscall_error(status: exception_t) -> (ret: bool)
    ensures
        ret == trusted_exception_is_syscall_error(status),
{
    status == exception_t::EXCEPTION_SYSCALL_ERROR
}

#[verifier::external_body]
pub fn trusted_make_null_cap() -> (ret: cap)
    ensures
        trusted_view_cap(&ret) == spec_null_cap(),
{
    cap_null_cap::new().unsplay()
}

#[verifier::external_body]
pub fn trusted_clone_cap(raw: &cap) -> (ret: cap)
    ensures
        trusted_view_cap(&ret) == trusted_view_cap(raw),
{
    raw.clone()
}

#[verifier::external_body]
pub fn trusted_cap_is_zombie(raw: &cap) -> (ret: bool)
    ensures
        ret == (trusted_view_cap(raw).kind == CapKind::ZombieCap),
{
    raw.get_tag() == cap_tag::cap_zombie_cap
}

#[verifier::external_body]
pub fn trusted_cap_is_untyped(raw: &cap) -> (ret: bool)
    ensures
        ret == (trusted_view_cap(raw).kind == CapKind::UntypedCap),
{
    raw.get_tag() == cap_tag::cap_untyped_cap
}

#[verifier::external_body]
pub fn trusted_cap_is_reply(raw: &cap) -> (ret: bool)
    ensures
        ret == (trusted_view_cap(raw).kind == CapKind::ReplyCap),
{
    raw.get_tag() == cap_tag::cap_reply_cap
}

#[verifier::external_body]
pub fn trusted_cap_is_irq_control(raw: &cap) -> (ret: bool)
    ensures
        ret == (trusted_view_cap(raw).kind == CapKind::IRQControlCap),
{
    raw.get_tag() == cap_tag::cap_irq_control_cap
}

#[verifier::external_body]
pub fn trusted_slot_cap_is_null(raw_slot: &cte_t) -> (ret: bool)
    ensures
        ret == (trusted_view_cte(raw_slot).cap.kind == CapKind::NullCap),
{
    raw_slot.capability.get_tag() == cap_tag::cap_null_cap
}

#[verifier::external_body]
pub fn trusted_slot_cap_is_thread(raw_slot: &cte_t) -> (ret: bool)
    ensures
        ret == (trusted_view_cte(raw_slot).cap.kind == CapKind::ThreadCap),
{
    raw_slot.capability.get_tag() == cap_tag::cap_thread_cap
}

#[verifier::external_body]
pub fn trusted_slot_cap_is_zombie(raw_slot: &cte_t) -> (ret: bool)
    ensures
        ret == (trusted_view_cte(raw_slot).cap.kind == CapKind::ZombieCap),
{
    raw_slot.capability.get_tag() == cap_tag::cap_zombie_cap
}

#[verifier::external_body]
pub fn trusted_slot_cap_is_cnode(raw_slot: &cte_t) -> (ret: bool)
    ensures
        ret == (trusted_view_cte(raw_slot).cap.kind == CapKind::CNodeCap),
{
    raw_slot.capability.get_tag() == cap_tag::cap_cnode_cap
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct CapSnapshot {
    pub tag: u64,
    pub object_addr: usize,
    pub object_present: bool,
    pub can_read: bool,
    pub can_write: bool,
    pub can_grant: bool,
    pub can_grant_reply: bool,
    pub badge: u64,
    pub badge_present: bool,
    pub cnode_guard: u64,
    pub cnode_guard_size: u64,
    pub cnode_radix: u64,
    pub cnode_present: bool,
    pub untyped_block_size: u64,
    pub untyped_free_index: u64,
    pub untyped_is_device: bool,
    pub untyped_present: bool,
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct CteSnapshot {
    pub cap: CapSnapshot,
    pub mdb_prev_addr: usize,
    pub mdb_next_addr: usize,
    pub mdb_revocable: bool,
    pub mdb_first_badged: bool,
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct ResolveAddressBitsRetSnapshot {
    pub status_is_success: bool,
    pub status_is_lookup_fault: bool,
    pub slot_addr: usize,
    pub slot_present: bool,
    pub bits_remaining: usize,
}

#[verifier::ext_equal]
pub struct ResolveAddressBitsRetCoreSpec {
    pub status: ResolveAddressBitsStatusSpec,
    pub slot: Option<SlotId>,
    pub bits_remaining: int,
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct CapBridge {
    pub snapshot: CapSnapshot,
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct CteBridge {
    pub snapshot: CteSnapshot,
}

#[verifier::ext_equal]
#[derive(Copy, Clone)]
pub struct ResolveAddressBitsRetBridge {
    pub snapshot: ResolveAddressBitsRetSnapshot,
}

pub type ConcreteHeapId = int;

pub open spec fn spec_zero_rights() -> Rights {
    Rights {
        can_read: false,
        can_write: false,
        can_grant: false,
        can_grant_reply: false,
    }
}

pub open spec fn spec_slot_id_from_addr(addr: usize) -> SlotId {
    addr as int
}

pub open spec fn spec_option_slot_id_from_addr(addr: usize) -> Option<SlotId> {
    if addr == 0 {
        None
    } else {
        Some(spec_slot_id_from_addr(addr))
    }
}

pub open spec fn spec_cap_kind_from_tag(tag: u64) -> CapKind {
    if tag == 0 {
        CapKind::NullCap
    } else if tag == 2 {
        CapKind::UntypedCap
    } else if tag == 4 {
        CapKind::EndpointCap
    } else if tag == 6 {
        CapKind::NotificationCap
    } else if tag == 10 {
        CapKind::CNodeCap
    } else if tag == 12 {
        CapKind::ThreadCap
    } else if tag == 8 {
        CapKind::ReplyCap
    } else if tag == 14
        || tag == 11
        || tag == 20
    {
        CapKind::IRQControlCap
    } else if tag == 16 {
        CapKind::IRQHandlerCap
    } else if tag == 18 {
        CapKind::ZombieCap
    } else if tag == 1
        || tag == 3
        || tag == 13
    {
        CapKind::ArchCap
    } else {
        CapKind::IRQControlCap
    }
}

pub open spec fn spec_object_kind_from_cap_kind(kind: CapKind) -> ObjectKind {
    match kind {
        CapKind::UntypedCap => ObjectKind::Untyped,
        CapKind::EndpointCap => ObjectKind::Endpoint,
        CapKind::NotificationCap => ObjectKind::Notification,
        CapKind::CNodeCap => ObjectKind::CNode,
        CapKind::ThreadCap => ObjectKind::Thread,
        CapKind::ReplyCap => ObjectKind::Reply,
        CapKind::IRQHandlerCap => ObjectKind::IRQ,
        CapKind::ZombieCap => ObjectKind::Zombie,
        CapKind::ArchCap => ObjectKind::Arch,
        _ => ObjectKind::Opaque,
    }
}

pub open spec fn spec_cap_has_object(kind: CapKind) -> bool {
    match kind {
        CapKind::NullCap | CapKind::IRQControlCap => false,
        _ => true,
    }
}

pub open spec fn spec_cap_badge_enabled(kind: CapKind) -> bool {
    kind == CapKind::EndpointCap || kind == CapKind::NotificationCap
}

pub open spec fn spec_cap_rights(snapshot: CapSnapshot) -> Rights {
    Rights {
        can_read: snapshot.can_read,
        can_write: snapshot.can_write,
        can_grant: snapshot.can_grant,
        can_grant_reply: snapshot.can_grant_reply,
    }
}

pub open spec fn spec_cap_object(snapshot: CapSnapshot, kind: CapKind) -> Option<ObjectRef> {
    if spec_cap_has_object(kind) && snapshot.object_present {
        Some(ObjectRef {
            id: snapshot.object_addr as int,
            kind: spec_object_kind_from_cap_kind(kind),
        })
    } else {
        None
    }
}

pub open spec fn spec_cap_region_id(snapshot: CapSnapshot, kind: CapKind) -> Option<int> {
    if spec_cap_has_object(kind) && snapshot.object_present {
        Some(snapshot.object_addr as int)
    } else {
        None
    }
}

pub open spec fn view_cap(snapshot: CapSnapshot) -> CapSpec {
    let kind = spec_cap_kind_from_tag(snapshot.tag);
    CapSpec {
        kind,
        object: spec_cap_object(snapshot, kind),
        region_id: spec_cap_region_id(snapshot, kind),
        rights: spec_cap_rights(snapshot),
        badge: if spec_cap_badge_enabled(kind) && snapshot.badge_present {
            Some(snapshot.badge as int)
        } else {
            None
        },
        cnode: if kind == CapKind::CNodeCap && snapshot.cnode_present {
            Some(CNodeCapDataSpec {
                radix_bits: snapshot.cnode_radix as int,
                guard: snapshot.cnode_guard as int,
                guard_size: snapshot.cnode_guard_size as int,
            })
        } else {
            None
        },
        untyped: if kind == CapKind::UntypedCap && snapshot.untyped_present {
            Some(UntypedCapDataSpec {
                block_size_bits: snapshot.untyped_block_size as int,
                free_index: snapshot.untyped_free_index as int,
                is_device: snapshot.untyped_is_device,
            })
        } else {
            None
        },
    }
}

pub open spec fn view_cte(snapshot: CteSnapshot) -> SlotEntrySpec {
    SlotEntrySpec {
        cap: view_cap(snapshot.cap),
        mdb_prev: spec_option_slot_id_from_addr(snapshot.mdb_prev_addr),
        mdb_next: spec_option_slot_id_from_addr(snapshot.mdb_next_addr),
        mdb_revocable: snapshot.mdb_revocable,
        mdb_first_badged: snapshot.mdb_first_badged,
    }
}

pub open spec fn view_resolve_address_bits_ret(
    snapshot: ResolveAddressBitsRetSnapshot,
) -> ResolveAddressBitsRetCoreSpec {
    ResolveAddressBitsRetCoreSpec {
        status: if snapshot.status_is_success {
            ResolveAddressBitsStatusSpec::Success
        } else {
            ResolveAddressBitsStatusSpec::LookupFault
        },
        slot: if snapshot.slot_present {
            Some(spec_slot_id_from_addr(snapshot.slot_addr))
        } else {
            None
        },
        bits_remaining: snapshot.bits_remaining as int,
    }
}

pub open spec fn cap_snapshot_wf(snapshot: CapSnapshot) -> bool {
    valid_cap(view_cap(snapshot))
}

pub open spec fn cte_snapshot_wf(snapshot: CteSnapshot) -> bool {
    valid_cap(view_cte(snapshot).cap)
}

pub open spec fn resolve_address_bits_ret_snapshot_wf(
    snapshot: ResolveAddressBitsRetSnapshot,
) -> bool {
    &&& snapshot.status_is_success != snapshot.status_is_lookup_fault
    &&& 0 <= snapshot.bits_remaining as int
    &&& (snapshot.status_is_success ==> snapshot.slot_present)
    &&& (snapshot.status_is_lookup_fault ==> !snapshot.slot_present)
}

pub uninterp spec fn trusted_view_cap(raw: &cap) -> CapSpec;

pub uninterp spec fn trusted_view_cte(slot: &cte_t) -> SlotEntrySpec;

pub uninterp spec fn trusted_view_resolve_address_bits_ret(
    raw: &resolveAddressBits_ret_t,
) -> ResolveAddressBitsRetCoreSpec;

#[verifier::external_body]
pub fn trusted_extract_cap(raw: &cap) -> (out: CapSnapshot)
    ensures
        cap_snapshot_wf(out),
        view_cap(out) == trusted_view_cap(raw),
{
    let tag = raw.get_tag();
    let mut snapshot = CapSnapshot {
        tag,
        object_addr: 0,
        object_present: false,
        can_read: false,
        can_write: false,
        can_grant: false,
        can_grant_reply: false,
        badge: 0,
        badge_present: false,
        cnode_guard: 0,
        cnode_guard_size: 0,
        cnode_radix: 0,
        cnode_present: false,
        untyped_block_size: 0,
        untyped_free_index: 0,
        untyped_is_device: false,
        untyped_present: false,
    };

    if tag == 2 {
        let c = cap::cap_untyped_cap(raw);
        snapshot.object_addr = c.get_capPtr() as usize;
        snapshot.object_present = true;
        snapshot.untyped_block_size = c.get_capBlockSize();
        snapshot.untyped_free_index = c.get_capFreeIndex();
        snapshot.untyped_is_device = c.get_capIsDevice() != 0;
        snapshot.untyped_present = true;
    } else if tag == 4 {
        let c = cap::cap_endpoint_cap(raw);
        snapshot.object_addr = c.get_capEPPtr() as usize;
        snapshot.object_present = true;
        snapshot.can_read = c.get_capCanReceive() != 0;
        snapshot.can_write = c.get_capCanSend() != 0;
        snapshot.can_grant = c.get_capCanGrant() != 0;
        snapshot.can_grant_reply = c.get_capCanGrantReply() != 0;
        snapshot.badge = c.get_capEPBadge();
        snapshot.badge_present = true;
    } else if tag == 6 {
        let c = cap::cap_notification_cap(raw);
        snapshot.object_addr = c.get_capNtfnPtr() as usize;
        snapshot.object_present = true;
        snapshot.can_read = c.get_capNtfnCanReceive() != 0;
        snapshot.can_write = c.get_capNtfnCanSend() != 0;
        snapshot.badge = c.get_capNtfnBadge();
        snapshot.badge_present = true;
    } else if tag == 8 {
        let c = cap::cap_reply_cap(raw);
        snapshot.object_addr = c.get_capTCBPtr() as usize;
        snapshot.object_present = true;
        snapshot.can_grant = c.get_capReplyCanGrant() != 0;
    } else if tag == 10 {
        let c = cap::cap_cnode_cap(raw);
        snapshot.object_addr = c.get_capCNodePtr() as usize;
        snapshot.object_present = true;
        snapshot.cnode_guard = c.get_capCNodeGuard();
        snapshot.cnode_guard_size = c.get_capCNodeGuardSize();
        snapshot.cnode_radix = c.get_capCNodeRadix();
        snapshot.cnode_present = true;
    } else if tag == 12 {
        let c = cap::cap_thread_cap(raw);
        snapshot.object_addr = c.get_capTCBPtr() as usize;
        snapshot.object_present = true;
    } else if tag == 16 {
        let c = cap::cap_irq_handler_cap(raw);
        snapshot.object_addr = c.get_capIRQ() as usize;
        snapshot.object_present = true;
    } else if tag == 18 {
        let c = cap::cap_zombie_cap(raw);
        snapshot.object_addr = c.get_capZombieID() as usize;
        snapshot.object_present = true;
    } else if tag == 1 {
        let c = cap::cap_frame_cap(raw);
        snapshot.object_addr = c.get_capFBasePtr() as usize;
        snapshot.object_present = true;
    } else if tag == 3 {
        let c = cap::cap_page_table_cap(raw);
        snapshot.object_addr = c.get_capPTBasePtr() as usize;
        snapshot.object_present = true;
    } else if tag == 13 {
        let c = cap::cap_asid_pool_cap(raw);
        snapshot.object_addr = c.get_capASIDPool() as usize;
        snapshot.object_present = true;
    }

    snapshot
}

#[verifier::external_body]
pub fn trusted_extract_cte(slot: &cte_t) -> (out: CteSnapshot)
    ensures
        cte_snapshot_wf(out),
        view_cte(out) == trusted_view_cte(slot),
{
    CteSnapshot {
        cap: trusted_extract_cap(&slot.capability),
        mdb_prev_addr: slot.cteMDBNode.get_mdbPrev() as usize,
        mdb_next_addr: slot.cteMDBNode.get_mdbNext() as usize,
        mdb_revocable: slot.cteMDBNode.get_mdbRevocable() != 0,
        mdb_first_badged: slot.cteMDBNode.get_mdbFirstBadged() != 0,
    }
}

#[verifier::external_body]
pub fn trusted_extract_resolve_address_bits_ret(
    raw: &resolveAddressBits_ret_t,
) -> (out: ResolveAddressBitsRetSnapshot)
    ensures
        resolve_address_bits_ret_snapshot_wf(out),
        view_resolve_address_bits_ret(out) == trusted_view_resolve_address_bits_ret(raw),
{
    ResolveAddressBitsRetSnapshot {
        status_is_success: raw.status == exception_t::EXCEPTION_NONE,
        status_is_lookup_fault: raw.status == exception_t::EXCEPTION_LOOKUP_FAULT,
        slot_addr: raw.slot as usize,
        slot_present: !raw.slot.is_null(),
        bits_remaining: raw.bitsRemaining,
    }
}

impl CapBridge {
    pub open spec fn view(self) -> CapSpec {
        view_cap(self.snapshot)
    }

    pub open spec fn wf(self) -> bool {
        cap_snapshot_wf(self.snapshot)
    }
}

impl CteBridge {
    pub open spec fn view(self) -> SlotEntrySpec {
        view_cte(self.snapshot)
    }

    pub open spec fn wf(self) -> bool {
        cte_snapshot_wf(self.snapshot)
    }
}

impl ResolveAddressBitsRetBridge {
    pub open spec fn view(self) -> ResolveAddressBitsRetCoreSpec {
        view_resolve_address_bits_ret(self.snapshot)
    }

    pub open spec fn wf(self) -> bool {
        resolve_address_bits_ret_snapshot_wf(self.snapshot)
    }
}

pub fn bridge_cap(raw: &cap) -> (out: CapBridge)
    ensures
        out.wf(),
        out.view() == trusted_view_cap(raw),
{
    let snapshot = trusted_extract_cap(raw);
    CapBridge { snapshot }
}

pub fn bridge_cte(slot: &cte_t) -> (out: CteBridge)
    ensures
        out.wf(),
        out.view() == trusted_view_cte(slot),
{
    let snapshot = trusted_extract_cte(slot);
    CteBridge { snapshot }
}

pub fn bridge_resolve_address_bits_ret(
    raw: &resolveAddressBits_ret_t,
) -> (out: ResolveAddressBitsRetBridge)
    ensures
        out.wf(),
        out.view() == trusted_view_resolve_address_bits_ret(raw),
{
    let snapshot = trusted_extract_resolve_address_bits_ret(raw);
    ResolveAddressBitsRetBridge { snapshot }
}

pub open spec fn refines_cap(concrete_view: CapSpec, abstract_cap: CapSpec) -> bool {
    concrete_view == abstract_cap
}

pub open spec fn refines_cte(concrete_view: SlotEntrySpec, abstract_slot: SlotEntrySpec) -> bool {
    concrete_view == abstract_slot
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
            // Follow l4v's phase split: compute the candidate child slot first,
            // then classify guard/depth/success outcomes.
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

pub open spec fn resolve_address_bits_expected_core(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
) -> ResolveAddressBitsRetCoreSpec {
    resolve_address_bits_expected_core_from_cap(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
    )
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

/// Trusted heap bridge vocabulary shared by Stage 5/6 proofs.
///
/// We keep the trusted surface split into:
/// 1. concrete slot entries matching abstract `SlotEntrySpec`;
/// 2. concrete CNode offset lookup matching abstract `cnode_lookup`.
///
/// This is narrower and more reusable than a single monolithic
/// "entire concrete CSpace matches this state" predicate.
///
/// Stage 5 now needs two flavors of this vocabulary:
/// 1. a single-heap, read-only form used by `resolve_address_bits`;
/// 2. a heap-indexed form used by `cte_insert` / `cte_move` / `cte_swap`,
///    where we need to relate pre/post concrete heaps without jumping
///    straight to a whole-heap post-state black box.
pub uninterp spec fn trusted_concrete_slot_view_at(
    heap: ConcreteHeapId,
    slot: SlotId,
) -> SlotEntrySpec;

pub uninterp spec fn trusted_concrete_cnode_lookup_slot_at(
    heap: ConcreteHeapId,
    cnode_obj: ObjectRef,
    offset: int,
) -> SlotId;

pub uninterp spec fn trusted_slot_ref_is_id(
    slot: &cte_t,
    id: SlotId,
) -> bool;

pub open spec fn trusted_slot_pair_refs_are_ids(
    slot1: &cte_t,
    slot1_id: SlotId,
    slot2: &cte_t,
    slot2_id: SlotId,
) -> bool {
    &&& trusted_slot_ref_is_id(slot1, slot1_id)
    &&& trusted_slot_ref_is_id(slot2, slot2_id)
}

pub open spec fn is_final_cap_call_pre_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slot: SlotId,
    raw_slot: &cte_t,
) -> bool {
    &&& state.has_slot(slot)
    &&& trusted_slot_ref_is_id(raw_slot, slot)
    &&& trusted_cspace_heap_matches_state_at(heap, state)
}

#[verifier::external_body]
pub proof fn lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slot: SlotId,
    raw_slot: &cte_t,
)
    requires
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        trusted_view_cte(raw_slot) == state.slot_entry(slot),
        trusted_view_cte(raw_slot).cap == state.slot_cap(slot),
{
}

#[verifier::external_body]
pub fn trusted_follow_mdb_next(raw_slot: &cte_t) -> (out: &'static cte_t)
    requires
        trusted_view_cte(raw_slot).mdb_next is Some,
    ensures
        trusted_slot_ref_is_id(out, trusted_view_cte(raw_slot).mdb_next.unwrap()),
{
    convert_to_type_ref::<cte_t>(raw_slot.cteMDBNode.get_mdbNext() as usize)
}

#[verifier::external_body]
pub fn trusted_mdb_next_slot_id(raw_slot: &cte_t) -> (out: usize)
    ensures
        out == if trusted_view_cte(raw_slot).mdb_next is Some {
            trusted_view_cte(raw_slot).mdb_next.unwrap() as usize
        } else {
            0usize
        },
{
    raw_slot.cteMDBNode.get_mdbNext() as usize
}

#[verifier::external_body]
pub fn trusted_has_mdb_next(raw_slot: &cte_t) -> (ret: bool)
    ensures
        ret == (trusted_view_cte(raw_slot).mdb_next is Some),
{
    raw_slot.cteMDBNode.get_mdbNext() != 0
}

pub open spec fn derive_cap_call_pre_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slot: SlotId,
    raw_slot: &cte_t,
    raw_capability: &cap,
) -> bool {
    &&& is_final_cap_call_pre_at(heap, state, slot, raw_slot)
    &&& spec_derive_cap_pre(state, slot, trusted_view_cap(raw_capability))
}

pub open spec fn is_mdb_parent_of_call_pre_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
    parent: SlotId,
    child: SlotId,
    raw_parent: &cte_t,
    raw_child: &cte_t,
) -> bool {
    &&& state.has_slot(parent)
    &&& state.has_slot(child)
    &&& trusted_slot_pair_refs_are_ids(raw_parent, parent, raw_child, child)
    &&& trusted_cspace_heap_matches_state_at(heap, state)
}

pub proof fn lemma_derive_cap_call_pre_at_implies_slot_refines(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slot: SlotId,
    raw_slot: &cte_t,
    raw_capability: &cap,
)
    requires
        derive_cap_call_pre_at(heap, state, slot, raw_slot, raw_capability),
    ensures
        refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view_at(heap, slot).cap, state.slot_cap(slot)),
{
    assert(trusted_cspace_heap_matches_state_at(heap, state));
    assert(trusted_cspace_slot_views_match_state_at(heap, state));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(heap, state, slot);
}

pub proof fn lemma_is_mdb_parent_of_call_pre_at_implies_parent_child_refine(
    heap: ConcreteHeapId,
    state: CSpaceState,
    parent: SlotId,
    child: SlotId,
    raw_parent: &cte_t,
    raw_child: &cte_t,
)
    requires
        is_mdb_parent_of_call_pre_at(heap, state, parent, child, raw_parent, raw_child),
    ensures
        refines_cte(trusted_concrete_slot_view_at(heap, parent), state.slot_entry(parent)),
        refines_cap(trusted_concrete_slot_view_at(heap, parent).cap, state.slot_cap(parent)),
        refines_cte(trusted_concrete_slot_view_at(heap, child), state.slot_entry(child)),
        refines_cap(trusted_concrete_slot_view_at(heap, child).cap, state.slot_cap(child)),
{
    assert(trusted_cspace_heap_matches_state_at(heap, state));
    assert(trusted_cspace_slot_views_match_state_at(heap, state));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(heap, state, parent);
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(heap, state, child);
}

pub open spec fn trusted_cspace_selected_slot_views_match_state_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slots: Set<SlotId>,
) -> bool {
    forall|slot: SlotId| #![auto]
        slots.contains(slot) ==> {
            &&& state.has_slot(slot)
            &&& refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot))
        }
}

pub open spec fn trusted_cspace_slot_views_match_state_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
) -> bool {
    forall|slot: SlotId| #![auto]
        state.has_slot(slot) ==> refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot))
}

pub open spec fn trusted_cspace_cnode_lookups_match_state_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
) -> bool {
    forall|obj: ObjectRef, offset: int| #![auto]
        state.cnode_lookup.dom().contains(obj) && state.cnode_lookup[obj].dom().contains(offset)
            ==> trusted_concrete_cnode_lookup_slot_at(heap, obj, offset) == state.cnode_lookup[obj][offset]
}

pub open spec fn trusted_cspace_heap_matches_state_at(
    heap: ConcreteHeapId,
    state: CSpaceState,
) -> bool {
    &&& trusted_cspace_slot_views_match_state_at(heap, state)
    &&& trusted_cspace_cnode_lookups_match_state_at(heap, state)
}

pub open spec fn trusted_cspace_slots_unchanged_except_at(
    old_heap: ConcreteHeapId,
    new_heap: ConcreteHeapId,
    old_state: CSpaceState,
    changed: Set<SlotId>,
) -> bool {
    forall|slot: SlotId| #![auto]
        old_state.has_slot(slot) && !changed.contains(slot)
            ==> trusted_concrete_slot_view_at(new_heap, slot)
                == trusted_concrete_slot_view_at(old_heap, slot)
}

pub open spec fn trusted_cspace_cnode_lookups_unchanged_at(
    old_heap: ConcreteHeapId,
    new_heap: ConcreteHeapId,
    old_state: CSpaceState,
) -> bool {
    forall|obj: ObjectRef, offset: int| #![auto]
        old_state.cnode_lookup.dom().contains(obj) && old_state.cnode_lookup[obj].dom().contains(offset)
            ==> trusted_concrete_cnode_lookup_slot_at(new_heap, obj, offset)
                == trusted_concrete_cnode_lookup_slot_at(old_heap, obj, offset)
}

pub open spec fn trusted_cspace_local_heap_transition_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(old_heap, old_state)
    &&& trusted_cspace_selected_slot_views_match_state_at(new_heap, new_state, changed)
    &&& trusted_cspace_slots_unchanged_except_at(old_heap, new_heap, old_state, changed)
    &&& trusted_cspace_cnode_lookups_unchanged_at(old_heap, new_heap, old_state)
}

pub proof fn lemma_trusted_cspace_selected_slot_views_match_state_at_implies_slot_refines(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slots: Set<SlotId>,
    slot: SlotId,
)
    requires
        trusted_cspace_selected_slot_views_match_state_at(heap, state, slots),
        slots.contains(slot),
    ensures
        state.has_slot(slot),
        refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view_at(heap, slot).cap, state.slot_cap(slot)),
{
    assert(state.has_slot(slot));
    assert(refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot)));
    assert(state.slot_cap(slot) == state.slot_entry(slot).cap);
    assert(refines_cap(trusted_concrete_slot_view_at(heap, slot).cap, state.slot_cap(slot)));
}

pub proof fn lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(
    heap: ConcreteHeapId,
    state: CSpaceState,
    slot: SlotId,
)
    requires
        trusted_cspace_slot_views_match_state_at(heap, state),
        state.has_slot(slot),
    ensures
        refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view_at(heap, slot).cap, state.slot_cap(slot)),
{
    assert(refines_cte(trusted_concrete_slot_view_at(heap, slot), state.slot_entry(slot)));
    assert(state.slot_cap(slot) == state.slot_entry(slot).cap);
    assert(refines_cap(trusted_concrete_slot_view_at(heap, slot).cap, state.slot_cap(slot)));
}

pub proof fn lemma_trusted_cspace_cnode_lookups_match_state_at_implies_lookup_entry(
    heap: ConcreteHeapId,
    state: CSpaceState,
    obj: ObjectRef,
    offset: int,
)
    requires
        trusted_cspace_cnode_lookups_match_state_at(heap, state),
        state.cnode_lookup.dom().contains(obj),
        state.cnode_lookup[obj].dom().contains(offset),
    ensures
        trusted_concrete_cnode_lookup_slot_at(heap, obj, offset) == state.cnode_lookup[obj][offset],
        state.cnode_slot_at(obj, offset) == Some(trusted_concrete_cnode_lookup_slot_at(heap, obj, offset)),
{
    assert(trusted_concrete_cnode_lookup_slot_at(heap, obj, offset) == state.cnode_lookup[obj][offset]);
    assert(state.cnode_slot_at(obj, offset) == Some(state.cnode_lookup[obj][offset]));
}

pub proof fn lemma_trusted_cspace_cnode_lookups_match_state_at_implies_cap_lookup_entry(
    heap: ConcreteHeapId,
    state: CSpaceState,
    cnode_cap: CapSpec,
    offset: int,
)
    requires
        trusted_cspace_cnode_lookups_match_state_at(heap, state),
        cnode_cap.kind == CapKind::CNodeCap,
        cnode_cap.object is Some,
        state.cnode_lookup.dom().contains(cnode_cap.object.unwrap()),
        state.cnode_lookup[cnode_cap.object.unwrap()].dom().contains(offset),
    ensures
        state.cnode_cap_slot_at(cnode_cap, offset)
            == Some(trusted_concrete_cnode_lookup_slot_at(heap, cnode_cap.object.unwrap(), offset)),
{
    let obj = cnode_cap.object.unwrap();
    lemma_trusted_cspace_cnode_lookups_match_state_at_implies_lookup_entry(
        heap,
        state,
        obj,
        offset,
    );
    assert(state.cnode_cap_slot_at(cnode_cap, offset) == Some(state.cnode_lookup[obj][offset]));
}

pub proof fn lemma_trusted_cspace_slots_unchanged_except_at_implies_slot_view_eq(
    old_heap: ConcreteHeapId,
    new_heap: ConcreteHeapId,
    old_state: CSpaceState,
    changed: Set<SlotId>,
    slot: SlotId,
)
    requires
        trusted_cspace_slots_unchanged_except_at(old_heap, new_heap, old_state, changed),
        old_state.has_slot(slot),
        !changed.contains(slot),
    ensures
        trusted_concrete_slot_view_at(new_heap, slot) == trusted_concrete_slot_view_at(old_heap, slot),
{
    assert(trusted_concrete_slot_view_at(new_heap, slot) == trusted_concrete_slot_view_at(old_heap, slot));
}

pub proof fn lemma_trusted_cspace_cnode_lookups_unchanged_at_implies_lookup_entry_eq(
    old_heap: ConcreteHeapId,
    new_heap: ConcreteHeapId,
    old_state: CSpaceState,
    obj: ObjectRef,
    offset: int,
)
    requires
        trusted_cspace_cnode_lookups_unchanged_at(old_heap, new_heap, old_state),
        old_state.cnode_lookup.dom().contains(obj),
        old_state.cnode_lookup[obj].dom().contains(offset),
    ensures
        trusted_concrete_cnode_lookup_slot_at(new_heap, obj, offset)
            == trusted_concrete_cnode_lookup_slot_at(old_heap, obj, offset),
{
    assert(
        trusted_concrete_cnode_lookup_slot_at(new_heap, obj, offset)
            == trusted_concrete_cnode_lookup_slot_at(old_heap, obj, offset)
    );
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_implies_changed_slot_refines_new_state(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
    slot: SlotId,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        changed.contains(slot),
    ensures
        new_state.has_slot(slot),
        refines_cte(trusted_concrete_slot_view_at(new_heap, slot), new_state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view_at(new_heap, slot).cap, new_state.slot_cap(slot)),
{
    lemma_trusted_cspace_selected_slot_views_match_state_at_implies_slot_refines(
        new_heap,
        new_state,
        changed,
        slot,
    );
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
    slot: SlotId,
    expected: SlotEntrySpec,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        changed.contains(slot),
        new_state.slot_entry(slot) == expected,
    ensures
        trusted_concrete_slot_view_at(new_heap, slot) == expected,
        refines_cte(trusted_concrete_slot_view_at(new_heap, slot), expected),
        refines_cap(trusted_concrete_slot_view_at(new_heap, slot).cap, expected.cap),
{
    lemma_trusted_cspace_local_heap_transition_at_implies_changed_slot_refines_new_state(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        slot,
    );
    assert(trusted_concrete_slot_view_at(new_heap, slot) == new_state.slot_entry(slot));
    assert(trusted_concrete_slot_view_at(new_heap, slot) == expected);
    assert(refines_cte(trusted_concrete_slot_view_at(new_heap, slot), expected));
    assert(refines_cap(trusted_concrete_slot_view_at(new_heap, slot).cap, expected.cap));
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_implies_untouched_slot_refines_old_state(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
    slot: SlotId,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        old_state.has_slot(slot),
        !changed.contains(slot),
    ensures
        trusted_concrete_slot_view_at(new_heap, slot) == trusted_concrete_slot_view_at(old_heap, slot),
        refines_cte(trusted_concrete_slot_view_at(new_heap, slot), old_state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view_at(new_heap, slot).cap, old_state.slot_cap(slot)),
{
    lemma_trusted_cspace_slots_unchanged_except_at_implies_slot_view_eq(
        old_heap,
        new_heap,
        old_state,
        changed,
        slot,
    );
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(
        old_heap,
        old_state,
        slot,
    );
    assert(refines_cte(trusted_concrete_slot_view_at(new_heap, slot), old_state.slot_entry(slot)));
    assert(refines_cap(trusted_concrete_slot_view_at(new_heap, slot).cap, old_state.slot_cap(slot)));
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_implies_post_slot_views_match_state_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        slots_unchanged_except(old_state, new_state, changed),
    ensures
        trusted_cspace_slot_views_match_state_at(new_heap, new_state),
{
    assert forall|slot: SlotId| #![auto]
        new_state.has_slot(slot) ==> refines_cte(trusted_concrete_slot_view_at(new_heap, slot), new_state.slot_entry(slot)) by {
        if new_state.has_slot(slot) {
            assert(new_state.slots.dom().contains(slot));
            assert(new_state.slots.dom() =~= old_state.slots.dom());
            assert(new_state.slots.dom().contains(slot) == old_state.slots.dom().contains(slot));
            assert(old_state.has_slot(slot));
            if changed.contains(slot) {
                lemma_trusted_cspace_local_heap_transition_at_implies_changed_slot_refines_new_state(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    changed,
                    slot,
                );
            } else {
                lemma_trusted_cspace_local_heap_transition_at_implies_untouched_slot_refines_old_state(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    changed,
                    slot,
                );
                lemma_slots_unchanged_except_preserves_slot_data(
                    old_state,
                    new_state,
                    changed,
                    slot,
                );
                assert(refines_cte(trusted_concrete_slot_view_at(new_heap, slot), new_state.slot_entry(slot)));
            }
        }
    }
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_implies_post_cnode_lookups_match_state_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        new_state.cnode_lookup =~= old_state.cnode_lookup,
    ensures
        trusted_cspace_cnode_lookups_match_state_at(new_heap, new_state),
{
    assert forall|obj: ObjectRef, offset: int| #![auto]
        new_state.cnode_lookup.dom().contains(obj) && new_state.cnode_lookup[obj].dom().contains(offset)
            ==> trusted_concrete_cnode_lookup_slot_at(new_heap, obj, offset) == new_state.cnode_lookup[obj][offset] by {
        if new_state.cnode_lookup.dom().contains(obj) && new_state.cnode_lookup[obj].dom().contains(offset) {
            assert(new_state.cnode_lookup.dom().contains(obj));
            assert(new_state.cnode_lookup.dom() =~= old_state.cnode_lookup.dom());
            assert(new_state.cnode_lookup.dom().contains(obj) == old_state.cnode_lookup.dom().contains(obj));
            assert(old_state.cnode_lookup.dom().contains(obj));
            assert(new_state.cnode_lookup[obj].dom().contains(offset));
            assert(new_state.cnode_lookup[obj] =~= old_state.cnode_lookup[obj]);
            assert(
                new_state.cnode_lookup[obj].dom().contains(offset)
                    == old_state.cnode_lookup[obj].dom().contains(offset)
            );
            assert(old_state.cnode_lookup[obj].dom().contains(offset));
            lemma_trusted_cspace_cnode_lookups_unchanged_at_implies_lookup_entry_eq(
                old_heap,
                new_heap,
                old_state,
                obj,
                offset,
            );
            lemma_trusted_cspace_cnode_lookups_match_state_at_implies_lookup_entry(
                old_heap,
                old_state,
                obj,
                offset,
            );
            assert(new_state.cnode_lookup[obj][offset] == old_state.cnode_lookup[obj][offset]);
        }
    }
}

pub proof fn lemma_trusted_cspace_local_heap_transition_at_implies_post_heap_matches_state_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    changed: Set<SlotId>,
)
    requires
        trusted_cspace_local_heap_transition_at(old_heap, old_state, new_heap, new_state, changed),
        slots_unchanged_except(old_state, new_state, changed),
        new_state.cnode_lookup =~= old_state.cnode_lookup,
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
{
    lemma_trusted_cspace_local_heap_transition_at_implies_post_slot_views_match_state_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
    );
    lemma_trusted_cspace_local_heap_transition_at_implies_post_cnode_lookups_match_state_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
    );
}

pub open spec fn cte_insert_bridge_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(old_heap, old_state)
    &&& spec_cte_insert_pre(old_state, src, dest, trusted_view_cap(raw_new_cap))
}

pub open spec fn cte_insert_call_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
    src_slot: &cte_t,
    dest_slot: &cte_t,
) -> bool {
    &&& trusted_slot_pair_refs_are_ids(src_slot, src, dest_slot, dest)
    &&& cte_insert_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap)
}

pub open spec fn cte_insert_local_heap_transition_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
) -> bool {
    trusted_cspace_local_heap_transition_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        spec_cte_insert_changed_slots(old_state, src, dest),
    )
}

pub open spec fn insert_new_cap_bridge_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    parent: SlotId,
    slot: SlotId,
    raw_new_cap: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(old_heap, old_state)
    &&& spec_insert_new_cap_pre(old_state, parent, slot, trusted_view_cap(raw_new_cap))
}

pub open spec fn insert_new_cap_call_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    parent: SlotId,
    slot: SlotId,
    raw_new_cap: &cap,
    raw_parent: &cte_t,
    raw_slot: &cte_t,
) -> bool {
    &&& trusted_slot_pair_refs_are_ids(raw_parent, parent, raw_slot, slot)
    &&& insert_new_cap_bridge_pre_at(old_heap, old_state, parent, slot, raw_new_cap)
}

pub open spec fn insert_new_cap_local_heap_transition_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    parent: SlotId,
    slot: SlotId,
) -> bool {
    trusted_cspace_local_heap_transition_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        spec_cte_insert_changed_slots(old_state, parent, slot),
    )
}

pub proof fn lemma_insert_new_cap_local_heap_transition_post_implies_expected_parent_slot_views(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    parent: SlotId,
    slot: SlotId,
    new_cap: CapSpec,
)
    requires
        old_state.has_slot(parent),
        old_state.has_slot(slot),
        new_state.has_slot(parent),
        new_state.has_slot(slot),
        insert_new_cap_local_heap_transition_at(old_heap, old_state, new_heap, new_state, parent, slot),
        spec_insert_new_cap_post(old_state, new_state, parent, slot, new_cap),
    ensures
        trusted_concrete_slot_view_at(new_heap, parent)
            == spec_insert_new_cap_expected_parent_entry(old_state, parent, slot),
        trusted_concrete_slot_view_at(new_heap, slot)
            == spec_insert_new_cap_expected_slot_entry(old_state, parent, slot, new_cap),
{
    let changed = spec_cte_insert_changed_slots(old_state, parent, slot);
    lemma_insert_new_cap_post_implies_expected_parent_slot_entries(
        old_state,
        new_state,
        parent,
        slot,
        new_cap,
    );
    lemma_cte_insert_changed_slots_contains_src_dest(old_state, parent, slot);
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        parent,
        spec_insert_new_cap_expected_parent_entry(old_state, parent, slot),
    );
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        slot,
        spec_insert_new_cap_expected_slot_entry(old_state, parent, slot, new_cap),
    );
}

pub proof fn lemma_cte_insert_bridge_pre_at_implies_src_dest_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
)
    requires
        cte_insert_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap),
    ensures
        refines_cte(trusted_concrete_slot_view_at(old_heap, src), old_state.slot_entry(src)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, src).cap, old_state.slot_cap(src)),
        refines_cte(trusted_concrete_slot_view_at(old_heap, dest), old_state.slot_entry(dest)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, dest).cap, old_state.slot_cap(dest)),
{
    assert(spec_cte_insert_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, src);
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, dest);
}

pub proof fn lemma_cte_insert_bridge_pre_at_implies_old_next_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
)
    requires
        cte_insert_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap),
        old_state.slot_entry(src).mdb_next is Some,
    ensures
        refines_cte(
            trusted_concrete_slot_view_at(old_heap, old_state.slot_entry(src).mdb_next.unwrap()),
            old_state.slot_entry(old_state.slot_entry(src).mdb_next.unwrap()),
        ),
        refines_cap(
            trusted_concrete_slot_view_at(old_heap, old_state.slot_entry(src).mdb_next.unwrap()).cap,
            old_state.slot_cap(old_state.slot_entry(src).mdb_next.unwrap()),
        ),
{
    assert(spec_cte_insert_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
    assert(old_state.wf());
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_wf_implies_valid_slot_entry(old_state, src);
    let next = old_state.slot_entry(src).mdb_next.unwrap();
    assert(old_state.has_slot(next));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, next);
}

pub proof fn lemma_cte_insert_local_heap_transition_post_implies_expected_src_dest_views(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
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
        cte_insert_local_heap_transition_at(old_heap, old_state, new_heap, new_state, src, dest),
        spec_cte_insert_post(
            old_state,
            new_state,
            src,
            dest,
            new_cap,
            new_cap_is_revocable,
        ),
    ensures
        trusted_concrete_slot_view_at(new_heap, src)
            == spec_cte_insert_expected_src_entry(old_state, src, dest, new_cap),
        trusted_concrete_slot_view_at(new_heap, dest)
            == spec_cte_insert_expected_dest_entry(
                old_state,
                src,
                dest,
                new_cap,
                new_cap_is_revocable,
            ),
{
    let changed = spec_cte_insert_changed_slots(old_state, src, dest);
    lemma_cte_insert_post_implies_expected_src_dest_entries(
        old_state,
        new_state,
        src,
        dest,
        new_cap,
        new_cap_is_revocable,
    );
    lemma_cte_insert_changed_slots_contains_src_dest(old_state, src, dest);
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        src,
        spec_cte_insert_expected_src_entry(old_state, src, dest, new_cap),
    );
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        dest,
        spec_cte_insert_expected_dest_entry(
            old_state,
            src,
            dest,
            new_cap,
            new_cap_is_revocable,
        ),
    );
}

pub open spec fn cte_move_bridge_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(old_heap, old_state)
    &&& spec_cte_move_pre(old_state, src, dest, trusted_view_cap(raw_new_cap))
}

pub open spec fn cte_move_call_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
    src_slot: &cte_t,
    dest_slot: &cte_t,
) -> bool {
    &&& trusted_slot_pair_refs_are_ids(src_slot, src, dest_slot, dest)
    &&& cte_move_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap)
}

pub open spec fn cte_move_local_heap_transition_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
) -> bool {
    trusted_cspace_local_heap_transition_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        spec_cte_move_changed_slots(old_state, src, dest),
    )
}

pub proof fn lemma_cte_move_bridge_pre_at_implies_src_dest_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
)
    requires
        cte_move_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap),
    ensures
        refines_cte(trusted_concrete_slot_view_at(old_heap, src), old_state.slot_entry(src)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, src).cap, old_state.slot_cap(src)),
        refines_cte(trusted_concrete_slot_view_at(old_heap, dest), old_state.slot_entry(dest)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, dest).cap, old_state.slot_cap(dest)),
{
    assert(spec_cte_move_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, src);
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, dest);
}

pub proof fn lemma_cte_move_bridge_pre_at_implies_neighbors_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
)
    requires
        cte_move_bridge_pre_at(old_heap, old_state, src, dest, raw_new_cap),
    ensures
        old_state.slot_entry(src).mdb_prev is Some ==> {
            let prev = old_state.slot_entry(src).mdb_prev.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, prev), old_state.slot_entry(prev))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, prev).cap, old_state.slot_cap(prev))
        },
        old_state.slot_entry(src).mdb_next is Some ==> {
            let next = old_state.slot_entry(src).mdb_next.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, next), old_state.slot_entry(next))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, next).cap, old_state.slot_cap(next))
        },
{
    assert(spec_cte_move_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
    assert(old_state.wf());
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_wf_implies_valid_slot_entry(old_state, src);
    if old_state.slot_entry(src).mdb_prev is Some {
        let prev = old_state.slot_entry(src).mdb_prev.unwrap();
        assert(old_state.has_slot(prev));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, prev);
    }
    if old_state.slot_entry(src).mdb_next is Some {
        let next = old_state.slot_entry(src).mdb_next.unwrap();
        assert(old_state.has_slot(next));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, next);
    }
}

pub proof fn lemma_cte_move_local_heap_transition_post_implies_expected_src_dest_views(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
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
        cte_move_local_heap_transition_at(old_heap, old_state, new_heap, new_state, src, dest),
        spec_cte_move_post(old_state, new_state, src, dest, new_cap),
    ensures
        trusted_concrete_slot_view_at(new_heap, src) == spec_cte_move_expected_src_entry(),
        trusted_concrete_slot_view_at(new_heap, dest)
            == spec_cte_move_expected_dest_entry(old_state, src, new_cap),
{
    let changed = spec_cte_move_changed_slots(old_state, src, dest);
    lemma_cte_move_post_implies_expected_src_dest_entries(
        old_state,
        new_state,
        src,
        dest,
        new_cap,
    );
    lemma_cte_move_changed_slots_contains_core(old_state, src, dest);
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        src,
        spec_cte_move_expected_src_entry(),
    );
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        dest,
        spec_cte_move_expected_dest_entry(old_state, src, new_cap),
    );
}

pub open spec fn cte_swap_bridge_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    slot1: SlotId,
    slot2: SlotId,
    raw_cap1: &cap,
    raw_cap2: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(old_heap, old_state)
    &&& spec_cte_swap_pre(
        old_state,
        slot1,
        slot2,
        trusted_view_cap(raw_cap1),
        trusted_view_cap(raw_cap2),
    )
}

pub open spec fn cte_swap_call_pre_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    slot1: SlotId,
    slot2: SlotId,
    raw_cap1: &cap,
    raw_cap2: &cap,
    raw_slot1: &cte_t,
    raw_slot2: &cte_t,
) -> bool {
    &&& trusted_slot_pair_refs_are_ids(raw_slot1, slot1, raw_slot2, slot2)
    &&& cte_swap_bridge_pre_at(old_heap, old_state, slot1, slot2, raw_cap1, raw_cap2)
}

pub open spec fn cte_swap_local_heap_transition_at(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    slot1: SlotId,
    slot2: SlotId,
) -> bool {
    trusted_cspace_local_heap_transition_at(
        old_heap,
        old_state,
        new_heap,
        new_state,
        spec_cte_swap_changed_slots(old_state, slot1, slot2),
    )
}

pub proof fn lemma_cte_swap_bridge_pre_at_implies_core_slots_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    slot1: SlotId,
    slot2: SlotId,
    raw_cap1: &cap,
    raw_cap2: &cap,
)
    requires
        cte_swap_bridge_pre_at(old_heap, old_state, slot1, slot2, raw_cap1, raw_cap2),
    ensures
        refines_cte(trusted_concrete_slot_view_at(old_heap, slot1), old_state.slot_entry(slot1)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, slot1).cap, old_state.slot_cap(slot1)),
        refines_cte(trusted_concrete_slot_view_at(old_heap, slot2), old_state.slot_entry(slot2)),
        refines_cap(trusted_concrete_slot_view_at(old_heap, slot2).cap, old_state.slot_cap(slot2)),
{
    assert(spec_cte_swap_pre(
        old_state,
        slot1,
        slot2,
        trusted_view_cap(raw_cap1),
        trusted_view_cap(raw_cap2),
    ));
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, slot1);
    lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, slot2);
}

pub proof fn lemma_cte_swap_bridge_pre_at_implies_neighbors_refine(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    slot1: SlotId,
    slot2: SlotId,
    raw_cap1: &cap,
    raw_cap2: &cap,
)
    requires
        cte_swap_bridge_pre_at(old_heap, old_state, slot1, slot2, raw_cap1, raw_cap2),
    ensures
        old_state.slot_entry(slot1).mdb_prev is Some ==> {
            let prev = old_state.slot_entry(slot1).mdb_prev.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, prev), old_state.slot_entry(prev))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, prev).cap, old_state.slot_cap(prev))
        },
        old_state.slot_entry(slot1).mdb_next is Some ==> {
            let next = old_state.slot_entry(slot1).mdb_next.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, next), old_state.slot_entry(next))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, next).cap, old_state.slot_cap(next))
        },
        old_state.slot_entry(slot2).mdb_prev is Some ==> {
            let prev = old_state.slot_entry(slot2).mdb_prev.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, prev), old_state.slot_entry(prev))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, prev).cap, old_state.slot_cap(prev))
        },
        old_state.slot_entry(slot2).mdb_next is Some ==> {
            let next = old_state.slot_entry(slot2).mdb_next.unwrap();
            &&& refines_cte(trusted_concrete_slot_view_at(old_heap, next), old_state.slot_entry(next))
            &&& refines_cap(trusted_concrete_slot_view_at(old_heap, next).cap, old_state.slot_cap(next))
        },
{
    assert(spec_cte_swap_pre(
        old_state,
        slot1,
        slot2,
        trusted_view_cap(raw_cap1),
        trusted_view_cap(raw_cap2),
    ));
    assert(old_state.wf());
    assert(trusted_cspace_heap_matches_state_at(old_heap, old_state));
    assert(trusted_cspace_slot_views_match_state_at(old_heap, old_state));
    lemma_wf_implies_valid_slot_entry(old_state, slot1);
    lemma_wf_implies_valid_slot_entry(old_state, slot2);
    if old_state.slot_entry(slot1).mdb_prev is Some {
        let prev = old_state.slot_entry(slot1).mdb_prev.unwrap();
        assert(old_state.has_slot(prev));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, prev);
    }
    if old_state.slot_entry(slot1).mdb_next is Some {
        let next = old_state.slot_entry(slot1).mdb_next.unwrap();
        assert(old_state.has_slot(next));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, next);
    }
    if old_state.slot_entry(slot2).mdb_prev is Some {
        let prev = old_state.slot_entry(slot2).mdb_prev.unwrap();
        assert(old_state.has_slot(prev));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, prev);
    }
    if old_state.slot_entry(slot2).mdb_next is Some {
        let next = old_state.slot_entry(slot2).mdb_next.unwrap();
        assert(old_state.has_slot(next));
        lemma_trusted_cspace_slot_views_match_state_at_implies_slot_refines(old_heap, old_state, next);
    }
}

pub proof fn lemma_cte_swap_local_heap_transition_post_implies_expected_slot_views(
    old_heap: ConcreteHeapId,
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
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
        cte_swap_local_heap_transition_at(old_heap, old_state, new_heap, new_state, slot1, slot2),
        spec_cte_swap_post(old_state, new_state, slot1, slot2, cap1, cap2),
    ensures
        trusted_concrete_slot_view_at(new_heap, slot1)
            == spec_cte_swap_expected_slot1_entry(old_state, slot1, slot2, cap2),
        trusted_concrete_slot_view_at(new_heap, slot2)
            == spec_cte_swap_expected_slot2_entry(old_state, slot1, slot2, cap1),
{
    let changed = spec_cte_swap_changed_slots(old_state, slot1, slot2);
    lemma_cte_swap_post_implies_expected_slot_entries(
        old_state,
        new_state,
        slot1,
        slot2,
        cap1,
        cap2,
    );
    lemma_cte_swap_changed_slots_contains_core(old_state, slot1, slot2);
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        slot1,
        spec_cte_swap_expected_slot1_entry(old_state, slot1, slot2, cap2),
    );
    lemma_trusted_cspace_local_heap_transition_at_and_slot_entry_eq_implies_concrete_slot_eq(
        old_heap,
        old_state,
        new_heap,
        new_state,
        changed,
        slot2,
        spec_cte_swap_expected_slot2_entry(old_state, slot1, slot2, cap1),
    );
}

pub uninterp spec fn trusted_concrete_slot_view(slot: SlotId) -> SlotEntrySpec;

pub uninterp spec fn trusted_concrete_cnode_lookup_slot(
    cnode_obj: ObjectRef,
    offset: int,
) -> SlotId;

pub open spec fn trusted_cspace_slot_views_match_state(state: CSpaceState) -> bool {
    forall|slot: SlotId| #![auto]
        state.has_slot(slot) ==> refines_cte(trusted_concrete_slot_view(slot), state.slot_entry(slot))
}

pub open spec fn trusted_cspace_cnode_lookups_match_state(state: CSpaceState) -> bool {
    forall|obj: ObjectRef, offset: int| #![auto]
        state.cnode_lookup.dom().contains(obj) && state.cnode_lookup[obj].dom().contains(offset)
            ==> trusted_concrete_cnode_lookup_slot(obj, offset) == state.cnode_lookup[obj][offset]
}

pub open spec fn trusted_cspace_heap_matches_state(state: CSpaceState) -> bool {
    &&& trusted_cspace_slot_views_match_state(state)
    &&& trusted_cspace_cnode_lookups_match_state(state)
}

pub proof fn lemma_trusted_cspace_slot_views_match_state_implies_slot_refines(
    state: CSpaceState,
    slot: SlotId,
)
    requires
        trusted_cspace_slot_views_match_state(state),
        state.has_slot(slot),
    ensures
        refines_cte(trusted_concrete_slot_view(slot), state.slot_entry(slot)),
        refines_cap(trusted_concrete_slot_view(slot).cap, state.slot_cap(slot)),
{
    assert(refines_cte(trusted_concrete_slot_view(slot), state.slot_entry(slot)));
    assert(state.slot_cap(slot) == state.slot_entry(slot).cap);
    assert(refines_cap(trusted_concrete_slot_view(slot).cap, state.slot_cap(slot)));
}

pub proof fn lemma_trusted_cspace_cnode_lookups_match_state_implies_lookup_entry(
    state: CSpaceState,
    obj: ObjectRef,
    offset: int,
)
    requires
        trusted_cspace_cnode_lookups_match_state(state),
        state.cnode_lookup.dom().contains(obj),
        state.cnode_lookup[obj].dom().contains(offset),
    ensures
        trusted_concrete_cnode_lookup_slot(obj, offset) == state.cnode_lookup[obj][offset],
        state.cnode_slot_at(obj, offset) == Some(trusted_concrete_cnode_lookup_slot(obj, offset)),
{
    assert(trusted_concrete_cnode_lookup_slot(obj, offset) == state.cnode_lookup[obj][offset]);
    assert(state.cnode_slot_at(obj, offset) == Some(state.cnode_lookup[obj][offset]));
}

pub proof fn lemma_trusted_cspace_cnode_lookups_match_state_implies_cap_lookup_entry(
    state: CSpaceState,
    cnode_cap: CapSpec,
    offset: int,
)
    requires
        trusted_cspace_cnode_lookups_match_state(state),
        cnode_cap.kind == CapKind::CNodeCap,
        cnode_cap.object is Some,
        state.cnode_lookup.dom().contains(cnode_cap.object.unwrap()),
        state.cnode_lookup[cnode_cap.object.unwrap()].dom().contains(offset),
    ensures
        state.cnode_cap_slot_at(cnode_cap, offset)
            == Some(trusted_concrete_cnode_lookup_slot(cnode_cap.object.unwrap(), offset)),
{
    let obj = cnode_cap.object.unwrap();
    lemma_trusted_cspace_cnode_lookups_match_state_implies_lookup_entry(state, obj, offset);
    assert(state.cnode_cap_slot_at(cnode_cap, offset) == Some(state.cnode_lookup[obj][offset]));
}

pub open spec fn resolve_address_bits_bridge_pre(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
) -> bool {
    &&& trusted_cspace_heap_matches_state(state)
    &&& valid_cap(trusted_view_cap(raw_root))
    &&& spec_resolve_address_bits_pre(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
    )
}

pub open spec fn resolve_address_bits_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    concrete_view: ResolveAddressBitsRetCoreSpec,
) -> bool {
    resolve_address_bits_core_refines_cap(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        concrete_view,
    )
}

pub open spec fn resolve_address_bits_one_step_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    concrete_view: ResolveAddressBitsRetCoreSpec,
) -> bool {
    let root_cap = trusted_view_cap(raw_root);
    if !(root_cap.kind == CapKind::CNodeCap
        && root_cap.cnode is Some
        && root_cap.object is Some) {
        concrete_view == resolve_address_bits_fault_core(bits as int)
    } else {
        let level_bits = spec_cnode_level_bits(root_cap);
        // Mirror the l4v control-flow skeleton: identify the next slot before
        // dispatching guard/depth/success cases.
        let next_slot = spec_resolve_address_bits_next_slot(
            state,
            root_cap,
            cap_ptr as int,
            bits as int,
        );
        if !spec_resolve_guard_matches(root_cap, cap_ptr as int, bits as int) {
            concrete_view == resolve_address_bits_fault_core(bits as int)
        } else if level_bits > bits as int {
            concrete_view == resolve_address_bits_fault_core(bits as int)
        } else {
            next_slot is Some
            && state.has_slot(next_slot.unwrap())
            && {
                let next = next_slot.unwrap();
                if bits as int == level_bits {
                    concrete_view == resolve_address_bits_success_core(next, 0)
                } else {
                    let remaining = bits as int - level_bits;
                    if state.slot_cap(next).kind == CapKind::CNodeCap {
                        resolve_address_bits_core_refines_cap(
                            state,
                            state.slot_cap(next),
                            cap_ptr as int,
                            remaining,
                            concrete_view,
                        )
                    } else {
                        concrete_view == resolve_address_bits_success_core(next, remaining)
                    }
                }
            }
        }
    }
}

pub proof fn lemma_resolve_address_bits_one_step_refines_state_implies_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    concrete_view: ResolveAddressBitsRetCoreSpec,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        resolve_address_bits_one_step_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            concrete_view,
        ),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            concrete_view,
        ),
{
    let root_cap = trusted_view_cap(raw_root);
    if !(root_cap.kind == CapKind::CNodeCap
        && root_cap.cnode is Some
        && root_cap.object is Some) {
        assert(concrete_view == resolve_address_bits_fault_core(bits as int));
        lemma_resolve_address_bits_invalid_root_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
        );
        assert(resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            concrete_view,
        ));
    } else {
        assert(spec_resolve_address_bits_pre(
            state,
            root_cap,
            cap_ptr as int,
            bits as int,
        ));
        lemma_resolve_pre_implies_root_lookup_ready(
            state,
            root_cap,
            cap_ptr as int,
            bits as int,
        );
        let level_bits = spec_cnode_level_bits(root_cap);
        if !spec_resolve_guard_matches(root_cap, cap_ptr as int, bits as int) {
            assert(concrete_view == resolve_address_bits_fault_core(bits as int));
            lemma_resolve_address_bits_guard_mismatch_core_refines_state(
                state,
                raw_root,
                cap_ptr,
                bits,
            );
            assert(resolve_address_bits_core_refines_state(
                state,
                raw_root,
                cap_ptr,
                bits,
                concrete_view,
            ));
        } else if level_bits > bits as int {
            assert(concrete_view == resolve_address_bits_fault_core(bits as int));
            lemma_resolve_address_bits_depth_mismatch_core_refines_state(
                state,
                raw_root,
                cap_ptr,
                bits,
            );
            assert(resolve_address_bits_core_refines_state(
                state,
                raw_root,
                cap_ptr,
                bits,
                concrete_view,
            ));
        } else {
            let offset = spec_extract_bits(
                cap_ptr as int,
                bits as int - level_bits,
                root_cap.cnode->Some_0.radix_bits,
            );
            lemma_extract_bits_range(
                cap_ptr as int,
                bits as int - level_bits,
                root_cap.cnode->Some_0.radix_bits,
            );
            lemma_resolve_known_offset_implies_next_slot_exists(
                state,
                root_cap,
                cap_ptr as int,
                bits as int,
                offset,
            );
            let next_slot = spec_resolve_address_bits_next_slot(
                state,
                root_cap,
                cap_ptr as int,
                bits as int,
            );
            assert(next_slot is Some);
            let next = next_slot.unwrap();
            assert(state.has_slot(next));
            if bits as int == level_bits {
                assert(concrete_view == resolve_address_bits_success_core(next, 0));
                lemma_resolve_address_bits_exact_success_core_refines_state(
                    state,
                    raw_root,
                    cap_ptr,
                    bits,
                    next,
                );
                assert(resolve_address_bits_core_refines_state(
                    state,
                    raw_root,
                    cap_ptr,
                    bits,
                    concrete_view,
                ));
            } else {
                let remaining = bits as int - level_bits;
                let next_cap = state.slot_cap(next);
                if next_cap.kind == CapKind::CNodeCap {
                    assert(resolve_address_bits_core_refines_cap(
                        state,
                        next_cap,
                        cap_ptr as int,
                        remaining,
                        concrete_view,
                    ));
                    let child_result = choose|child_result: ResolveAddressBitsResultSpec|
                        spec_resolve_address_bits(
                            state,
                            next_cap,
                            cap_ptr as int,
                            remaining,
                            child_result,
                        ) && refines_resolve_address_bits_ret(concrete_view, child_result);
                    assert(spec_resolve_address_bits(
                        state,
                        next_cap,
                        cap_ptr as int,
                        remaining,
                        child_result,
                    ));
                    assert(refines_resolve_address_bits_ret(concrete_view, child_result));
                    if child_result.status == ResolveAddressBitsStatusSpec::Success {
                        let slot = child_result.slot.unwrap();
                        let bits_left = child_result.bits_remaining;
                        assert(child_result.fault is None);
                        assert(spec_resolve_address_bits_success(
                            state,
                            next_cap,
                            cap_ptr as int,
                            remaining,
                            slot,
                            bits_left,
                        ));
                        assert(concrete_view == resolve_address_bits_success_core(slot, bits_left));
                        lemma_resolve_address_bits_recursive_success_core_refines_state(
                            state,
                            raw_root,
                            cap_ptr,
                            bits,
                            next,
                            slot,
                            bits_left,
                        );
                        assert(resolve_address_bits_core_refines_state(
                            state,
                            raw_root,
                            cap_ptr,
                            bits,
                            concrete_view,
                        ));
                    } else {
                        assert(child_result.status == ResolveAddressBitsStatusSpec::LookupFault);
                        assert(child_result.fault is Some);
                        assert(spec_resolve_address_bits_fault(
                            state,
                            next_cap,
                            cap_ptr as int,
                            remaining,
                            child_result,
                        ));
                        assert(concrete_view == project_resolve_address_bits_result_core(child_result));
                        lemma_resolve_address_bits_recursive_fault_core_refines_state(
                            state,
                            raw_root,
                            cap_ptr,
                            bits,
                            next,
                            child_result,
                        );
                        assert(resolve_address_bits_core_refines_state(
                            state,
                            raw_root,
                            cap_ptr,
                            bits,
                            concrete_view,
                        ));
                    }
                } else {
                    assert(concrete_view == resolve_address_bits_success_core(next, remaining));
                    lemma_resolve_address_bits_early_stop_core_refines_state(
                        state,
                        raw_root,
                        cap_ptr,
                        bits,
                        next,
                    );
                    assert(resolve_address_bits_core_refines_state(
                        state,
                        raw_root,
                        cap_ptr,
                        bits,
                        concrete_view,
                    ));
                }
            }
        }
    }
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
                    lemma_wf_implies_valid_slot_entry(state, next);
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

pub proof fn lemma_resolve_address_bits_expected_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            resolve_address_bits_expected_core(state, raw_root, cap_ptr, bits),
        ),
{
    lemma_resolve_address_bits_expected_core_refines_cap(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
    );
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
                    lemma_wf_implies_valid_slot_entry(state, next);
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
                        lemma_wf_implies_valid_slot_entry(state, next);
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

pub proof fn lemma_resolve_address_bits_core_refines_state_implies_expected_core(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    concrete_view: ResolveAddressBitsRetCoreSpec,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        resolve_address_bits_core_refines_state(state, raw_root, cap_ptr, bits, concrete_view),
    ensures
        concrete_view == resolve_address_bits_expected_core(state, raw_root, cap_ptr, bits),
{
    assert(spec_resolve_address_bits_pre(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
    ));
    assert(valid_cap(trusted_view_cap(raw_root)));
    lemma_resolve_address_bits_core_refines_cap_implies_expected_core_from_cap(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        concrete_view,
    );
}

pub proof fn lemma_resolve_address_bits_result_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    abstract_result: ResolveAddressBitsResultSpec,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        spec_resolve_address_bits(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
            abstract_result,
        ),
        abstract_result.status == ResolveAddressBitsStatusSpec::Success ==> abstract_result.fault is None,
        abstract_result.status == ResolveAddressBitsStatusSpec::LookupFault ==> abstract_result.fault is Some,
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            project_resolve_address_bits_result_core(abstract_result),
        ),
{
    lemma_projected_resolve_address_bits_result_refines(abstract_result);
    assert(resolve_address_bits_core_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        project_resolve_address_bits_result_core(abstract_result),
    ));
}

pub proof fn lemma_resolve_address_bits_success_result_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    slot: SlotId,
    bits_left: int,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        state.has_slot(slot),
        0 <= bits_left <= bits as int,
        spec_resolve_address_bits_success(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
            slot,
            bits_left,
        ),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::Success,
                slot: Some(slot),
                bits_remaining: bits_left,
            },
        ),
{
    let abstract_result = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::Success,
        slot: Some(slot),
        bits_remaining: bits_left,
        fault: None,
    };
    lemma_resolve_address_bits_success_result_implies_contract(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        slot,
        bits_left,
    );
    lemma_resolve_address_bits_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn lemma_resolve_address_bits_fault_result_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    abstract_result: ResolveAddressBitsResultSpec,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        abstract_result.status == ResolveAddressBitsStatusSpec::LookupFault,
        abstract_result.fault is Some,
        spec_resolve_address_bits_fault(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
            abstract_result,
        ),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            project_resolve_address_bits_result_core(abstract_result),
        ),
{
    lemma_resolve_address_bits_fault_result_implies_contract(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        abstract_result,
    );
    lemma_resolve_address_bits_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn lemma_resolve_address_bits_exact_success_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    slot: SlotId,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        state.has_slot(slot),
        0 < spec_cnode_level_bits(trusted_view_cap(raw_root)),
        spec_cnode_level_bits(trusted_view_cap(raw_root)) == bits as int,
        spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
        spec_resolve_address_bits_next_slot(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ) == Some(slot),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::Success,
                slot: Some(slot),
                bits_remaining: 0,
            },
        ),
{
    lemma_resolve_address_bits_exact_success(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        slot,
    );
    lemma_resolve_address_bits_success_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        slot,
        0,
    );
}

pub proof fn lemma_resolve_address_bits_early_stop_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    slot: SlotId,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        state.has_slot(slot),
        0 < spec_cnode_level_bits(trusted_view_cap(raw_root)),
        spec_cnode_level_bits(trusted_view_cap(raw_root)) < bits as int,
        spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
        spec_resolve_address_bits_next_slot(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ) == Some(slot),
        state.slot_cap(slot).kind != CapKind::CNodeCap,
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::Success,
                slot: Some(slot),
                bits_remaining: bits as int - spec_cnode_level_bits(trusted_view_cap(raw_root)),
            },
        ),
{
    let bits_left = bits as int - spec_cnode_level_bits(trusted_view_cap(raw_root));
    lemma_resolve_address_bits_early_stop_success(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        slot,
    );
    lemma_resolve_address_bits_success_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        slot,
        bits_left,
    );
}

pub proof fn lemma_resolve_address_bits_invalid_root_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        !(trusted_view_cap(raw_root).kind == CapKind::CNodeCap
            && trusted_view_cap(raw_root).cnode is Some
            && trusted_view_cap(raw_root).object is Some),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::LookupFault,
                slot: None,
                bits_remaining: bits as int,
            },
        ),
{
    let abstract_result = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::LookupFault,
        slot: None,
        bits_remaining: bits as int,
        fault: Some(ResolveAddressBitsFaultSpec::InvalidRoot),
    };
    assert(spec_resolve_invalid_root_fault(
        trusted_view_cap(raw_root),
        bits as int,
        abstract_result,
    ));
    lemma_resolve_invalid_root_fault_implies_fault(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        abstract_result,
    );
    lemma_resolve_address_bits_fault_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn lemma_resolve_address_bits_guard_mismatch_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        !spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::LookupFault,
                slot: None,
                bits_remaining: bits as int,
            },
        ),
{
    let abstract_result = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::LookupFault,
        slot: None,
        bits_remaining: bits as int,
        fault: Some(ResolveAddressBitsFaultSpec::GuardMismatch {
            bits_left: bits as int,
            guard_found: trusted_view_cap(raw_root).cnode.unwrap().guard,
            guard_size: trusted_view_cap(raw_root).cnode.unwrap().guard_size,
        }),
    };
    assert(spec_resolve_guard_mismatch_fault(
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        abstract_result,
    ));
    lemma_resolve_guard_mismatch_fault_implies_fault(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        abstract_result,
    );
    lemma_resolve_address_bits_fault_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn lemma_resolve_address_bits_depth_mismatch_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
        spec_cnode_level_bits(trusted_view_cap(raw_root)) > bits as int,
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::LookupFault,
                slot: None,
                bits_remaining: bits as int,
            },
        ),
{
    let abstract_result = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::LookupFault,
        slot: None,
        bits_remaining: bits as int,
        fault: Some(ResolveAddressBitsFaultSpec::DepthMismatch {
            bits_left: bits as int,
            bits_found: spec_cnode_level_bits(trusted_view_cap(raw_root)),
        }),
    };
    assert(spec_resolve_depth_mismatch_fault(
        trusted_view_cap(raw_root),
        bits as int,
        abstract_result,
    ));
    lemma_resolve_depth_mismatch_fault_implies_fault(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        abstract_result,
    );
    lemma_resolve_address_bits_fault_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn lemma_resolve_address_bits_recursive_success_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    next: SlotId,
    slot: SlotId,
    bits_left: int,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        state.has_slot(next),
        state.has_slot(slot),
        0 < spec_cnode_level_bits(trusted_view_cap(raw_root)),
        spec_cnode_level_bits(trusted_view_cap(raw_root)) < bits as int,
        spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
        spec_resolve_address_bits_next_slot(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ) == Some(next),
        state.slot_cap(next).kind == CapKind::CNodeCap,
        spec_resolve_address_bits_success(
            state,
            state.slot_cap(next),
            cap_ptr as int,
            bits as int - spec_cnode_level_bits(trusted_view_cap(raw_root)),
            slot,
            bits_left,
        ),
        0 <= bits_left <= bits as int - spec_cnode_level_bits(trusted_view_cap(raw_root)),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ResolveAddressBitsRetCoreSpec {
                status: ResolveAddressBitsStatusSpec::Success,
                slot: Some(slot),
                bits_remaining: bits_left,
            },
        ),
{
    lemma_resolve_address_bits_recursive_success(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        next,
        slot,
        bits_left,
    );
    lemma_resolve_address_bits_success_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        slot,
        bits_left,
    );
}

pub proof fn lemma_resolve_address_bits_recursive_fault_core_refines_state(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    next: SlotId,
    abstract_result: ResolveAddressBitsResultSpec,
)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
        trusted_view_cap(raw_root).kind == CapKind::CNodeCap,
        trusted_view_cap(raw_root).cnode is Some,
        trusted_view_cap(raw_root).object is Some,
        state.has_slot(next),
        0 < spec_cnode_level_bits(trusted_view_cap(raw_root)),
        spec_cnode_level_bits(trusted_view_cap(raw_root)) < bits as int,
        spec_resolve_guard_matches(
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ),
        spec_resolve_address_bits_next_slot(
            state,
            trusted_view_cap(raw_root),
            cap_ptr as int,
            bits as int,
        ) == Some(next),
        state.slot_cap(next).kind == CapKind::CNodeCap,
        abstract_result.status == ResolveAddressBitsStatusSpec::LookupFault,
        abstract_result.fault is Some,
        spec_resolve_address_bits_fault(
            state,
            state.slot_cap(next),
            cap_ptr as int,
            bits as int - spec_cnode_level_bits(trusted_view_cap(raw_root)),
            abstract_result,
        ),
    ensures
        resolve_address_bits_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            project_resolve_address_bits_result_core(abstract_result),
        ),
{
    lemma_resolve_address_bits_recursive_fault(
        state,
        trusted_view_cap(raw_root),
        cap_ptr as int,
        bits as int,
        next,
        abstract_result,
    );
    lemma_resolve_address_bits_fault_result_refines_state(
        state,
        raw_root,
        cap_ptr,
        bits,
        abstract_result,
    );
}

pub proof fn refinement_bridge_smoke_check() {
    let endpoint_snapshot = CapSnapshot {
        tag: 4,
        object_addr: 0x1000usize,
        object_present: true,
        can_read: true,
        can_write: true,
        can_grant: false,
        can_grant_reply: false,
        badge: 7,
        badge_present: true,
        cnode_guard: 0,
        cnode_guard_size: 0,
        cnode_radix: 0,
        cnode_present: false,
        untyped_block_size: 0,
        untyped_free_index: 0,
        untyped_is_device: false,
        untyped_present: false,
    };

    let cnode_snapshot = CapSnapshot {
        tag: 10,
        object_addr: 0x2000usize,
        object_present: true,
        can_read: false,
        can_write: false,
        can_grant: false,
        can_grant_reply: false,
        badge: 0,
        badge_present: false,
        cnode_guard: 3,
        cnode_guard_size: 2,
        cnode_radix: 4,
        cnode_present: true,
        untyped_block_size: 0,
        untyped_free_index: 0,
        untyped_is_device: false,
        untyped_present: false,
    };

    let cte_snapshot = CteSnapshot {
        cap: endpoint_snapshot,
        mdb_prev_addr: 0x3000usize,
        mdb_next_addr: 0usize,
        mdb_revocable: true,
        mdb_first_badged: true,
    };

    let success_snapshot = ResolveAddressBitsRetSnapshot {
        status_is_success: true,
        status_is_lookup_fault: false,
        slot_addr: 0x4000usize,
        slot_present: true,
        bits_remaining: 0usize,
    };

    let fault_snapshot = ResolveAddressBitsRetSnapshot {
        status_is_success: false,
        status_is_lookup_fault: true,
        slot_addr: 0usize,
        slot_present: false,
        bits_remaining: 5usize,
    };

    assert(cap_snapshot_wf(endpoint_snapshot));
    assert(cte_snapshot_wf(cte_snapshot));
    assert(resolve_address_bits_ret_snapshot_wf(success_snapshot));
    assert(resolve_address_bits_ret_snapshot_wf(fault_snapshot));

    assert(view_cap(endpoint_snapshot).kind == CapKind::EndpointCap);
    assert(view_cap(endpoint_snapshot).object == Some(ObjectRef {
        id: 0x1000int,
        kind: ObjectKind::Endpoint,
    }));
    assert(view_cap(endpoint_snapshot).badge == Some(7int));

    assert(view_cap(cnode_snapshot).kind == CapKind::CNodeCap);
    assert(view_cap(cnode_snapshot).cnode == Some(CNodeCapDataSpec {
        radix_bits: 4,
        guard: 3,
        guard_size: 2,
    }));

    assert(view_cte(cte_snapshot).mdb_prev == Some(0x3000int));
    assert(view_cte(cte_snapshot).mdb_next is None);
    assert(view_cte(cte_snapshot).mdb_revocable);

    assert(view_resolve_address_bits_ret(success_snapshot) == ResolveAddressBitsRetCoreSpec {
        status: ResolveAddressBitsStatusSpec::Success,
        slot: Some(0x4000int),
        bits_remaining: 0,
    });
    assert(view_resolve_address_bits_ret(fault_snapshot) == ResolveAddressBitsRetCoreSpec {
        status: ResolveAddressBitsStatusSpec::LookupFault,
        slot: None,
        bits_remaining: 5,
    });

    let abstract_endpoint = view_cap(endpoint_snapshot);
    let abstract_cte = view_cte(cte_snapshot);
    let abstract_success = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::Success,
        slot: Some(0x4000int),
        bits_remaining: 0,
        fault: None,
    };
    let abstract_fault = ResolveAddressBitsResultSpec {
        status: ResolveAddressBitsStatusSpec::LookupFault,
        slot: None,
        bits_remaining: 5,
        fault: Some(ResolveAddressBitsFaultSpec::InvalidRoot),
    };

    assert(refines_cap(abstract_endpoint, abstract_endpoint));
    assert(refines_cte(abstract_cte, abstract_cte));
    assert(refines_resolve_address_bits_ret(
        view_resolve_address_bits_ret(success_snapshot),
        abstract_success,
    ));
    assert(refines_resolve_address_bits_ret(
        view_resolve_address_bits_ret(fault_snapshot),
        abstract_fault,
    ));
    lemma_projected_resolve_address_bits_result_refines(abstract_success);
    lemma_projected_resolve_address_bits_result_refines(abstract_fault);
}

} // verus!
