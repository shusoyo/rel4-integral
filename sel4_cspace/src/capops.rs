use crate::interface::{cte_insert, cte_move, cte_swap, cte_t};
use sel4_common::structures_gen::{cap, cap_tag, endpoint};
use sel4_common::{
    sel4_config::SEL4_ILLEGAL_OPERATION, shared_types_bf_gen::seL4_CapRights,
    structures::exception_t, utils::convert_to_mut_type_ref,
};

use log::debug;

pub enum CSpaceOpError {
    IllegalOperation,
    DeleteFirst,
    FailedOnDeriveCap(exception_t),
}

pub type CSpaceOpResult = Result<(), CSpaceOpError>;

#[inline]
pub fn cspace_copy(
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    cap_right: seL4_CapRights,
) -> CSpaceOpResult {
    let src_cap = mask_cap_rights(cap_right, &src_slot.capability);

    let dc_ret = src_slot.derive_cap(&src_cap);
    if dc_ret.status != exception_t::EXCEPTION_NONE {
        return Err(CSpaceOpError::FailedOnDeriveCap(dc_ret.status));
    }
    if dc_ret.capability.get_tag() == cap_tag::cap_null_cap {
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;
        return Err(CSpaceOpError::IllegalOperation);
    }

    cte_insert(&dc_ret.capability, src_slot, dest_slot);

    Ok(())
    // exception_t::EXCEPTION_NONE
}

#[inline]
pub fn cspace_mint(
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    cap_right: seL4_CapRights,
    cap_data: usize,
) -> CSpaceOpResult {
    let src_cap = mask_cap_rights(cap_right, &src_slot.capability);
    let new_cap = src_cap.update_data(false, cap_data as u64);
    let dc_ret = src_slot.derive_cap(&new_cap);

    if dc_ret.status != exception_t::EXCEPTION_NONE {
        debug!("Error deriving cap for CNode Copy operation.");
        return Err(CSpaceOpError::FailedOnDeriveCap(dc_ret.status));
    }

    if dc_ret.capability.get_tag() == cap_tag::cap_null_cap {
        debug!("CNode Mint:Mint cap would be invalid.");
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;

        return Err(CSpaceOpError::IllegalOperation);
    }
    cte_insert(&dc_ret.capability, src_slot, dest_slot);

    Ok(())
    // exception_t::EXCEPTION_NONE
}

#[inline]
pub fn cspace_mutate(
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    cap_data: usize,
) -> CSpaceOpResult {
    let new_cap = src_slot.capability.update_data(true, cap_data as u64);
    if new_cap.get_tag() == cap_tag::cap_null_cap {
        debug!("CNode Mint:Mint cap would be invalid.");
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;

        return Err(CSpaceOpError::IllegalOperation);
    }

    // set_thread_state(get_currenct_thread(), ThreadState::ThreadStateRestart);

    cte_move(&new_cap, src_slot, dest_slot);
    // exception_t::EXCEPTION_NONE
    Ok(())
}

#[inline]
pub fn invoke_cnode_rotate(
    slot1: &mut cte_t,
    slot2: &mut cte_t,
    slot3: &mut cte_t,
    src_new_data: usize,
    pivot_new_data: usize,
) -> CSpaceOpResult {
    let new_src_cap = slot1.capability.update_data(true, src_new_data as u64);
    let new_pivot_cap = slot2.capability.update_data(true, pivot_new_data as u64);

    if new_src_cap.get_tag() == cap_tag::cap_null_cap {
        debug!("CNode Rotate: Source cap invalid");
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;

        return Err(CSpaceOpError::IllegalOperation);
    }

    if new_pivot_cap.get_tag() == cap_tag::cap_null_cap {
        debug!("CNode Rotate: Pivot cap invalid");
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;
        return Err(CSpaceOpError::IllegalOperation);
    }

    // set_thread_state(get_currenct_thread(), ThreadState::ThreadStateRestart);

    if slot1.get_ptr() == slot3.get_ptr() {
        cte_swap(&new_src_cap, slot1, &new_pivot_cap, slot2);
    } else {
        cte_move(&new_pivot_cap, slot2, slot3);
        cte_move(&new_src_cap, slot1, slot2);
    }

    // exception_t::EXCEPTION_NONE
    Ok(())
}

#[inline]
pub fn cspace_move(src_slot: &mut cte_t, dest_slot: &mut cte_t) -> CSpaceOpResult {
    let src_cap = &src_slot.clone().capability;
    if src_cap.get_tag() == cap_tag::cap_null_cap {
        debug!("CNode Copy/Mint/Move/Mutate: Mutated cap would be invalid.");
        // unsafe {
        //     current_syscall_error._type = SEL4_ILLEGAL_OPERATION;
        // }
        // return exception_t::EXCEPTION_SYSCALL_ERROR;
        return Err(CSpaceOpError::IllegalOperation);
    }

    // set_thread_state(get_currenct_thread(), ThreadState::ThreadStateRestart);
    cte_move(&src_cap, src_slot, dest_slot);

    // exception_t::EXCEPTION_NONE
    Ok(())
}

#[inline]
pub fn cspace_revoke(dest_slot: &mut cte_t) -> exception_t {
    // set_thread_state(get_currenct_thread(), ThreadState::ThreadStateRestart);
    dest_slot.revoke()
}

#[inline]
pub fn cspace_delete(dest_slot: &mut cte_t) -> exception_t {
    // set_thread_state(get_currenct_thread(), ThreadState::ThreadStateRestart);
    dest_slot.delete_all(true)
}

use crate::arch::arch_mask_cap_rights;
use crate::capability::cap_func;
use sel4_common::arch::maskVMRights;
use sel4_common::structures_gen::cap_Splayed;

pub fn mask_cap_rights(rights: seL4_CapRights, capability: &cap) -> cap {
    if capability.is_arch_cap() {
        return arch_mask_cap_rights(rights, capability);
    }
    match capability.clone().splay() {
        cap_Splayed::endpoint_cap(data) => {
            let capability_copy = &capability.clone();
            let new_cap = cap::cap_endpoint_cap(capability_copy);
            new_cap.set_capCanSend(data.get_capCanSend() & rights.get_capAllowWrite() as u64);
            new_cap.set_capCanReceive(data.get_capCanReceive() & rights.get_capAllowRead() as u64);
            new_cap.set_capCanGrant(data.get_capCanGrant() & rights.get_capAllowGrant() as u64);
            new_cap.set_capCanGrantReply(
                data.get_capCanGrantReply() & rights.get_capAllowGrantReply() as u64,
            );
            capability_copy.clone()
        }
        cap_Splayed::notification_cap(data) => {
            let capability_copy = &capability.clone();
            let new_cap = cap::cap_notification_cap(capability_copy);
            new_cap
                .set_capNtfnCanSend(data.get_capNtfnCanSend() & rights.get_capAllowWrite() as u64);
            new_cap.set_capNtfnCanReceive(
                data.get_capNtfnCanReceive() & rights.get_capAllowRead() as u64,
            );
            capability_copy.clone()
        }
        cap_Splayed::reply_cap(data) => {
            let capability_copy = &capability.clone();
            let new_cap = cap::cap_reply_cap(capability_copy);
            new_cap.set_capReplyCanGrant(
                data.get_capReplyCanGrant() & rights.get_capAllowGrant() as u64,
            );
            capability_copy.clone()
        }
        cap_Splayed::frame_cap(data) => {
            let capability_copy = &capability.clone();
            let new_cap = cap::cap_frame_cap(capability_copy);
            let mut vm_rights = unsafe { core::mem::transmute(data.get_capFVMRights()) };
            vm_rights = maskVMRights(vm_rights, rights);
            new_cap.set_capFVMRights(vm_rights as u64);
            capability_copy.clone()
        }
        _ => capability.clone(),
    }
}
