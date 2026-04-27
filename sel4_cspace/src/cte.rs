//! `CSpace Table Entry`相关操作的具体实现，包含`cte`链表的插入删除等。
use super::{
    capability::{is_cap_revocable, same_object_as, same_region_as},
    deps::{finalise_cap, post_cap_deletion, preemption_point},
    structures::{finaliseSlot_ret, resolveAddressBits_ret_t},
};
use crate::capability::{
    cap_func,
    zombie::{cap_cyclic_zombie, zombie_func},
};
use core::intrinsics::{likely, unlikely};
use core::ptr;
use sel4_common::{
    sel4_bitfield_types::Bitfield,
    structures_gen::{cap, cap_null_cap, cap_tag, mdb_node},
};
use sel4_common::{
    sel4_config::WORD_RADIX,
    utils::{convert_to_option_mut_type_ref, max_free_index},
};
use sel4_common::{
    structures::exception_t,
    utils::{convert_to_mut_type_ref, convert_to_type_ref},
};
#[cfg(feature = "verify")]
use vstd::prelude::*;

#[repr(C)]
#[derive(Clone)]
pub struct deriveCap_ret {
    pub status: exception_t,
    pub capability: cap,
}

/// 由cap_t和 mdb_node 组成，是CSpace的基本组成单元
#[repr(C)]
#[derive(Clone, Debug)]
pub struct cte_t {
    pub capability: cap,
    pub cteMDBNode: mdb_node,
}

impl cte_t {
    pub fn get_ptr(&self) -> usize {
        self as *const cte_t as usize
    }

    pub fn get_offset_slot(&self, index: usize) -> &'static mut Self {
        convert_to_mut_type_ref::<Self>(self.get_ptr() + core::mem::size_of::<cte_t>() * index)
    }

    #[cfg_attr(feature = "verify", verifier::external)]
    pub fn derive_cap(&self, capability: &cap) -> deriveCap_ret {
        if capability.is_arch_cap() {
            return self.arch_derive_cap(capability);
        }
        let mut ret = deriveCap_ret {
            status: exception_t::EXCEPTION_NONE,
            capability: cap_null_cap::new().unsplay(),
        };

        match capability.get_tag() {
            cap_tag::cap_zombie_cap => {
                ret.capability = cap_null_cap::new().unsplay();
            }
            cap_tag::cap_untyped_cap => {
                ret.status = self.ensure_no_children();
                if ret.status != exception_t::EXCEPTION_NONE {
                    ret.capability = cap_null_cap::new().unsplay();
                } else {
                    ret.capability = capability.clone();
                }
            }
            #[cfg(not(feature = "kernel_mcs"))]
            cap_tag::cap_reply_cap => {
                ret.capability = cap_null_cap::new().unsplay();
            }
            cap_tag::cap_irq_control_cap => {
                ret.capability = cap_null_cap::new().unsplay();
            }
            _ => {
                ret.capability = capability.clone();
            }
        }
        ret
    }
    /// 判断当前`cte`是否存在派生出来的子节点
    #[cfg_attr(feature = "verify", verifier::external)]
    pub fn ensure_no_children(&self) -> exception_t {
        if self.cteMDBNode.get_mdbNext() != 0 {
            let next = convert_to_type_ref::<cte_t>(self.cteMDBNode.get_mdbNext() as usize);
            if self.is_mdb_parent_of(next) {
                return exception_t::EXCEPTION_SYSCALL_ERROR;
            }
        }
        exception_t::EXCEPTION_NONE
    }
    /// 判断当前`cte`是否为`next`节点的父节点（除了父节点，还有兄弟节点的关系可能）
    #[cfg_attr(feature = "verify", verifier::external)]
    fn is_mdb_parent_of(&self, next: &Self) -> bool {
        if self.cteMDBNode.get_mdbRevocable() == 0 {
            return false;
        }
        if !same_region_as(&self.capability, &next.capability) {
            return false;
        }
        match self.capability.get_tag() {
            cap_tag::cap_endpoint_cap => {
                assert_eq!(next.capability.get_tag(), cap_tag::cap_endpoint_cap);
                let badge = cap::cap_endpoint_cap(&self.capability).get_capEPBadge();
                if badge == 0 {
                    return true;
                }
                badge == cap::cap_endpoint_cap(&next.capability).get_capEPBadge()
                    && next.cteMDBNode.get_mdbFirstBadged() == 0
            }
            cap_tag::cap_notification_cap => {
                assert_eq!(next.capability.get_tag(), cap_tag::cap_notification_cap);
                let badge = cap::cap_notification_cap(&self.capability).get_capNtfnBadge();
                if badge == 0 {
                    return true;
                }
                badge == cap::cap_notification_cap(&next.capability).get_capNtfnBadge()
                    && next.cteMDBNode.get_mdbFirstBadged() == 0
            }
            #[cfg(feature = "enable_smc")]
            cap_tag::cap_smc_cap => {
                let badge = cap::cap_smc_cap(&self.capability).get_capSMCBadge();
                if badge == 0 {
                    return true;
                }
                badge == cap::cap_smc_cap(&next.capability).get_capSMCBadge()
                    && next.cteMDBNode.get_mdbFirstBadged() == 0
            }
            _ => true,
        }
    }

    /// 判断当前`cte`是否是能力派生树上的最后一个能力,如果`prev`与当前指向对象，则当前`cte`不是最后一个`cap`
    /// 如果`cte`的`next`是当前`cte`派生出来的能力，则当前`cte`也不是最后一个`cap`
    #[cfg_attr(feature = "verify", verifier::external)]
    pub fn is_final_cap(&self) -> bool {
        let mdb = &self.cteMDBNode;
        let prev_is_same_obj = if mdb.get_mdbPrev() == 0 {
            false
        } else {
            let prev = convert_to_type_ref::<cte_t>(mdb.get_mdbPrev() as usize);
            same_object_as(&prev.capability, &self.capability)
        };

        if prev_is_same_obj {
            return false;
        }
        if mdb.get_mdbNext() == 0 {
            true
        } else {
            let next = convert_to_type_ref::<cte_t>(mdb.get_mdbNext() as usize);
            !same_object_as(&self.capability, &next.capability)
        }
    }

    #[cfg_attr(feature = "verify", verifier::external)]
    pub fn is_long_running_delete(&self) -> bool {
        if self.capability.get_tag() == cap_tag::cap_null_cap || !self.is_final_cap() {
            return false;
        }
        matches!(
            self.capability.get_tag(),
            cap_tag::cap_thread_cap | cap_tag::cap_zombie_cap | cap_tag::cap_cnode_cap
        )
    }

    ///清除`cte slot`中的`capability`
    /// 因为涉及到几个函数之间的来回调用，不太好理解，所以用一个`CNode cap`删除的例子来帮助理解，
    /// 假设现在有一个`CNode`的`slot`要执行`delete_all(true)`，会先调用`finalise(true)`，在`finalise_cap`中，
    /// 会将`cnode_cap`设置为`zombie_cap`，然后进入`reduce_zombie`,
    /// `reduce_zombie`会调用最后一个`slot`的`delete_all(false)`函数，然后再次进入`finalise(false)`
    /// 假设最后一个`slot`存储的`cap`为一个二级`cnode_cap`，则会在`finalise_cap`中生成一个新的`zombie_cap`，
    /// 之后再次进入`reduce_zombie(false)`，在其中进入`else`分支，
    /// 执行`cteswap`将二级`cnode_cap`中的第一个`cap`与二级`cnode_cap`进行交换，使得二级`cnode_cap`指向自身，变成`cyclicZombie`。
    /// 然后继续清除即可。至于二级`cnode_cap`其实无法被清除。
    unsafe fn finalise(&mut self, immediate: bool) -> finaliseSlot_ret {
        let mut ret = finaliseSlot_ret::default();
        while self.capability.get_tag() != cap_tag::cap_null_cap {
            let fc_ret = finalise_cap(&self.capability, self.is_final_cap(), false);
            if cap_removable(&fc_ret.remainder, self) {
                ret.status = exception_t::EXCEPTION_NONE;
                ret.success = true;
                ret.cleanupInfo = fc_ret.cleanupInfo;
                return ret;
            }
            self.capability = fc_ret.clone().remainder;
            if !immediate && cap_cyclic_zombie(&fc_ret.remainder, self) {
                ret.status = exception_t::EXCEPTION_NONE;
                ret.success = false;
                ret.cleanupInfo = fc_ret.cleanupInfo;
                return ret;
            }
            let status = self.reduce_zombie(immediate);
            if exception_t::EXCEPTION_NONE != status {
                ret.status = status;
                ret.success = false;
                ret.cleanupInfo = cap_null_cap::new().unsplay();
                return ret;
            }

            let status = preemption_point();
            if exception_t::EXCEPTION_NONE != status {
                ret.status = status;
                ret.success = false;
                ret.cleanupInfo = cap_null_cap::new().unsplay();
                return ret;
            }
        }
        ret
    }

    /// 将当前的`cte slot`中的能力清除，因为可能是`cnode_cap`或者`tcb_cap`，其中都可以存储多个`cap`，
    /// 所以可能顺带将存储的`cap`也清除掉
    pub fn delete_all(&mut self, exposed: bool) -> exception_t {
        let fs_ret = unsafe { self.finalise(exposed) };
        if fs_ret.status != exception_t::EXCEPTION_NONE {
            return fs_ret.status;
        }
        if exposed || fs_ret.success {
            self.set_empty(&fs_ret.cleanupInfo);
        }
        exception_t::EXCEPTION_NONE
    }

    /// 将当前的`cte slot`中的能力清除,要求`cap`是可删除的
    pub fn delete_one(&mut self) {
        if self.capability.get_tag() != cap_tag::cap_null_cap {
            let fc_ret = unsafe { finalise_cap(&self.capability, self.is_final_cap(), true) };
            assert!(
                cap_removable(&fc_ret.remainder, self)
                    && fc_ret.cleanupInfo.get_tag() == cap_tag::cap_null_cap
            );
            self.set_empty(&cap_null_cap::new().unsplay());
        }
    }

    /// 将当前`slot`从`capability derivation tree`中删除
    fn set_empty(&mut self, cleanup_info: &cap) {
        if self.capability.get_tag() != cap_tag::cap_null_cap {
            let mdb = &self.cteMDBNode;
            let prev_addr = mdb.get_mdbPrev() as usize;
            let next_addr = mdb.get_mdbNext() as usize;
            if prev_addr != 0 {
                let prev_node = convert_to_mut_type_ref::<cte_t>(prev_addr);
                prev_node.cteMDBNode.set_mdbNext(next_addr as u64);
            }

            if next_addr != 0 {
                let next_node = convert_to_mut_type_ref::<cte_t>(next_addr);
                next_node.cteMDBNode.set_mdbPrev(prev_addr as u64);
                let first_badged = ((next_node.cteMDBNode.get_mdbFirstBadged() != 0)
                    || (mdb.get_mdbFirstBadged() != 0)) as usize;
                next_node.cteMDBNode.set_mdbFirstBadged(first_badged as u64);
            }
            self.capability = cap_null_cap::new().unsplay();
            self.cteMDBNode = mdb_node {
                0: Bitfield { arr: [0; 2usize] },
            };
            unsafe { post_cap_deletion(cleanup_info) };
        }
    }

    /// 每次删除`zombie cap`中的最后一个`capability`,用于删除unremovable的capability。
    fn reduce_zombie(&mut self, immediate: bool) -> exception_t {
        assert_eq!(self.capability.get_tag(), cap_tag::cap_zombie_cap);
        let self_ptr = self as *mut cte_t as usize;
        let ptr = cap::cap_zombie_cap(&self.capability).get_zombie_ptr();
        let n = cap::cap_zombie_cap(&self.capability).get_zombie_number();
        let zombie_type = cap::cap_zombie_cap(&self.capability).get_capZombieType();
        assert!(n > 0);
        if immediate {
            let end_slot = unsafe { &mut *((ptr as *mut cte_t).add(n - 1)) };
            let status = end_slot.delete_all(false);
            if status != exception_t::EXCEPTION_NONE {
                return status;
            }
            match self.capability.get_tag() {
                cap_tag::cap_null_cap => {
                    return exception_t::EXCEPTION_NONE;
                }
                cap_tag::cap_zombie_cap => {
                    let ptr2 = cap::cap_zombie_cap(&self.capability).get_zombie_ptr();
                    if ptr == ptr2
                        && cap::cap_zombie_cap(&self.capability).get_zombie_number() == n
                        && cap::cap_zombie_cap(&self.capability).get_capZombieType() == zombie_type
                    {
                        assert_eq!(end_slot.capability.get_tag(), cap_tag::cap_null_cap);
                        cap::cap_zombie_cap(&self.capability).set_zombie_number(n - 1);
                    } else {
                        assert!(ptr2 == self_ptr && ptr != self_ptr);
                    }
                }
                _ => {
                    panic!("Expected recursion to result in Zombie.")
                }
            }
        } else {
            assert_ne!(ptr, self_ptr);
            let next_slot = convert_to_mut_type_ref::<cte_t>(ptr);
            let cap1 = next_slot.capability.clone();
            let cap2 = self.capability.clone();
            cte_swap(&cap1, next_slot, &cap2, self);
        }
        exception_t::EXCEPTION_NONE
    }

    #[cfg(target_arch = "riscv64")]
    #[inline]
    fn get_volatile_value(&self) -> usize {
        unsafe {
            let raw_value = ptr::read_volatile((self.get_ptr() + 24) as *const usize);
            let mut value = ((raw_value >> 2) & mask_bits!(37)) << 2;
            if (value & (1usize << 38)) != 0 {
                value |= 0xffffff8000000000;
            }
            value
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[inline]
    fn get_volatile_value(&self) -> usize {
        unsafe {
            let raw_value = ptr::read_volatile((self.get_ptr() + 24) as *const usize);
            let mut value = ((raw_value >> 2) & mask_bits!(46)) << 2;
            if (value & (1usize << 46)) != 0 {
                #[cfg(not(feature = "hypervisor"))]
                {
                    value |= 0xffffff8000000000;
                }
                #[cfg(feature = "hypervisor")]
                {
                    value |= 0x8000000000;
                }
            }
            value
        }
    }

    // 撤销当前`cte`中的`capability`
    #[inline]
    pub fn revoke(&mut self) -> exception_t {
        while let Some(cte) = convert_to_option_mut_type_ref::<cte_t>(self.get_volatile_value()) {
            if !self.is_mdb_parent_of(cte) {
                break;
            }

            let mut status = cte.delete_all(true);
            if status != exception_t::EXCEPTION_NONE {
                return status;
            }

            status = unsafe { preemption_point() };
            if status != exception_t::EXCEPTION_NONE {
                return status;
            }
        }
        exception_t::EXCEPTION_NONE
    }
}

/// 将一个cap插入slot中并维护能力派生树
///
/// 将一个new_cap插入到dest slot中并作为src slot的派生子节点插入派生树中
#[cfg_attr(feature = "verify", verifier::external)]
pub fn cte_insert(new_cap: &cap, src_slot: &mut cte_t, dest_slot: &mut cte_t) {
    let srcMDB = &mut src_slot.cteMDBNode;
    let srcCap = &(src_slot.capability.clone());
    let mut newMDB = srcMDB.clone();
    let newCapIsRevocable = is_cap_revocable(new_cap, srcCap);
    newMDB.set_mdbPrev(src_slot as *const cte_t as u64);
    newMDB.set_mdbRevocable(newCapIsRevocable as u64);
    newMDB.set_mdbFirstBadged(newCapIsRevocable as u64);

    /* Haskell error: "cteInsert to non-empty destination" */
    assert_eq!(dest_slot.capability.get_tag(), cap_tag::cap_null_cap);
    /* Haskell error: "cteInsert: mdb entry must be empty" */
    assert!(dest_slot.cteMDBNode.get_mdbNext() == 0 && dest_slot.cteMDBNode.get_mdbPrev() == 0);

    set_untyped_cap_as_full(srcCap, new_cap, src_slot);

    dest_slot.capability = new_cap.clone();
    dest_slot.cteMDBNode = newMDB.clone();
    src_slot
        .cteMDBNode
        .set_mdbNext(dest_slot as *const cte_t as u64);
    if newMDB.get_mdbNext() != 0 {
        let cte_ref = convert_to_mut_type_ref::<cte_t>(newMDB.get_mdbNext() as usize);
        cte_ref
            .cteMDBNode
            .set_mdbPrev(dest_slot as *const cte_t as u64);
    }
}

/// insert a new cap to slot, set parent's next is slot.
#[cfg_attr(feature = "verify", verifier::external)]
pub fn insert_new_cap(parent: &mut cte_t, slot: &mut cte_t, capability: &cap) {
    let next = parent.cteMDBNode.get_mdbNext() as usize;
    slot.capability = capability.clone();
    slot.cteMDBNode = mdb_node::new(next as u64, 1u64, 1u64, parent as *const cte_t as u64);
    if next != 0 {
        let next_ref = convert_to_mut_type_ref::<cte_t>(next);
        next_ref.cteMDBNode.set_mdbPrev(slot as *const cte_t as u64);
    }
    parent.cteMDBNode.set_mdbNext(slot as *const cte_t as u64);
}

/// 将一个cap插入slot中并删除原节点
///
/// 将一个new_cap插入到dest slot中并作为替代src slot在派生树中的位置
#[cfg_attr(feature = "verify", verifier::external)]
pub fn cte_move(new_cap: &cap, src_slot: &mut cte_t, dest_slot: &mut cte_t) {
    /* Haskell error: "cteInsert to non-empty destination" */
    assert_eq!(dest_slot.capability.get_tag(), cap_tag::cap_null_cap);
    /* Haskell error: "cteInsert: mdb entry must be empty" */
    assert!(dest_slot.cteMDBNode.get_mdbNext() == 0 && dest_slot.cteMDBNode.get_mdbPrev() == 0);
    let mdb = src_slot.cteMDBNode.clone();
    dest_slot.capability = new_cap.clone();
    src_slot.capability = cap_null_cap::new().unsplay();
    dest_slot.cteMDBNode = mdb.clone();
    src_slot.cteMDBNode = mdb_node::new(0, 0, 0, 0);

    let prev_ptr = mdb.clone().get_mdbPrev() as usize;
    if prev_ptr != 0 {
        let prev_ref = convert_to_mut_type_ref::<cte_t>(prev_ptr);
        prev_ref
            .cteMDBNode
            .set_mdbNext(dest_slot as *const cte_t as u64);
    }
    let next_ptr = mdb.get_mdbNext() as usize;
    if next_ptr != 0 {
        let next_ref = convert_to_mut_type_ref::<cte_t>(next_ptr);
        next_ref
            .cteMDBNode
            .set_mdbPrev(dest_slot as *const cte_t as u64);
    }
}

/// 交换两个slot，并将新的cap数据填入
#[cfg_attr(feature = "verify", verifier::external)]
pub fn cte_swap(cap1: &cap, slot1: &mut cte_t, cap2: &cap, slot2: &mut cte_t) {
    let mdb1 = slot1.cteMDBNode.clone();
    let mdb2 = slot2.cteMDBNode.clone();
    {
        let prev_ptr = mdb1.get_mdbPrev() as usize;
        if prev_ptr != 0 {
            convert_to_mut_type_ref::<cte_t>(prev_ptr)
                .cteMDBNode
                .set_mdbNext(slot2 as *const cte_t as u64);
        }
        let next_ptr = mdb1.get_mdbNext() as usize;
        if next_ptr != 0 {
            convert_to_mut_type_ref::<cte_t>(next_ptr)
                .cteMDBNode
                .set_mdbPrev(slot2 as *const cte_t as u64);
        }
    }

    slot1.capability = cap2.clone();
    //FIXME::result not right due to compiler

    slot2.capability = cap1.clone();
    slot1.cteMDBNode = mdb2.clone();
    slot2.cteMDBNode = mdb1.clone();
    {
        let prev_ptr = mdb2.get_mdbPrev() as usize;
        if prev_ptr != 0 {
            convert_to_mut_type_ref::<cte_t>(prev_ptr)
                .cteMDBNode
                .set_mdbNext(slot1 as *const cte_t as u64);
        }
        let next_ptr = mdb2.get_mdbNext() as usize;
        if next_ptr != 0 {
            convert_to_mut_type_ref::<cte_t>(next_ptr)
                .cteMDBNode
                .set_mdbPrev(slot1 as *const cte_t as u64);
        }
    }
}

/// 判断当前`cap`能否被删除，只有`CNode Capability`能够做到`slot=z_slot`，且n==1意味着是`tcb`初始分配的`CNode`。
#[inline]
fn cap_removable(capability: &cap, slot: *mut cte_t) -> bool {
    match capability.get_tag() {
        cap_tag::cap_null_cap => true,
        cap_tag::cap_zombie_cap => {
            let n = cap::cap_zombie_cap(capability).get_zombie_number();
            let ptr = cap::cap_zombie_cap(capability).get_zombie_ptr();
            let z_slot = ptr as *mut cte_t;
            n == 0 || (n == 1 && slot == z_slot)
        }
        _ => {
            panic!("Invalid cap type , finalise_cap should only return Zombie or NullCap");
        }
    }
}

/// 如果`srcCap`和`newCap`都是`UntypedCap`，并且指向同一块内存，内存大小也相同，就将`srcCap`记录为没有剩余空间。
/// 自我认为是防止同一块内存空间被分配两次
#[cfg_attr(feature = "verify", verifier::external_body)]
fn set_untyped_cap_as_full(srcCap: &cap, newCap: &cap, srcSlot: &mut cte_t) {
    if srcCap.get_tag() == cap_tag::cap_untyped_cap && newCap.get_tag() == cap_tag::cap_untyped_cap
    {
        assert_eq!(srcSlot.capability.get_tag(), cap_tag::cap_untyped_cap);
        if cap::cap_untyped_cap(srcCap).get_capPtr() == cap::cap_untyped_cap(newCap).get_capPtr()
            && cap::cap_untyped_cap(srcCap).get_capBlockSize()
                == cap::cap_untyped_cap(newCap).get_capBlockSize()
        {
            cap::cap_untyped_cap(&srcSlot.capability).set_capFreeIndex(max_free_index(
                cap::cap_untyped_cap(srcCap).get_capBlockSize() as usize,
            ) as u64);
        }
    }
}

/// 从cspace寻址特定的slot
///
/// 从给定的cnode、cap index、和depth中找到对应cap的slot，成功则返回slot指针，失败返回找到的最深的cnode
///
/// Parse cap_ptr ,get a capbility from cnode.
#[allow(unreachable_code)]
#[cfg_attr(feature = "verify", verifier::external)]
pub fn resolve_address_bits(
    node_cap: &cap,
    cap_ptr: usize,
    _n_bits: usize,
) -> resolveAddressBits_ret_t {
    let mut ret = resolveAddressBits_ret_t::default();
    let mut n_bits = _n_bits;
    ret.bitsRemaining = n_bits;
    let mut nodeCap = node_cap.clone();

    if unlikely(nodeCap.clone().get_tag() != cap_tag::cap_cnode_cap) {
        ret.status = exception_t::EXCEPTION_LOOKUP_FAULT;
        return ret;
    }

    loop {
        let cnode_cap = cap::cap_cnode_cap(&nodeCap);
        let radixBits = cnode_cap.get_capCNodeRadix() as usize;
        let guardBits = cnode_cap.get_capCNodeGuardSize() as usize;
        let levelBits = radixBits + guardBits;
        assert_ne!(levelBits, 0);
        let capGuard = cnode_cap.get_capCNodeGuard() as usize;
        let guard =
            (cap_ptr >> ((n_bits - guardBits) & mask_bits!(WORD_RADIX))) & mask_bits!(guardBits);
        if unlikely(guardBits > n_bits || guard != capGuard) {
            ret.status = exception_t::EXCEPTION_LOOKUP_FAULT;
            return ret;
        }
        if unlikely(levelBits > n_bits) {
            ret.status = exception_t::EXCEPTION_LOOKUP_FAULT;
            return ret;
        }
        let offset = (cap_ptr >> (n_bits - levelBits)) & mask_bits!(radixBits);
        let slot = unsafe { (cnode_cap.get_capCNodePtr() as *mut cte_t).add(offset) };

        if likely(n_bits == levelBits) {
            ret.slot = slot;
            ret.bitsRemaining = 0;
            return ret;
        }
        n_bits -= levelBits;
        nodeCap = unsafe { (*slot).capability.clone() };
        if unlikely(nodeCap.clone().get_tag() != cap_tag::cap_cnode_cap) {
            ret.slot = slot;
            ret.bitsRemaining = n_bits;
            return ret;
        }
    }
    panic!("UNREACHABLE");
}

#[cfg(feature = "verify")]
verus! {

#[allow(unused_imports)]
use crate::refinement_bridge::*;
#[allow(unused_imports)]
use crate::specs::abstract_cspace::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::derive::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::insert::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::queries::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::r#move::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::resolve::*;
#[allow(unused_imports)]
use crate::specs::cspace_ops::swap::*;
pub open spec fn cte_insert_exec_contract(
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
    new_cap_is_revocable: bool,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(new_heap, new_state)
    &&& spec_cte_insert(
        old_state,
        new_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
        new_cap_is_revocable,
    )
    &&& new_state.slot_entry(src)
        == spec_cte_insert_expected_src_entry(
            old_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        )
    &&& new_state.slot_entry(dest)
        == spec_cte_insert_expected_dest_entry(
            old_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        )
    &&& trusted_concrete_slot_view_at(new_heap, src)
        == spec_cte_insert_expected_src_entry(
            old_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        )
    &&& trusted_concrete_slot_view_at(new_heap, dest)
        == spec_cte_insert_expected_dest_entry(
            old_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        )
}

pub open spec fn insert_new_cap_exec_contract(
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    parent: SlotId,
    slot: SlotId,
    raw_new_cap: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(new_heap, new_state)
    &&& spec_insert_new_cap(
        old_state,
        new_state,
        parent,
        slot,
        trusted_view_cap(raw_new_cap),
    )
    &&& new_state.slot_entry(parent)
        == spec_insert_new_cap_expected_parent_entry(
            old_state,
            parent,
            slot,
        )
    &&& new_state.slot_entry(slot)
        == spec_insert_new_cap_expected_slot_entry(
            old_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        )
    &&& trusted_concrete_slot_view_at(new_heap, parent)
        == spec_insert_new_cap_expected_parent_entry(
            old_state,
            parent,
            slot,
        )
    &&& trusted_concrete_slot_view_at(new_heap, slot)
        == spec_insert_new_cap_expected_slot_entry(
            old_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        )
}

pub open spec fn cte_move_exec_contract(
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    src: SlotId,
    dest: SlotId,
    raw_new_cap: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(new_heap, new_state)
    &&& spec_cte_move(
        old_state,
        new_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
    )
    &&& new_state.slot_entry(src) == spec_cte_move_expected_src_entry()
    &&& new_state.slot_entry(dest)
        == spec_cte_move_expected_dest_entry(
            old_state,
            src,
            trusted_view_cap(raw_new_cap),
        )
    &&& trusted_concrete_slot_view_at(new_heap, src) == spec_cte_move_expected_src_entry()
    &&& trusted_concrete_slot_view_at(new_heap, dest)
        == spec_cte_move_expected_dest_entry(
            old_state,
            src,
            trusted_view_cap(raw_new_cap),
        )
}

pub open spec fn cte_swap_exec_contract(
    old_state: CSpaceState,
    new_heap: ConcreteHeapId,
    new_state: CSpaceState,
    slot1_id: SlotId,
    slot2_id: SlotId,
    raw_cap1: &cap,
    raw_cap2: &cap,
) -> bool {
    &&& trusted_cspace_heap_matches_state_at(new_heap, new_state)
    &&& spec_cte_swap(
        old_state,
        new_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap1),
        trusted_view_cap(raw_cap2),
    )
    &&& new_state.slot_entry(slot1_id)
        == spec_cte_swap_expected_slot1_entry(
            old_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap2),
        )
    &&& new_state.slot_entry(slot2_id)
        == spec_cte_swap_expected_slot2_entry(
            old_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
        )
    &&& trusted_concrete_slot_view_at(new_heap, slot1_id)
        == spec_cte_swap_expected_slot1_entry(
            old_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap2),
        )
    &&& trusted_concrete_slot_view_at(new_heap, slot2_id)
        == spec_cte_swap_expected_slot2_entry(
            old_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
        )
}

pub open spec fn resolve_address_bits_exec_contract(
    state: CSpaceState,
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    ret: ResolveAddressBitsRetBridge,
) -> bool {
    &&& ret.wf()
    &&& ret.view() == resolve_address_bits_expected_core(state, raw_root, cap_ptr, bits)
}

pub open spec fn derive_cap_exec_contract(
    state: CSpaceState,
    slot: SlotId,
    raw_capability: &cap,
    ret: &deriveCap_ret,
) -> bool {
    &&& spec_derive_cap_post(
        state,
        slot,
        trusted_view_cap(raw_capability),
        trusted_view_derive_cap_ret_capability(ret),
    )
    &&& spec_derive_cap_returns_syscall_error(
        state,
        slot,
        trusted_view_cap(raw_capability),
    ) ==> trusted_derive_cap_ret_is_syscall_error(ret)
    &&& !spec_derive_cap_returns_syscall_error(
        state,
        slot,
        trusted_view_cap(raw_capability),
    ) ==> trusted_derive_cap_ret_is_none(ret)
}

pub open spec fn is_mdb_parent_of_exec_contract(
    state: CSpaceState,
    parent: SlotId,
    child: SlotId,
    ret: bool,
) -> bool {
    spec_is_mdb_parent_of_post(state, parent, child, ret)
}

pub open spec fn is_final_cap_exec_contract(
    state: CSpaceState,
    slot: SlotId,
    ret: bool,
) -> bool {
    spec_is_final_cap_post(state, slot, ret)
}

pub open spec fn same_object_as_exec_contract(
    raw_cap1: &cap,
    raw_cap2: &cap,
    ret: bool,
) -> bool {
    ret == spec_same_object_as_caps(trusted_view_cap(raw_cap1), trusted_view_cap(raw_cap2))
}

pub open spec fn same_region_as_exec_contract(
    raw_cap1: &cap,
    raw_cap2: &cap,
    ret: bool,
) -> bool {
    ret == spec_same_region_as_caps(trusted_view_cap(raw_cap1), trusted_view_cap(raw_cap2))
}

pub open spec fn is_cap_revocable_exec_contract(
    raw_derived_cap: &cap,
    raw_src_cap: &cap,
    ret: bool,
) -> bool {
    ret == spec_is_cap_revocable(trusted_view_cap(raw_derived_cap), trusted_view_cap(raw_src_cap))
}

#[verifier::external_body]
fn trusted_range_top_u128_if_small(base: usize, bits: u64) -> (ret: u128)
    ensures
        bits < 64 ==> ret as int == base as int + cspace_spec_pow2(bits as nat) - 1,
        !(bits < 64) ==> ret == 0u128,
{
    if bits < 64 {
        base as u128 + ((1u128 << bits) - 1u128)
    } else {
        0u128
    }
}

proof fn lemma_supported_cap_tag_kind_equivalences(tag: u64)
    requires
        spec_supported_cap_tag(tag),
    ensures
        (tag == 0u64) == (spec_cap_kind_from_tag(tag) == CapKind::NullCap),
        (tag == 2u64) == (spec_cap_kind_from_tag(tag) == CapKind::UntypedCap),
        (tag == 4u64) == (spec_cap_kind_from_tag(tag) == CapKind::EndpointCap),
        (tag == 6u64) == (spec_cap_kind_from_tag(tag) == CapKind::NotificationCap),
        (tag == 8u64) == (spec_cap_kind_from_tag(tag) == CapKind::ReplyCap),
        (tag == 10u64) == (spec_cap_kind_from_tag(tag) == CapKind::CNodeCap),
        (tag == 12u64) == (spec_cap_kind_from_tag(tag) == CapKind::ThreadCap),
        (tag == 14u64 || tag == 11u64 || tag == 20u64)
            == (spec_cap_kind_from_tag(tag) == CapKind::IRQControlCap),
        (tag == 16u64) == (spec_cap_kind_from_tag(tag) == CapKind::IRQHandlerCap),
        (tag == 18u64) == (spec_cap_kind_from_tag(tag) == CapKind::ZombieCap),
        (tag == 1u64 || tag == 3u64 || tag == 13u64)
            == (spec_cap_kind_from_tag(tag) == CapKind::ArchCap),
{
    if tag == 0u64 {
        assert(spec_cap_kind_from_tag(0u64) == CapKind::NullCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::NullCap);
    } else if tag == 2u64 {
        assert(spec_cap_kind_from_tag(2u64) == CapKind::UntypedCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::UntypedCap);
    } else if tag == 4u64 {
        assert(spec_cap_kind_from_tag(4u64) == CapKind::EndpointCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::EndpointCap);
    } else if tag == 6u64 {
        assert(spec_cap_kind_from_tag(6u64) == CapKind::NotificationCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::NotificationCap);
    } else if tag == 8u64 {
        assert(spec_cap_kind_from_tag(8u64) == CapKind::ReplyCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::ReplyCap);
    } else if tag == 10u64 {
        assert(spec_cap_kind_from_tag(10u64) == CapKind::CNodeCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::CNodeCap);
    } else if tag == 12u64 {
        assert(spec_cap_kind_from_tag(12u64) == CapKind::ThreadCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::ThreadCap);
    } else if tag == 14u64 || tag == 11u64 || tag == 20u64 {
        if tag == 14u64 {
            assert(spec_cap_kind_from_tag(14u64) == CapKind::IRQControlCap) by (compute_only);
        } else if tag == 11u64 {
            assert(spec_cap_kind_from_tag(11u64) == CapKind::IRQControlCap) by (compute_only);
        } else {
            assert(tag == 20u64);
            assert(spec_cap_kind_from_tag(20u64) == CapKind::IRQControlCap) by (compute_only);
        }
        assert(spec_cap_kind_from_tag(tag) == CapKind::IRQControlCap);
    } else if tag == 16u64 {
        assert(spec_cap_kind_from_tag(16u64) == CapKind::IRQHandlerCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::IRQHandlerCap);
    } else if tag == 18u64 {
        assert(spec_cap_kind_from_tag(18u64) == CapKind::ZombieCap) by (compute_only);
        assert(spec_cap_kind_from_tag(tag) == CapKind::ZombieCap);
    } else {
        assert(tag == 1u64 || tag == 3u64 || tag == 13u64);
        if tag == 1u64 {
            assert(spec_cap_kind_from_tag(1u64) == CapKind::ArchCap) by (compute_only);
        } else if tag == 3u64 {
            assert(spec_cap_kind_from_tag(3u64) == CapKind::ArchCap) by (compute_only);
        } else {
            assert(tag == 13u64);
            assert(spec_cap_kind_from_tag(13u64) == CapKind::ArchCap) by (compute_only);
        }
        assert(spec_cap_kind_from_tag(tag) == CapKind::ArchCap);
    }
}

fn cap_tag_is_null(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::NullCap),
{
    let ret = tag == 0u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_untyped(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::UntypedCap),
{
    let ret = tag == 2u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_endpoint(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::EndpointCap),
{
    let ret = tag == 4u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_notification(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::NotificationCap),
{
    let ret = tag == 6u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_reply(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::ReplyCap),
{
    let ret = tag == 8u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_cnode(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::CNodeCap),
{
    let ret = tag == 10u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_thread(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::ThreadCap),
{
    let ret = tag == 12u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_irq_control(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::IRQControlCap),
{
    let ret = tag == 14u64 || tag == 11u64 || tag == 20u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_irq_handler(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::IRQHandlerCap),
{
    let ret = tag == 16u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_zombie(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::ZombieCap),
{
    let ret = tag == 18u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

fn cap_tag_is_arch(tag: u64) -> (ret: bool)
    requires
        spec_supported_cap_tag(tag),
    ensures
        ret == (spec_cap_kind_from_tag(tag) == CapKind::ArchCap),
{
    let ret = tag == 1u64 || tag == 3u64 || tag == 13u64;
    proof {
        lemma_supported_cap_tag_kind_equivalences(tag);
    }
    ret
}

proof fn lemma_bridge_cap_object_shape_for_kind(
    bridged_cap: CapBridge,
    kind: CapKind,
    object_kind: ObjectKind,
)
    requires
        bridged_cap.view().kind == kind,
        spec_cap_has_object(kind),
        spec_object_kind_from_cap_kind(kind) == object_kind,
    ensures
        bridged_cap.view().object == if bridged_cap.snapshot.object_present {
            Some(ObjectRef {
                id: bridged_cap.snapshot.object_addr as int,
                kind: object_kind,
            })
        } else {
            None
        },
{
    let snapshot = bridged_cap.snapshot;
    assert(bridged_cap.view() == view_cap(snapshot));
    assert(view_cap(snapshot).kind == spec_cap_kind_from_tag(snapshot.tag));
    assert(spec_cap_kind_from_tag(snapshot.tag) == kind);
    assert(bridged_cap.view().object == spec_cap_object(snapshot, spec_cap_kind_from_tag(snapshot.tag)));
    assert(bridged_cap.view().object == spec_cap_object(snapshot, kind));
    assert(
        spec_cap_object(snapshot, kind) == if spec_cap_has_object(kind) && snapshot.object_present {
            Some(ObjectRef {
                id: snapshot.object_addr as int,
                kind: spec_object_kind_from_cap_kind(kind),
            })
        } else {
            None
        }
    ) by (compute_only);
    assert(
        spec_cap_object(snapshot, kind) == if snapshot.object_present {
            Some(ObjectRef {
                id: snapshot.object_addr as int,
                kind: spec_object_kind_from_cap_kind(kind),
            })
        } else {
            None
        }
    );
    assert(
        bridged_cap.view().object == if snapshot.object_present {
            Some(ObjectRef {
                id: snapshot.object_addr as int,
                kind: object_kind,
            })
        } else {
            None
        }
    );
}

proof fn lemma_bridge_caps_same_object_ref_for_kind(
    lhs: CapBridge,
    rhs: CapBridge,
    kind: CapKind,
    object_kind: ObjectKind,
)
    requires
        lhs.view().kind == kind,
        rhs.view().kind == kind,
        spec_cap_has_object(kind),
        spec_object_kind_from_cap_kind(kind) == object_kind,
    ensures
        spec_same_object_ref(lhs.view(), rhs.view()) == (
            lhs.snapshot.object_present
                && rhs.snapshot.object_present
                && lhs.snapshot.object_addr as int == rhs.snapshot.object_addr as int
        ),
{
    lemma_bridge_cap_object_shape_for_kind(lhs, kind, object_kind);
    lemma_bridge_cap_object_shape_for_kind(rhs, kind, object_kind);

    if lhs.snapshot.object_present && rhs.snapshot.object_present {
        assert(
            lhs.view().object == Some(ObjectRef {
                id: lhs.snapshot.object_addr as int,
                kind: object_kind,
            })
        );
        assert(
            rhs.view().object == Some(ObjectRef {
                id: rhs.snapshot.object_addr as int,
                kind: object_kind,
            })
        );
    } else if !lhs.snapshot.object_present {
        assert(lhs.view().object is None);
    } else {
        assert(rhs.view().object is None);
    }

    assert(
        spec_same_object_ref(lhs.view(), rhs.view()) == (
            lhs.snapshot.object_present
                && rhs.snapshot.object_present
                && lhs.snapshot.object_addr as int == rhs.snapshot.object_addr as int
        )
    );
}

proof fn lemma_bridge_cnode_data_shape(bridged_cap: CapBridge)
    requires
        bridged_cap.view().kind == CapKind::CNodeCap,
    ensures
        bridged_cap.view().cnode == if bridged_cap.snapshot.cnode_present {
            Some(CNodeCapDataSpec {
                radix_bits: bridged_cap.snapshot.cnode_radix as int,
                guard: bridged_cap.snapshot.cnode_guard as int,
                guard_size: bridged_cap.snapshot.cnode_guard_size as int,
            })
        } else {
            None
        },
{
    let snapshot = bridged_cap.snapshot;
    assert(bridged_cap.view() == view_cap(snapshot));
    assert(view_cap(snapshot).kind == spec_cap_kind_from_tag(snapshot.tag));
    assert(spec_cap_kind_from_tag(snapshot.tag) == CapKind::CNodeCap);
    assert(
        bridged_cap.view().cnode == if snapshot.cnode_present {
            Some(CNodeCapDataSpec {
                radix_bits: snapshot.cnode_radix as int,
                guard: snapshot.cnode_guard as int,
                guard_size: snapshot.cnode_guard_size as int,
            })
        } else {
            None
        }
    );
}

proof fn lemma_bridge_untyped_data_shape(bridged_cap: CapBridge)
    requires
        bridged_cap.view().kind == CapKind::UntypedCap,
    ensures
        bridged_cap.view().untyped == if bridged_cap.snapshot.untyped_present {
            Some(UntypedCapDataSpec {
                block_size_bits: bridged_cap.snapshot.untyped_block_size as int,
                free_index: bridged_cap.snapshot.untyped_free_index as int,
                is_device: bridged_cap.snapshot.untyped_is_device,
            })
        } else {
            None
        },
{
    let snapshot = bridged_cap.snapshot;
    assert(bridged_cap.view() == view_cap(snapshot));
    assert(view_cap(snapshot).kind == spec_cap_kind_from_tag(snapshot.tag));
    assert(spec_cap_kind_from_tag(snapshot.tag) == CapKind::UntypedCap);
    assert(
        bridged_cap.view().untyped == if snapshot.untyped_present {
            Some(UntypedCapDataSpec {
                block_size_bits: snapshot.untyped_block_size as int,
                free_index: snapshot.untyped_free_index as int,
                is_device: snapshot.untyped_is_device,
            })
        } else {
            None
        }
    );
}

pub open spec fn is_long_running_delete_exec_contract(
    state: CSpaceState,
    slot: SlotId,
    ret: bool,
) -> bool {
    spec_is_long_running_delete_post(state, slot, ret)
}

pub open spec fn ensure_no_children_exec_contract(
    state: CSpaceState,
    slot: SlotId,
    ret: exception_t,
) -> bool {
    &&& spec_ensure_no_children_expected_error(state, slot)
        ==> trusted_exception_is_syscall_error(ret)
    &&& !spec_ensure_no_children_expected_error(state, slot)
        ==> trusted_exception_is_none(ret)
}

pub assume_specification[cte_t::ensure_no_children](me: &cte_t) -> (ret: exception_t)
    ensures
        forall|heap: ConcreteHeapId, state: CSpaceState, slot: SlotId| #![auto]
            is_final_cap_call_pre_at(heap, state, slot, me)
                ==> ensure_no_children_exec_contract(state, slot, ret),
;

pub assume_specification[cte_t::is_final_cap](me: &cte_t) -> (ret: bool)
    ensures
        forall|heap: ConcreteHeapId, state: CSpaceState, slot: SlotId| #![auto]
            is_final_cap_call_pre_at(heap, state, slot, me)
                ==> is_final_cap_exec_contract(state, slot, ret),
;

pub assume_specification[resolve_address_bits](
    node_cap: &cap,
    cap_ptr: usize,
    bits: usize,
) -> (ret: resolveAddressBits_ret_t)
    ensures
        forall|state: CSpaceState| #![auto]
            resolve_address_bits_bridge_pre(state, node_cap, cap_ptr, bits)
                ==> resolve_address_bits_one_step_refines_state(
                    state,
                    node_cap,
                    cap_ptr,
                    bits,
                    trusted_view_resolve_address_bits_ret(&ret),
                ),
;

pub assume_specification[cte_insert](
    new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
)
    ensures
        forall|old_heap: ConcreteHeapId,
               old_state: CSpaceState,
               new_heap: ConcreteHeapId,
               new_state: CSpaceState,
               src: SlotId,
               dest: SlotId,
               new_cap_is_revocable: bool| #![auto]
            old_state.has_slot(src)
                && old_state.has_slot(dest)
                && new_state.has_slot(src)
                && new_state.has_slot(dest)
                && cte_insert_call_pre_at(
                    old_heap,
                    old_state,
                    src,
                    dest,
                    new_cap,
                    old(src_slot),
                    old(dest_slot),
                )
                && spec_cte_insert_post(
                    old_state,
                    new_state,
                    src,
                    dest,
                    trusted_view_cap(new_cap),
                    new_cap_is_revocable,
                )
                ==> cte_insert_local_heap_transition_at(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    src,
                    dest,
                ),
;

pub assume_specification[insert_new_cap](
    parent: &mut cte_t,
    slot: &mut cte_t,
    capability: &cap,
)
    ensures
        forall|old_heap: ConcreteHeapId,
               old_state: CSpaceState,
               new_heap: ConcreteHeapId,
               new_state: CSpaceState,
               parent_id: SlotId,
               slot_id: SlotId| #![auto]
            old_state.has_slot(parent_id)
                && old_state.has_slot(slot_id)
                && new_state.has_slot(parent_id)
                && new_state.has_slot(slot_id)
                && insert_new_cap_call_pre_at(
                    old_heap,
                    old_state,
                    parent_id,
                    slot_id,
                    capability,
                    old(parent),
                    old(slot),
                )
                && spec_insert_new_cap_post(
                    old_state,
                    new_state,
                    parent_id,
                    slot_id,
                    trusted_view_cap(capability),
                )
                ==> insert_new_cap_local_heap_transition_at(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    parent_id,
                    slot_id,
                ),
;

pub assume_specification[cte_move](
    new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
)
    ensures
        forall|old_heap: ConcreteHeapId,
               old_state: CSpaceState,
               new_heap: ConcreteHeapId,
               new_state: CSpaceState,
               src: SlotId,
               dest: SlotId| #![auto]
            old_state.has_slot(src)
                && old_state.has_slot(dest)
                && new_state.has_slot(src)
                && new_state.has_slot(dest)
                && cte_move_call_pre_at(
                    old_heap,
                    old_state,
                    src,
                    dest,
                    new_cap,
                    old(src_slot),
                    old(dest_slot),
                )
                && spec_cte_move_post(
                    old_state,
                    new_state,
                    src,
                    dest,
                    trusted_view_cap(new_cap),
                )
                ==> cte_move_local_heap_transition_at(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    src,
                    dest,
                ),
;

pub assume_specification[cte_swap](
    cap1: &cap,
    slot1: &mut cte_t,
    cap2: &cap,
    slot2: &mut cte_t,
)
    ensures
        forall|old_heap: ConcreteHeapId,
               old_state: CSpaceState,
               new_heap: ConcreteHeapId,
               new_state: CSpaceState,
               slot1_id: SlotId,
               slot2_id: SlotId| #![auto]
            old_state.has_slot(slot1_id)
                && old_state.has_slot(slot2_id)
                && new_state.has_slot(slot1_id)
                && new_state.has_slot(slot2_id)
                && cte_swap_call_pre_at(
                    old_heap,
                    old_state,
                    slot1_id,
                    slot2_id,
                    cap1,
                    cap2,
                    old(slot1),
                    old(slot2),
                )
                && spec_cte_swap_post(
                    old_state,
                    new_state,
                    slot1_id,
                    slot2_id,
                    trusted_view_cap(cap1),
                    trusted_view_cap(cap2),
                )
                ==> cte_swap_local_heap_transition_at(
                    old_heap,
                    old_state,
                    new_heap,
                    new_state,
                    slot1_id,
                    slot2_id,
                ),
;

fn cte_insert_exec_step(
    raw_new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(src): Ghost<SlotId>,
    Ghost(dest): Ghost<SlotId>,
    Ghost(new_cap_is_revocable): Ghost<bool>,
)
    requires
        old_state.has_slot(src),
        old_state.has_slot(dest),
        new_state.has_slot(src),
        new_state.has_slot(dest),
        cte_insert_call_pre_at(
            old_heap,
            old_state,
            src,
            dest,
            raw_new_cap,
            old(src_slot),
            old(dest_slot),
        ),
        spec_cte_insert_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        ),
    ensures
        cte_insert_exec_contract(
            old_state,
            new_heap,
            new_state,
            src,
            dest,
            raw_new_cap,
            new_cap_is_revocable,
        ),
{
    crate::cte::cte_insert(raw_new_cap, src_slot, dest_slot);
    proof {
        let changed = spec_cte_insert_changed_slots(old_state, src, dest);
        assert(cte_insert_local_heap_transition_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            src,
            dest,
        ));
        assert(spec_cte_insert_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
        assert(spec_cte_insert_frame(old_state, new_state, src, dest));
        assert(slots_unchanged_except(old_state, new_state, changed));
        assert(new_state.cnode_lookup =~= old_state.cnode_lookup);
        lemma_trusted_cspace_local_heap_transition_at_implies_post_heap_matches_state_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            changed,
        );
        lemma_cte_insert_post_implies_expected_src_dest_entries(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        );
        lemma_cte_insert_local_heap_transition_post_implies_expected_src_dest_views(
            old_heap,
            old_state,
            new_heap,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        );
        lemma_cte_insert_pre_post_implies_contract(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        );
    }
    assert(cte_insert_exec_contract(
        old_state,
        new_heap,
        new_state,
        src,
        dest,
        raw_new_cap,
        new_cap_is_revocable,
    ));
}

fn is_final_cap_exec_step(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_final_cap_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_final_cap_exec_contract(state, slot, ret),
{
    let ret = is_final_cap_via_same_object_as_refined(
        raw_slot,
        Ghost(heap),
        Ghost(state),
        Ghost(slot),
    );
    assert(is_final_cap_exec_contract(state, slot, ret));
    ret
}

fn is_long_running_delete_exec_step(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_long_running_delete_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_long_running_delete_exec_contract(state, slot, ret),
{
    let ret = is_long_running_delete_via_is_final_cap_refined(
        raw_slot,
        Ghost(heap),
        Ghost(state),
        Ghost(slot),
    );
    assert(is_long_running_delete_exec_contract(state, slot, ret));
    ret
}

fn ensure_no_children_exec_step(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: exception_t)
    requires
        spec_ensure_no_children_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        ensure_no_children_exec_contract(state, slot, ret),
{
    let ret = ensure_no_children_via_is_mdb_parent_of_refined(
        raw_slot,
        Ghost(heap),
        Ghost(state),
        Ghost(slot),
    );
    assert(ensure_no_children_exec_contract(state, slot, ret));
    ret
}

fn derive_cap_exec_step(
    raw_slot: &cte_t,
    raw_capability: &cap,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: deriveCap_ret)
    requires
        derive_cap_call_pre_at(heap, state, slot, raw_slot, raw_capability),
    ensures
        derive_cap_exec_contract(state, slot, raw_capability, &ret),
{
    let ret = derive_cap_via_ensure_no_children_refined(
        raw_slot,
        raw_capability,
        Ghost(heap),
        Ghost(state),
        Ghost(slot),
    );
    assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
    ret
}

fn is_mdb_parent_of_exec_step(
    raw_parent: &cte_t,
    raw_child: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(parent): Ghost<SlotId>,
    Ghost(child): Ghost<SlotId>,
) -> (ret: bool)
    requires
        is_mdb_parent_of_call_pre_at(heap, state, parent, child, raw_parent, raw_child),
    ensures
        is_mdb_parent_of_exec_contract(state, parent, child, ret),
{
    let ret = is_mdb_parent_of_via_same_region_as_refined(
        raw_parent,
        raw_child,
        Ghost(heap),
        Ghost(state),
        Ghost(parent),
        Ghost(child),
    );
    assert(is_mdb_parent_of_exec_contract(state, parent, child, ret));
    ret
}

fn insert_new_cap_exec_step(
    parent_slot: &mut cte_t,
    slot_ref: &mut cte_t,
    raw_new_cap: &cap,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(parent): Ghost<SlotId>,
    Ghost(slot): Ghost<SlotId>,
)
    requires
        old_state.has_slot(parent),
        old_state.has_slot(slot),
        new_state.has_slot(parent),
        new_state.has_slot(slot),
        insert_new_cap_call_pre_at(
            old_heap,
            old_state,
            parent,
            slot,
            raw_new_cap,
            old(parent_slot),
            old(slot_ref),
        ),
        spec_insert_new_cap_post(
            old_state,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        ),
    ensures
        insert_new_cap_exec_contract(
            old_state,
            new_heap,
            new_state,
            parent,
            slot,
            raw_new_cap,
        ),
{
    crate::cte::insert_new_cap(parent_slot, slot_ref, raw_new_cap);
    proof {
        let changed = spec_cte_insert_changed_slots(old_state, parent, slot);
        assert(insert_new_cap_local_heap_transition_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            parent,
            slot,
        ));
        assert(spec_insert_new_cap_pre(old_state, parent, slot, trusted_view_cap(raw_new_cap)));
        assert(spec_insert_new_cap_frame(old_state, new_state, parent, slot));
        assert(slots_unchanged_except(old_state, new_state, changed));
        assert(new_state.cnode_lookup =~= old_state.cnode_lookup);
        lemma_trusted_cspace_local_heap_transition_at_implies_post_heap_matches_state_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            changed,
        );
        lemma_insert_new_cap_post_implies_expected_parent_slot_entries(
            old_state,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        );
        lemma_insert_new_cap_local_heap_transition_post_implies_expected_parent_slot_views(
            old_heap,
            old_state,
            new_heap,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        );
        lemma_insert_new_cap_pre_post_implies_contract(
            old_state,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        );
    }
    assert(insert_new_cap_exec_contract(
        old_state,
        new_heap,
        new_state,
        parent,
        slot,
        raw_new_cap,
    ));
}

fn cte_move_exec_step(
    raw_new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(src): Ghost<SlotId>,
    Ghost(dest): Ghost<SlotId>,
)
    requires
        old_state.has_slot(src),
        old_state.has_slot(dest),
        new_state.has_slot(src),
        new_state.has_slot(dest),
        cte_move_call_pre_at(
            old_heap,
            old_state,
            src,
            dest,
            raw_new_cap,
            old(src_slot),
            old(dest_slot),
        ),
        spec_cte_move_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        ),
    ensures
        cte_move_exec_contract(
            old_state,
            new_heap,
            new_state,
            src,
            dest,
            raw_new_cap,
        ),
{
    crate::cte::cte_move(raw_new_cap, src_slot, dest_slot);
    proof {
        let changed = spec_cte_move_changed_slots(old_state, src, dest);
        assert(cte_move_local_heap_transition_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            src,
            dest,
        ));
        assert(spec_cte_move_pre(old_state, src, dest, trusted_view_cap(raw_new_cap)));
        assert(spec_cte_move_frame(old_state, new_state, src, dest));
        assert(slots_unchanged_except(old_state, new_state, changed));
        assert(new_state.cnode_lookup =~= old_state.cnode_lookup);
        lemma_trusted_cspace_local_heap_transition_at_implies_post_heap_matches_state_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            changed,
        );
        lemma_cte_move_post_implies_expected_src_dest_entries(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        );
        lemma_cte_move_local_heap_transition_post_implies_expected_src_dest_views(
            old_heap,
            old_state,
            new_heap,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        );
        lemma_cte_move_pre_post_implies_contract(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        );
    }
    assert(cte_move_exec_contract(
        old_state,
        new_heap,
        new_state,
        src,
        dest,
        raw_new_cap,
    ));
}

fn cte_swap_exec_step(
    raw_cap1: &cap,
    slot1: &mut cte_t,
    raw_cap2: &cap,
    slot2: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(slot1_id): Ghost<SlotId>,
    Ghost(slot2_id): Ghost<SlotId>,
)
    requires
        old_state.has_slot(slot1_id),
        old_state.has_slot(slot2_id),
        new_state.has_slot(slot1_id),
        new_state.has_slot(slot2_id),
        cte_swap_call_pre_at(
            old_heap,
            old_state,
            slot1_id,
            slot2_id,
            raw_cap1,
            raw_cap2,
            old(slot1),
            old(slot2),
        ),
        spec_cte_swap_post(
            old_state,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        ),
    ensures
        cte_swap_exec_contract(
            old_state,
            new_heap,
            new_state,
            slot1_id,
            slot2_id,
            raw_cap1,
            raw_cap2,
        ),
{
    crate::cte::cte_swap(raw_cap1, slot1, raw_cap2, slot2);
    proof {
        let changed = spec_cte_swap_changed_slots(old_state, slot1_id, slot2_id);
        assert(cte_swap_local_heap_transition_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            slot1_id,
            slot2_id,
        ));
        assert(spec_cte_swap_pre(
            old_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        ));
        assert(spec_cte_swap_frame(old_state, new_state, slot1_id, slot2_id));
        assert(slots_unchanged_except(old_state, new_state, changed));
        assert(new_state.cnode_lookup =~= old_state.cnode_lookup);
        lemma_trusted_cspace_local_heap_transition_at_implies_post_heap_matches_state_at(
            old_heap,
            old_state,
            new_heap,
            new_state,
            changed,
        );
        lemma_cte_swap_post_implies_expected_slot_entries(
            old_state,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        );
        lemma_cte_swap_local_heap_transition_post_implies_expected_slot_views(
            old_heap,
            old_state,
            new_heap,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        );
        lemma_cte_swap_pre_post_implies_contract(
            old_state,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        );
    }
    assert(cte_swap_exec_contract(
        old_state,
        new_heap,
        new_state,
        slot1_id,
        slot2_id,
        raw_cap1,
        raw_cap2,
    ));
}

fn resolve_address_bits_exec_step(
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    Ghost(state): Ghost<CSpaceState>,
) -> (ret: ResolveAddressBitsRetBridge)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
    ensures
        resolve_address_bits_exec_contract(state, raw_root, cap_ptr, bits, ret),
{
    let raw_ret = crate::cte::resolve_address_bits(raw_root, cap_ptr, bits);
    let ret = bridge_resolve_address_bits_ret(&raw_ret);
    assert(ret.view() == trusted_view_resolve_address_bits_ret(&raw_ret));
    proof {
        assert(resolve_address_bits_one_step_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ret.view(),
        ));
        lemma_resolve_address_bits_one_step_refines_state_implies_core_refines_state(
            state,
            raw_root,
            cap_ptr,
            bits,
            ret.view(),
        );
        lemma_resolve_address_bits_core_refines_state_implies_expected_core(
            state,
            raw_root,
            cap_ptr,
            bits,
            ret.view(),
        );
    }
    assert(ret.view() == resolve_address_bits_expected_core(state, raw_root, cap_ptr, bits));
    ret
}

fn cte_insert_refined_with_revocable(
    raw_new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(src): Ghost<SlotId>,
    Ghost(dest): Ghost<SlotId>,
    Ghost(new_cap_is_revocable): Ghost<bool>,
)
    requires
        old_state.has_slot(src),
        old_state.has_slot(dest),
        new_state.has_slot(src),
        new_state.has_slot(dest),
        cte_insert_call_pre_at(old_heap, old_state, src, dest, raw_new_cap, old(src_slot), old(dest_slot)),
        spec_cte_insert_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        ),
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
        spec_cte_insert(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        ),
        new_state.slot_entry(src)
            == spec_cte_insert_expected_src_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
            ),
        new_state.slot_entry(dest)
            == spec_cte_insert_expected_dest_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
                new_cap_is_revocable,
            ),
        trusted_concrete_slot_view_at(new_heap, src)
            == spec_cte_insert_expected_src_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
            ),
        trusted_concrete_slot_view_at(new_heap, dest)
            == spec_cte_insert_expected_dest_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
                new_cap_is_revocable,
            ),
{
    cte_insert_exec_step(
        raw_new_cap,
        src_slot,
        dest_slot,
        Ghost(old_heap),
        Ghost(old_state),
        Ghost(new_heap),
        Ghost(new_state),
        Ghost(src),
        Ghost(dest),
        Ghost(new_cap_is_revocable),
    );
    assert(cte_insert_exec_contract(
        old_state,
        new_heap,
        new_state,
        src,
        dest,
        raw_new_cap,
        new_cap_is_revocable,
    ));
    assert(trusted_cspace_heap_matches_state_at(new_heap, new_state));
    assert(spec_cte_insert(
        old_state,
        new_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
        new_cap_is_revocable,
    ));
    assert(new_state.slot_entry(src) == spec_cte_insert_expected_src_entry(
        old_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
    ));
    assert(new_state.slot_entry(dest) == spec_cte_insert_expected_dest_entry(
        old_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
        new_cap_is_revocable,
    ));
    assert(trusted_concrete_slot_view_at(new_heap, src) == spec_cte_insert_expected_src_entry(
        old_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
    ));
    assert(trusted_concrete_slot_view_at(new_heap, dest) == spec_cte_insert_expected_dest_entry(
        old_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
        new_cap_is_revocable,
    ));
}

pub fn cte_insert_refined(
    raw_new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(src): Ghost<SlotId>,
    Ghost(dest): Ghost<SlotId>,
)
    requires
        old_state.has_slot(src),
        old_state.has_slot(dest),
        new_state.has_slot(src),
        new_state.has_slot(dest),
        cte_insert_call_pre_at(old_heap, old_state, src, dest, raw_new_cap, old(src_slot), old(dest_slot)),
        spec_cte_insert_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            spec_cte_insert_expected_revocable(old_state, src, trusted_view_cap(raw_new_cap)),
        ),
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
        spec_cte_insert(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            spec_cte_insert_expected_revocable(old_state, src, trusted_view_cap(raw_new_cap)),
        ),
        new_state.slot_entry(src)
            == spec_cte_insert_expected_src_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
            ),
        new_state.slot_entry(dest)
            == spec_cte_insert_expected_dest_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
                spec_cte_insert_expected_revocable(old_state, src, trusted_view_cap(raw_new_cap)),
            ),
        trusted_concrete_slot_view_at(new_heap, src)
            == spec_cte_insert_expected_src_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
            ),
        trusted_concrete_slot_view_at(new_heap, dest)
            == spec_cte_insert_expected_dest_entry(
                old_state,
                src,
                dest,
                trusted_view_cap(raw_new_cap),
                spec_cte_insert_expected_revocable(old_state, src, trusted_view_cap(raw_new_cap)),
            ),
{
    proof {
        lemma_cte_insert_call_pre_at_implies_raw_slot_views_match_state(
            old_heap,
            old_state,
            src,
            dest,
            raw_new_cap,
            old(src_slot),
            old(dest_slot),
        );
    }

    let raw_src_cap = trusted_cap_ref_from_slot(src_slot);
    let new_cap_is_revocable = is_cap_revocable(raw_new_cap, raw_src_cap);

    proof {
        assert(trusted_view_cap(raw_src_cap) == trusted_view_cte(old(src_slot)).cap);
        assert(trusted_view_cte(old(src_slot)).cap == old_state.slot_cap(src));
        assert(is_cap_revocable_exec_contract(raw_new_cap, raw_src_cap, new_cap_is_revocable));
        assert(
            new_cap_is_revocable
                == spec_is_cap_revocable(trusted_view_cap(raw_new_cap), trusted_view_cap(raw_src_cap))
        );
        assert(
            new_cap_is_revocable
                == spec_is_cap_revocable(trusted_view_cap(raw_new_cap), old_state.slot_cap(src))
        );
        assert(
            new_cap_is_revocable
                == spec_cte_insert_expected_revocable(old_state, src, trusted_view_cap(raw_new_cap))
        );
        assert(spec_cte_insert_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
            new_cap_is_revocable,
        ));
    }

    cte_insert_refined_with_revocable(
        raw_new_cap,
        src_slot,
        dest_slot,
        Ghost(old_heap),
        Ghost(old_state),
        Ghost(new_heap),
        Ghost(new_state),
        Ghost(src),
        Ghost(dest),
        Ghost(new_cap_is_revocable),
    );
}

pub fn is_final_cap_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_final_cap_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_final_cap_exec_contract(state, slot, ret),
{
    let ret = is_final_cap_exec_step(raw_slot, Ghost(heap), Ghost(state), Ghost(slot));
    assert(is_final_cap_exec_contract(state, slot, ret));
    ret
}

fn is_final_cap_via_same_object_as_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_final_cap_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_final_cap_exec_contract(state, slot, ret),
{
    proof {
        lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
            heap,
            state,
            slot,
            raw_slot,
        );
    }

    let slot_cte = bridge_cte(raw_slot);
    let slot_cap = CapBridge { snapshot: slot_cte.snapshot.cap };
    let has_prev = slot_cte.snapshot.mdb_prev_addr != 0usize;
    let prev_same = if has_prev {
        proof {
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_prev is Some);
            assert(trusted_view_cte(raw_slot).mdb_prev is Some);
            assert(state.slot_entry(slot).mdb_prev is Some);
            assert(state.has_slot(state.slot_entry(slot).mdb_prev.unwrap()));
        }
        let raw_prev = trusted_slot_ref_from_addr(slot_cte.snapshot.mdb_prev_addr);
        let raw_prev_cap = trusted_cap_ref_from_slot(raw_prev);
        let raw_slot_cap = trusted_cap_ref_from_slot(raw_slot);
        let prev_cte = bridge_cte(raw_prev);
        let prev_cap = CapBridge { snapshot: prev_cte.snapshot.cap };
        let prev_same = same_object_as(raw_prev_cap, raw_slot_cap);
        proof {
            assert(state.slot_entry(slot).mdb_prev.unwrap() == spec_slot_id_from_addr(slot_cte.snapshot.mdb_prev_addr));
            assert(trusted_slot_ref_is_id(raw_prev, state.slot_entry(slot).mdb_prev.unwrap()));
            assert(is_final_cap_call_pre_at(
                heap,
                state,
                state.slot_entry(slot).mdb_prev.unwrap(),
                raw_prev,
            ));
            lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
                heap,
                state,
                state.slot_entry(slot).mdb_prev.unwrap(),
                raw_prev,
            );
            assert(prev_cte.view() == trusted_view_cte(raw_prev));
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(prev_cap.view() == state.slot_cap(
                state.slot_entry(slot).mdb_prev.unwrap(),
            ));
            assert(slot_cap.view() == state.slot_cap(slot));
            assert(trusted_view_cap(raw_prev_cap) == trusted_view_cte(raw_prev).cap);
            assert(trusted_view_cap(raw_slot_cap) == trusted_view_cte(raw_slot).cap);
            assert(same_object_as_exec_contract(raw_prev_cap, raw_slot_cap, prev_same));
            assert(prev_same == state.same_object_as(state.slot_entry(slot).mdb_prev.unwrap(), slot));
        }
        prev_same
    } else {
        proof {
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_prev is None);
            assert(!(trusted_view_cte(raw_slot).mdb_prev is Some));
            assert(trusted_view_cte(raw_slot).mdb_prev is None);
            assert(state.slot_entry(slot).mdb_prev is None);
        }
        false
    };

    let has_next = slot_cte.snapshot.mdb_next_addr != 0usize;
    let next_same = if has_next {
        proof {
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_next is Some);
            assert(trusted_view_cte(raw_slot).mdb_next is Some);
            assert(state.slot_entry(slot).mdb_next is Some);
            assert(state.has_slot(state.slot_entry(slot).mdb_next.unwrap()));
        }
        let raw_next = trusted_slot_ref_from_addr(slot_cte.snapshot.mdb_next_addr);
        let raw_slot_cap = trusted_cap_ref_from_slot(raw_slot);
        let raw_next_cap = trusted_cap_ref_from_slot(raw_next);
        let next_cte = bridge_cte(raw_next);
        let next_cap = CapBridge { snapshot: next_cte.snapshot.cap };
        let next_same = same_object_as(raw_slot_cap, raw_next_cap);
        proof {
            assert(state.slot_entry(slot).mdb_next.unwrap() == spec_slot_id_from_addr(slot_cte.snapshot.mdb_next_addr));
            assert(trusted_slot_ref_is_id(raw_next, state.slot_entry(slot).mdb_next.unwrap()));
            assert(is_final_cap_call_pre_at(
                heap,
                state,
                state.slot_entry(slot).mdb_next.unwrap(),
                raw_next,
            ));
            lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
                heap,
                state,
                state.slot_entry(slot).mdb_next.unwrap(),
                raw_next,
            );
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(next_cte.view() == trusted_view_cte(raw_next));
            assert(slot_cap.view() == state.slot_cap(slot));
            assert(next_cap.view() == state.slot_cap(
                state.slot_entry(slot).mdb_next.unwrap(),
            ));
            assert(trusted_view_cap(raw_slot_cap) == trusted_view_cte(raw_slot).cap);
            assert(trusted_view_cap(raw_next_cap) == trusted_view_cte(raw_next).cap);
            assert(same_object_as_exec_contract(raw_slot_cap, raw_next_cap, next_same));
            assert(next_same == state.same_object_as(slot, state.slot_entry(slot).mdb_next.unwrap()));
        }
        next_same
    } else {
        proof {
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_next is None);
            assert(!(trusted_view_cte(raw_slot).mdb_next is Some));
            assert(trusted_view_cte(raw_slot).mdb_next is None);
            assert(state.slot_entry(slot).mdb_next is None);
        }
        false
    };

    let ret = !prev_same && !next_same;
    proof {
        if has_prev {
            assert(state.slot_entry(slot).mdb_prev is Some);
            assert(prev_same == state.same_object_as(state.slot_entry(slot).mdb_prev.unwrap(), slot));
        } else {
            assert(state.slot_entry(slot).mdb_prev is None);
            assert(!prev_same);
        }
        if has_next {
            assert(state.slot_entry(slot).mdb_next is Some);
            assert(next_same == state.same_object_as(slot, state.slot_entry(slot).mdb_next.unwrap()));
        } else {
            assert(state.slot_entry(slot).mdb_next is None);
            assert(!next_same);
        }
        assert(ret == state.is_final_cap(slot));
    }
    assert(is_final_cap_exec_contract(state, slot, ret));
    ret
}

pub fn is_long_running_delete_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_long_running_delete_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_long_running_delete_exec_contract(state, slot, ret),
{
    let ret = is_long_running_delete_exec_step(raw_slot, Ghost(heap), Ghost(state), Ghost(slot));
    ret
}

pub fn ensure_no_children_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: exception_t)
    requires
        spec_ensure_no_children_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        ensure_no_children_exec_contract(state, slot, ret),
{
    let ret = ensure_no_children_exec_step(raw_slot, Ghost(heap), Ghost(state), Ghost(slot));
    assert(ensure_no_children_exec_contract(state, slot, ret));
    ret
}

fn ensure_no_children_via_is_mdb_parent_of_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: exception_t)
    requires
        spec_ensure_no_children_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        ensure_no_children_exec_contract(state, slot, ret),
        trusted_exception_is_none(ret) == !state.ensure_no_children_blocks(slot),
        trusted_exception_is_syscall_error(ret) == state.ensure_no_children_blocks(slot),
{
    proof {
        lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
            heap,
            state,
            slot,
            raw_slot,
        );
    }
    let slot_cte = bridge_cte(raw_slot);
    let has_next = slot_cte.snapshot.mdb_next_addr != 0usize;
    if has_next {
        proof {
            lemma_mdb_cte_wf_at_implies_valid_slot_entry(state, slot);
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_next is Some);
            assert(trusted_view_cte(raw_slot).mdb_next is Some);
            assert(state.slot_entry(slot).mdb_next is Some);
            assert(state.has_slot(state.slot_entry(slot).mdb_next.unwrap()));
        }
        let raw_child = trusted_slot_ref_from_addr(slot_cte.snapshot.mdb_next_addr);
        proof {
            assert(state.slot_entry(slot).mdb_next.unwrap() == spec_slot_id_from_addr(slot_cte.snapshot.mdb_next_addr));
        }
        assert(trusted_slot_ref_is_id(raw_child, state.slot_entry(slot).mdb_next.unwrap()));
        let is_parent = is_mdb_parent_of_refined(
            raw_slot,
            raw_child,
            Ghost(heap),
            Ghost(state),
            Ghost(slot),
            Ghost(state.slot_entry(slot).mdb_next.unwrap()),
        );
        assert(is_parent == state.mdb_parent_of(slot, state.slot_entry(slot).mdb_next.unwrap()));
        assert(
            state.ensure_no_children_blocks(slot)
                == (state.slot_entry(slot).mdb_next is Some
                    && state.mdb_parent_of(slot, state.slot_entry(slot).mdb_next.unwrap()))
        );
        assert(state.ensure_no_children_blocks(slot) == state.mdb_parent_of(slot, state.slot_entry(slot).mdb_next.unwrap()));
        if is_parent {
            let ret = trusted_make_exception_syscall_error();
            assert(state.ensure_no_children_blocks(slot));
            assert(ensure_no_children_exec_contract(state, slot, ret));
            assert(trusted_exception_is_none(ret) == !state.ensure_no_children_blocks(slot));
            assert(trusted_exception_is_syscall_error(ret) == state.ensure_no_children_blocks(slot));
            ret
        } else {
            let ret = trusted_make_exception_none();
            assert(!state.ensure_no_children_blocks(slot));
            assert(ensure_no_children_exec_contract(state, slot, ret));
            assert(trusted_exception_is_none(ret) == !state.ensure_no_children_blocks(slot));
            assert(trusted_exception_is_syscall_error(ret) == state.ensure_no_children_blocks(slot));
            ret
        }
    } else {
        proof {
            assert(slot_cte.view() == trusted_view_cte(raw_slot));
            assert(slot_cte.view().mdb_next is None);
            assert(trusted_view_cte(raw_slot).mdb_next is None);
            assert(state.slot_entry(slot).mdb_next is None);
        }
        let ret = trusted_make_exception_none();
        assert(!state.ensure_no_children_blocks(slot));
        assert(ensure_no_children_exec_contract(state, slot, ret));
        assert(trusted_exception_is_none(ret) == !state.ensure_no_children_blocks(slot));
        assert(trusted_exception_is_syscall_error(ret) == state.ensure_no_children_blocks(slot));
        ret
    }
}

pub fn derive_cap_refined(
    raw_slot: &cte_t,
    raw_capability: &cap,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: deriveCap_ret)
    requires
        derive_cap_call_pre_at(heap, state, slot, raw_slot, raw_capability),
    ensures
        derive_cap_exec_contract(state, slot, raw_capability, &ret),
{
    let ret = derive_cap_exec_step(
        raw_slot,
        raw_capability,
        Ghost(heap),
        Ghost(state),
        Ghost(slot),
    );
    ret
}

fn derive_cap_via_ensure_no_children_refined(
    raw_slot: &cte_t,
    raw_capability: &cap,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: deriveCap_ret)
    requires
        derive_cap_call_pre_at(heap, state, slot, raw_slot, raw_capability),
    ensures
        derive_cap_exec_contract(state, slot, raw_capability, &ret),
{
    let cap_bridge = bridge_cap(raw_capability);
    let tag = cap_bridge.snapshot.tag;
    let is_zombie = cap_tag_is_zombie(tag);
    let is_untyped = cap_tag_is_untyped(tag);
    let is_reply = cap_tag_is_reply(tag);
    let is_irq_control = cap_tag_is_irq_control(tag);
    if is_zombie {
        let null_cap = trusted_make_null_cap();
        let status = trusted_make_exception_none();
        let ret = trusted_make_derive_cap_ret(status, &null_cap);
        proof {
            assert(cap_bridge.view() == trusted_view_cap(raw_capability));
            assert(is_zombie == (cap_bridge.view().kind == CapKind::ZombieCap));
            assert(trusted_view_cap(raw_capability).kind == CapKind::ZombieCap);
        }
        assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
        ret
    } else if is_untyped {
        let status = ensure_no_children_via_is_mdb_parent_of_refined(
            raw_slot,
            Ghost(heap),
            Ghost(state),
            Ghost(slot),
        );
        let ok = trusted_check_exception_is_none(status);
        let out_cap = if ok {
            trusted_clone_cap(raw_capability)
        } else {
            trusted_make_null_cap()
        };
        let ret = trusted_make_derive_cap_ret(status, &out_cap);
        proof {
            assert(cap_bridge.view() == trusted_view_cap(raw_capability));
            assert(is_untyped == (cap_bridge.view().kind == CapKind::UntypedCap));
            assert(trusted_view_cap(raw_capability).kind == CapKind::UntypedCap);
            assert(
                spec_derive_cap_returns_syscall_error(state, slot, trusted_view_cap(raw_capability))
                    == state.ensure_no_children_blocks(slot)
            );
            assert(ok == !state.ensure_no_children_blocks(slot));
        }
        assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
        ret
    } else {
        #[cfg(not(feature = "kernel_mcs"))]
        if is_reply {
            let null_cap = trusted_make_null_cap();
            let status = trusted_make_exception_none();
            let ret = trusted_make_derive_cap_ret(status, &null_cap);
            proof {
                assert(cap_bridge.view() == trusted_view_cap(raw_capability));
                assert(is_reply == (cap_bridge.view().kind == CapKind::ReplyCap));
            }
            assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
            ret
        } else if is_irq_control {
            let null_cap = trusted_make_null_cap();
            let status = trusted_make_exception_none();
            let ret = trusted_make_derive_cap_ret(status, &null_cap);
            proof {
                assert(cap_bridge.view() == trusted_view_cap(raw_capability));
                assert(is_irq_control == (cap_bridge.view().kind == CapKind::IRQControlCap));
            }
            assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
            ret
        } else {
            let out_cap = trusted_clone_cap(raw_capability);
            let status = trusted_make_exception_none();
            let ret = trusted_make_derive_cap_ret(status, &out_cap);
            assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
            ret
        }

        #[cfg(feature = "kernel_mcs")]
        if is_irq_control {
            let null_cap = trusted_make_null_cap();
            let status = trusted_make_exception_none();
            let ret = trusted_make_derive_cap_ret(status, &null_cap);
            proof {
                assert(cap_bridge.view() == trusted_view_cap(raw_capability));
                assert(is_irq_control == (cap_bridge.view().kind == CapKind::IRQControlCap));
            }
            assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
            ret
        } else {
            let out_cap = trusted_clone_cap(raw_capability);
            let status = trusted_make_exception_none();
            let ret = trusted_make_derive_cap_ret(status, &out_cap);
            assert(derive_cap_exec_contract(state, slot, raw_capability, &ret));
            ret
        }
    }
}

pub fn is_mdb_parent_of_refined(
    raw_parent: &cte_t,
    raw_child: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(parent): Ghost<SlotId>,
    Ghost(child): Ghost<SlotId>,
) -> (ret: bool)
    requires
        is_mdb_parent_of_call_pre_at(heap, state, parent, child, raw_parent, raw_child),
    ensures
        is_mdb_parent_of_exec_contract(state, parent, child, ret),
{
    let ret = is_mdb_parent_of_exec_step(
        raw_parent,
        raw_child,
        Ghost(heap),
        Ghost(state),
        Ghost(parent),
        Ghost(child),
    );
    assert(is_mdb_parent_of_exec_contract(state, parent, child, ret));
    ret
}

fn same_region_as_from_bridges(
    cap1: CapBridge,
    cap2: CapBridge,
) -> (ret: bool)
    requires
        cap1.wf(),
        cap2.wf(),
    ensures
        ret == spec_same_region_as_caps(cap1.view(), cap2.view()),
{
    let lhs_tag = cap1.snapshot.tag;
    let rhs_tag = cap2.snapshot.tag;
    let lhs_is_untyped = cap_tag_is_untyped(lhs_tag);
    let lhs_is_endpoint = cap_tag_is_endpoint(lhs_tag);
    let lhs_is_notification = cap_tag_is_notification(lhs_tag);
    let lhs_is_reply = cap_tag_is_reply(lhs_tag);
    let lhs_is_cnode = cap_tag_is_cnode(lhs_tag);
    let lhs_is_thread = cap_tag_is_thread(lhs_tag);
    let lhs_is_irq_control = cap_tag_is_irq_control(lhs_tag);
    let lhs_is_irq_handler = cap_tag_is_irq_handler(lhs_tag);

    let rhs_is_untyped = cap_tag_is_untyped(rhs_tag);
    let rhs_is_endpoint = cap_tag_is_endpoint(rhs_tag);
    let rhs_is_notification = cap_tag_is_notification(rhs_tag);
    let rhs_is_reply = cap_tag_is_reply(rhs_tag);
    let rhs_is_cnode = cap_tag_is_cnode(rhs_tag);
    let rhs_is_thread = cap_tag_is_thread(rhs_tag);
    let rhs_is_irq_control = cap_tag_is_irq_control(rhs_tag);
    let rhs_is_irq_handler = cap_tag_is_irq_handler(rhs_tag);
    let rhs_is_zombie = cap_tag_is_zombie(rhs_tag);
    let rhs_is_physical =
        rhs_is_untyped
            || rhs_is_endpoint
            || rhs_is_notification
            || rhs_is_cnode
            || rhs_is_thread
            || rhs_is_zombie;
    let rhs_size_bits =
        if rhs_is_untyped {
            cap2.snapshot.untyped_block_size
        } else if rhs_is_endpoint {
            4u64
        } else if rhs_is_notification {
            5u64
        } else if rhs_is_cnode {
            cap2.snapshot.cnode_radix + 5u64
        } else if rhs_is_thread {
            10u64
        } else {
            0u64
        };
    let lhs_top_u128 =
        trusted_range_top_u128_if_small(cap1.snapshot.object_addr, cap1.snapshot.untyped_block_size);
    let rhs_top_u128 = trusted_range_top_u128_if_small(cap2.snapshot.object_addr, rhs_size_bits);
    let untyped_contains =
        cap1.snapshot.object_present
            && cap1.snapshot.untyped_present
            && 4u64 <= cap1.snapshot.untyped_block_size
            && cap1.snapshot.untyped_block_size < 64
            && rhs_is_physical
            && cap2.snapshot.object_present
            && (!rhs_is_untyped || cap2.snapshot.untyped_present)
            && (!rhs_is_cnode || cap2.snapshot.cnode_present)
            && rhs_size_bits < 64
            && cap1.snapshot.object_addr as u128 <= cap2.snapshot.object_addr as u128
            && cap2.snapshot.object_addr as u128 <= rhs_top_u128
            && rhs_top_u128 <= lhs_top_u128;
    let ret = if lhs_is_untyped {
        untyped_contains
    } else if lhs_is_endpoint {
        rhs_is_endpoint
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_notification {
        rhs_is_notification
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_cnode {
        rhs_is_cnode
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
            && cap1.snapshot.cnode_present
            && cap2.snapshot.cnode_present
            && cap1.snapshot.cnode_radix == cap2.snapshot.cnode_radix
    } else if lhs_is_thread {
        rhs_is_thread
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_reply {
        rhs_is_reply
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_irq_control {
        rhs_is_irq_control || rhs_is_irq_handler
    } else if lhs_is_irq_handler {
        rhs_is_irq_handler
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else {
        false
    };

    proof {
        assert(lhs_is_untyped == (cap1.view().kind == CapKind::UntypedCap));
        assert(lhs_is_endpoint == (cap1.view().kind == CapKind::EndpointCap));
        assert(lhs_is_notification == (cap1.view().kind == CapKind::NotificationCap));
        assert(lhs_is_reply == (cap1.view().kind == CapKind::ReplyCap));
        assert(lhs_is_cnode == (cap1.view().kind == CapKind::CNodeCap));
        assert(lhs_is_thread == (cap1.view().kind == CapKind::ThreadCap));
        assert(lhs_is_irq_control == (cap1.view().kind == CapKind::IRQControlCap));
        assert(lhs_is_irq_handler == (cap1.view().kind == CapKind::IRQHandlerCap));
        assert(rhs_is_untyped == (cap2.view().kind == CapKind::UntypedCap));
        assert(rhs_is_endpoint == (cap2.view().kind == CapKind::EndpointCap));
        assert(rhs_is_notification == (cap2.view().kind == CapKind::NotificationCap));
        assert(rhs_is_reply == (cap2.view().kind == CapKind::ReplyCap));
        assert(rhs_is_cnode == (cap2.view().kind == CapKind::CNodeCap));
        assert(rhs_is_thread == (cap2.view().kind == CapKind::ThreadCap));
        assert(rhs_is_irq_control == (cap2.view().kind == CapKind::IRQControlCap));
        assert(rhs_is_irq_handler == (cap2.view().kind == CapKind::IRQHandlerCap));
        assert(rhs_is_zombie == (cap2.view().kind == CapKind::ZombieCap));

        if lhs_is_untyped {
            assert(cap1.view().kind == CapKind::UntypedCap);
            lemma_bridge_cap_object_shape_for_kind(
                cap1,
                CapKind::UntypedCap,
                ObjectKind::Untyped,
            );
            lemma_bridge_untyped_data_shape(cap1);
            assert(cap1.view().object is Some);
            assert(cap1.view().untyped is Some);
            assert(cap1.view().untyped.unwrap().block_size_bits == cap1.snapshot.untyped_block_size as int);
            assert(cap1.view().untyped.unwrap().block_size_bits < cspace_word_bits());
            assert(lhs_top_u128 as int == cap1.snapshot.object_addr as int
                + cspace_spec_pow2(cap1.snapshot.untyped_block_size as nat) - 1);

            if rhs_is_untyped {
                assert(cap2.view().kind == CapKind::UntypedCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::UntypedCap,
                    ObjectKind::Untyped,
                );
                lemma_bridge_untyped_data_shape(cap2);
                assert(cap2.view().object is Some);
                assert(cap2.view().untyped is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(spec_cap_size_bits(cap2.view()) == cap2.snapshot.untyped_block_size as int);
            } else if rhs_is_endpoint {
                assert(cap2.view().kind == CapKind::EndpointCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::EndpointCap,
                    ObjectKind::Endpoint,
                );
                assert(cap2.view().object is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(spec_cap_size_bits(cap2.view()) == cspace_endpoint_bits());
            } else if rhs_is_notification {
                assert(cap2.view().kind == CapKind::NotificationCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::NotificationCap,
                    ObjectKind::Notification,
                );
                assert(cap2.view().object is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(spec_cap_size_bits(cap2.view()) == cspace_notification_bits());
            } else if rhs_is_cnode {
                assert(cap2.view().kind == CapKind::CNodeCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::CNodeCap,
                    ObjectKind::CNode,
                );
                lemma_bridge_cnode_data_shape(cap2);
                assert(cap2.view().object is Some);
                assert(cap2.view().cnode is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(
                    spec_cap_size_bits(cap2.view())
                        == cap2.snapshot.cnode_radix as int + cspace_slot_bits()
                );
                assert(cap2.snapshot.cnode_radix as int + cspace_slot_bits() < cspace_word_bits());
            } else if rhs_is_thread {
                assert(cap2.view().kind == CapKind::ThreadCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::ThreadCap,
                    ObjectKind::Thread,
                );
                assert(cap2.view().object is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(spec_cap_size_bits(cap2.view()) == cspace_tcb_bits());
            } else if rhs_is_zombie {
                assert(cap2.view().kind == CapKind::ZombieCap);
                lemma_bridge_cap_object_shape_for_kind(
                    cap2,
                    CapKind::ZombieCap,
                    ObjectKind::Zombie,
                );
                assert(cap2.view().object is Some);
                assert(spec_is_physical_cap(cap2.view()));
                assert(spec_cap_size_bits(cap2.view()) == 0);
            } else {
                assert(!spec_is_physical_cap(cap2.view()));
            }

            if rhs_is_physical {
                assert(cap2.view().object is Some);
                assert(rhs_top_u128 as int == cap2.snapshot.object_addr as int
                    + cspace_spec_pow2(rhs_size_bits as nat) - 1);
                assert(spec_cap_range_top(cap2.view()) == rhs_top_u128 as int);
            }
            assert(
                untyped_contains
                    == spec_untyped_cap_contains_cap(cap1.view(), cap2.view())
            );
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view())
                    == spec_untyped_cap_contains_cap(cap1.view(), cap2.view())
            );
        } else if lhs_is_endpoint {
            assert(cap1.view().kind == CapKind::EndpointCap);
            if rhs_is_endpoint {
                assert(cap2.view().kind == CapKind::EndpointCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::EndpointCap,
                    ObjectKind::Endpoint,
                );
            } else {
                assert(cap2.view().kind != CapKind::EndpointCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_endpoint
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_notification {
            assert(cap1.view().kind == CapKind::NotificationCap);
            if rhs_is_notification {
                assert(cap2.view().kind == CapKind::NotificationCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::NotificationCap,
                    ObjectKind::Notification,
                );
            } else {
                assert(cap2.view().kind != CapKind::NotificationCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_notification
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_cnode {
            assert(cap1.view().kind == CapKind::CNodeCap);
            if rhs_is_cnode {
                assert(cap2.view().kind == CapKind::CNodeCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::CNodeCap,
                    ObjectKind::CNode,
                );
                lemma_bridge_cnode_data_shape(cap1);
                lemma_bridge_cnode_data_shape(cap2);
            } else {
                assert(cap2.view().kind != CapKind::CNodeCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_cnode
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                        && cap1.snapshot.cnode_present
                        && cap2.snapshot.cnode_present
                        && cap1.snapshot.cnode_radix as int == cap2.snapshot.cnode_radix as int
                )
            );
        } else if lhs_is_thread {
            assert(cap1.view().kind == CapKind::ThreadCap);
            if rhs_is_thread {
                assert(cap2.view().kind == CapKind::ThreadCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::ThreadCap,
                    ObjectKind::Thread,
                );
            } else {
                assert(cap2.view().kind != CapKind::ThreadCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_thread
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_reply {
            assert(cap1.view().kind == CapKind::ReplyCap);
            if rhs_is_reply {
                assert(cap2.view().kind == CapKind::ReplyCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::ReplyCap,
                    ObjectKind::Reply,
                );
            } else {
                assert(cap2.view().kind != CapKind::ReplyCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_reply
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_irq_control {
            assert(cap1.view().kind == CapKind::IRQControlCap);
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view())
                    == (rhs_is_irq_control || rhs_is_irq_handler)
            );
        } else if lhs_is_irq_handler {
            assert(cap1.view().kind == CapKind::IRQHandlerCap);
            if rhs_is_irq_handler {
                assert(cap2.view().kind == CapKind::IRQHandlerCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::IRQHandlerCap,
                    ObjectKind::IRQ,
                );
            } else {
                assert(cap2.view().kind != CapKind::IRQHandlerCap);
                assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_region_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_irq_handler
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else {
            assert(spec_same_region_as_caps(cap1.view(), cap2.view()) == false);
        }
    }
    ret
}

pub fn same_region_as_refined(
    raw_cap1: &cap,
    raw_cap2: &cap,
) -> (ret: bool)
    ensures
        same_region_as_exec_contract(raw_cap1, raw_cap2, ret),
{
    let cap1 = bridge_cap(raw_cap1);
    let cap2 = bridge_cap(raw_cap2);
    let ret = same_region_as_from_bridges(cap1, cap2);
    proof {
        assert(cap1.view() == trusted_view_cap(raw_cap1));
        assert(cap2.view() == trusted_view_cap(raw_cap2));
        assert(
            spec_same_region_as_caps(trusted_view_cap(raw_cap1), trusted_view_cap(raw_cap2))
                == spec_same_region_as_caps(cap1.view(), cap2.view())
        );
    }
    assert(same_region_as_exec_contract(raw_cap1, raw_cap2, ret));
    ret
}

fn is_mdb_parent_of_via_same_region_as_refined(
    raw_parent: &cte_t,
    raw_child: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(parent): Ghost<SlotId>,
    Ghost(child): Ghost<SlotId>,
) -> (ret: bool)
    requires
        is_mdb_parent_of_call_pre_at(heap, state, parent, child, raw_parent, raw_child),
    ensures
        is_mdb_parent_of_exec_contract(state, parent, child, ret),
{
    proof {
        lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
            heap,
            state,
            parent,
            raw_parent,
        );
        lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
            heap,
            state,
            child,
            raw_child,
        );
    }

    let parent_cte = bridge_cte(raw_parent);
    let child_cte = bridge_cte(raw_child);
    let parent_cap = CapBridge { snapshot: parent_cte.snapshot.cap };
    let child_cap = CapBridge { snapshot: child_cte.snapshot.cap };
    let raw_parent_cap = trusted_cap_ref_from_slot(raw_parent);
    let raw_child_cap = trusted_cap_ref_from_slot(raw_child);
    let parent_revocable = parent_cte.snapshot.mdb_revocable;
    let child_first_badged = child_cte.snapshot.mdb_first_badged;
    let same_region = same_region_as(raw_parent_cap, raw_child_cap);

    let badge_compatible =
        if parent_cte.snapshot.cap.tag == 4
            && parent_cte.snapshot.cap.badge_present
            && parent_cte.snapshot.cap.badge != 0
        {
            child_cte.snapshot.cap.tag == 4
                && child_cte.snapshot.cap.badge_present
                && child_cte.snapshot.cap.badge == parent_cte.snapshot.cap.badge
                && !child_first_badged
        } else if parent_cte.snapshot.cap.tag == 6
            && parent_cte.snapshot.cap.badge_present
            && parent_cte.snapshot.cap.badge != 0
        {
            child_cte.snapshot.cap.tag == 6
                && child_cte.snapshot.cap.badge_present
                && child_cte.snapshot.cap.badge == parent_cte.snapshot.cap.badge
                && !child_first_badged
        } else {
            true
        };

    let ret = parent_revocable && same_region && badge_compatible;

    proof {
        assert(parent_cte.view() == trusted_view_cte(raw_parent));
        assert(child_cte.view() == trusted_view_cte(raw_child));
        assert(trusted_view_cte(raw_parent) == state.slot_entry(parent));
        assert(trusted_view_cte(raw_child) == state.slot_entry(child));
        assert(parent_cte.view() == state.slot_entry(parent));
        assert(child_cte.view() == state.slot_entry(child));
        assert(view_cap(parent_cte.snapshot.cap) == state.slot_cap(parent));
        assert(view_cap(child_cte.snapshot.cap) == state.slot_cap(child));
        assert(parent_revocable == state.slot_entry(parent).mdb_revocable);
        assert(child_first_badged == state.slot_entry(child).mdb_first_badged);

        assert(parent_cap.view() == trusted_view_cte(raw_parent).cap);
        assert(child_cap.view() == trusted_view_cte(raw_child).cap);
        assert(parent_cap.view() == state.slot_cap(parent));
        assert(child_cap.view() == state.slot_cap(child));
        assert(trusted_view_cap(raw_parent_cap) == trusted_view_cte(raw_parent).cap);
        assert(trusted_view_cap(raw_child_cap) == trusted_view_cte(raw_child).cap);
        assert(same_region_as_exec_contract(raw_parent_cap, raw_child_cap, same_region));
        assert(same_region == spec_same_region_as_caps(state.slot_cap(parent), state.slot_cap(child)));

        if parent_cte.snapshot.cap.tag == 4
            && parent_cte.snapshot.cap.badge_present
            && parent_cte.snapshot.cap.badge != 0
        {
            assert(view_cap(parent_cte.snapshot.cap).kind == CapKind::EndpointCap);
            assert(view_cap(parent_cte.snapshot.cap).badge == Some(parent_cte.snapshot.cap.badge as int));
            assert(
                badge_compatible
                    == spec_mdb_parent_badge_compatible_caps(
                        view_cap(parent_cte.snapshot.cap),
                        view_cap(child_cte.snapshot.cap),
                        child_first_badged,
                    )
            );
        } else if parent_cte.snapshot.cap.tag == 6
            && parent_cte.snapshot.cap.badge_present
            && parent_cte.snapshot.cap.badge != 0
        {
            assert(view_cap(parent_cte.snapshot.cap).kind == CapKind::NotificationCap);
            assert(view_cap(parent_cte.snapshot.cap).badge == Some(parent_cte.snapshot.cap.badge as int));
            assert(
                badge_compatible
                    == spec_mdb_parent_badge_compatible_caps(
                        view_cap(parent_cte.snapshot.cap),
                        view_cap(child_cte.snapshot.cap),
                        child_first_badged,
                    )
            );
        } else {
            assert(
                badge_compatible
                    == spec_mdb_parent_badge_compatible_caps(
                        view_cap(parent_cte.snapshot.cap),
                        view_cap(child_cte.snapshot.cap),
                        child_first_badged,
                    )
            );
        }

        assert(
            spec_mdb_parent_badge_compatible_caps(
                view_cap(parent_cte.snapshot.cap),
                view_cap(child_cte.snapshot.cap),
                child_first_badged,
            ) == spec_mdb_parent_badge_compatible_caps(
                state.slot_cap(parent),
                state.slot_cap(child),
                state.slot_entry(child).mdb_first_badged,
            )
        );
        assert(
            ret
                == spec_mdb_parent_of_caps(
                    state.slot_cap(parent),
                    state.slot_entry(parent).mdb_revocable,
                    state.slot_cap(child),
                    state.slot_entry(child).mdb_first_badged,
                )
        );
        assert(ret == state.mdb_parent_of(parent, child));
    }

    assert(is_mdb_parent_of_exec_contract(state, parent, child, ret));
    ret
}

fn same_object_as_from_bridges(
    cap1: CapBridge,
    cap2: CapBridge,
) -> (ret: bool)
    requires
        cap1.wf(),
        cap2.wf(),
    ensures
        ret == spec_same_object_as_caps(cap1.view(), cap2.view()),
{
    let lhs_tag = cap1.snapshot.tag;
    let rhs_tag = cap2.snapshot.tag;
    let lhs_is_null = cap_tag_is_null(lhs_tag);
    let lhs_is_untyped = cap_tag_is_untyped(lhs_tag);
    let lhs_is_endpoint = cap_tag_is_endpoint(lhs_tag);
    let lhs_is_notification = cap_tag_is_notification(lhs_tag);
    let lhs_is_reply = cap_tag_is_reply(lhs_tag);
    let lhs_is_cnode = cap_tag_is_cnode(lhs_tag);
    let lhs_is_thread = cap_tag_is_thread(lhs_tag);
    let lhs_is_irq_control = cap_tag_is_irq_control(lhs_tag);
    let lhs_is_irq_handler = cap_tag_is_irq_handler(lhs_tag);
    let lhs_is_zombie = cap_tag_is_zombie(lhs_tag);
    let lhs_is_arch = cap_tag_is_arch(lhs_tag);

    let rhs_is_endpoint = cap_tag_is_endpoint(rhs_tag);
    let rhs_is_notification = cap_tag_is_notification(rhs_tag);
    let rhs_is_reply = cap_tag_is_reply(rhs_tag);
    let rhs_is_cnode = cap_tag_is_cnode(rhs_tag);
    let rhs_is_thread = cap_tag_is_thread(rhs_tag);
    let rhs_is_irq_handler = cap_tag_is_irq_handler(rhs_tag);
    let ret = if lhs_is_null || lhs_is_untyped || lhs_is_irq_control || lhs_is_zombie || lhs_is_arch {
        false
    } else if lhs_is_endpoint {
        rhs_is_endpoint
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_notification {
        rhs_is_notification
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_reply {
        rhs_is_reply
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_cnode {
        rhs_is_cnode
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
            && cap1.snapshot.cnode_present
            && cap2.snapshot.cnode_present
            && cap1.snapshot.cnode_radix == cap2.snapshot.cnode_radix
    } else if lhs_is_thread {
        rhs_is_thread
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else if lhs_is_irq_handler {
        rhs_is_irq_handler
            && cap1.snapshot.object_present
            && cap2.snapshot.object_present
            && cap1.snapshot.object_addr == cap2.snapshot.object_addr
    } else {
        false
    };

    proof {
        assert(lhs_is_null == (cap1.view().kind == CapKind::NullCap));
        assert(lhs_is_untyped == (cap1.view().kind == CapKind::UntypedCap));
        assert(lhs_is_endpoint == (cap1.view().kind == CapKind::EndpointCap));
        assert(lhs_is_notification == (cap1.view().kind == CapKind::NotificationCap));
        assert(lhs_is_reply == (cap1.view().kind == CapKind::ReplyCap));
        assert(lhs_is_cnode == (cap1.view().kind == CapKind::CNodeCap));
        assert(lhs_is_thread == (cap1.view().kind == CapKind::ThreadCap));
        assert(lhs_is_irq_control == (cap1.view().kind == CapKind::IRQControlCap));
        assert(lhs_is_irq_handler == (cap1.view().kind == CapKind::IRQHandlerCap));
        assert(lhs_is_zombie == (cap1.view().kind == CapKind::ZombieCap));
        assert(lhs_is_arch == (cap1.view().kind == CapKind::ArchCap));
        assert(rhs_is_endpoint == (cap2.view().kind == CapKind::EndpointCap));
        assert(rhs_is_notification == (cap2.view().kind == CapKind::NotificationCap));
        assert(rhs_is_reply == (cap2.view().kind == CapKind::ReplyCap));
        assert(rhs_is_cnode == (cap2.view().kind == CapKind::CNodeCap));
        assert(rhs_is_thread == (cap2.view().kind == CapKind::ThreadCap));
        assert(rhs_is_irq_handler == (cap2.view().kind == CapKind::IRQHandlerCap));

        assert(
            lhs_is_null || lhs_is_untyped || lhs_is_endpoint || lhs_is_notification || lhs_is_cnode
                || lhs_is_thread || lhs_is_reply || lhs_is_irq_control || lhs_is_irq_handler
                || lhs_is_zombie || lhs_is_arch
        );

        if lhs_is_null || lhs_is_untyped || lhs_is_irq_control || lhs_is_zombie || lhs_is_arch {
            assert(ret == false);
            assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
        } else if lhs_is_endpoint {
            assert(cap1.view().kind == CapKind::EndpointCap);
            if rhs_is_endpoint {
                assert(cap2.view().kind == CapKind::EndpointCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::EndpointCap,
                    ObjectKind::Endpoint,
                );
            } else {
                assert(cap2.view().kind != CapKind::EndpointCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_endpoint
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_notification {
            assert(cap1.view().kind == CapKind::NotificationCap);
            if rhs_is_notification {
                assert(cap2.view().kind == CapKind::NotificationCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::NotificationCap,
                    ObjectKind::Notification,
                );
            } else {
                assert(cap2.view().kind != CapKind::NotificationCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_notification
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_reply {
            assert(cap1.view().kind == CapKind::ReplyCap);
            if rhs_is_reply {
                assert(cap2.view().kind == CapKind::ReplyCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::ReplyCap,
                    ObjectKind::Reply,
                );
            } else {
                assert(cap2.view().kind != CapKind::ReplyCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_reply
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_cnode {
            assert(cap1.view().kind == CapKind::CNodeCap);
            if rhs_is_cnode {
                assert(cap2.view().kind == CapKind::CNodeCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::CNodeCap,
                    ObjectKind::CNode,
                );
                lemma_bridge_cnode_data_shape(cap1);
                lemma_bridge_cnode_data_shape(cap2);
            } else {
                assert(cap2.view().kind != CapKind::CNodeCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_cnode
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                        && cap1.snapshot.cnode_present
                        && cap2.snapshot.cnode_present
                        && cap1.snapshot.cnode_radix as int == cap2.snapshot.cnode_radix as int
                )
            );
        } else if lhs_is_thread {
            assert(cap1.view().kind == CapKind::ThreadCap);
            if rhs_is_thread {
                assert(cap2.view().kind == CapKind::ThreadCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::ThreadCap,
                    ObjectKind::Thread,
                );
            } else {
                assert(cap2.view().kind != CapKind::ThreadCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_thread
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else if lhs_is_irq_handler {
            assert(cap1.view().kind == CapKind::IRQHandlerCap);
            if rhs_is_irq_handler {
                assert(cap2.view().kind == CapKind::IRQHandlerCap);
                lemma_bridge_caps_same_object_ref_for_kind(
                    cap1,
                    cap2,
                    CapKind::IRQHandlerCap,
                    ObjectKind::IRQ,
                );
            } else {
                assert(cap2.view().kind != CapKind::IRQHandlerCap);
                assert(spec_same_object_as_caps(cap1.view(), cap2.view()) == false);
            }
            assert(
                spec_same_object_as_caps(cap1.view(), cap2.view()) == (
                    rhs_is_irq_handler
                        && cap1.snapshot.object_present
                        && cap2.snapshot.object_present
                        && cap1.snapshot.object_addr as int == cap2.snapshot.object_addr as int
                )
            );
        } else {
            assert(false);
        }
    }
    ret
}

pub fn same_object_as_refined(
    raw_cap1: &cap,
    raw_cap2: &cap,
) -> (ret: bool)
    ensures
        same_object_as_exec_contract(raw_cap1, raw_cap2, ret),
{
    let cap1 = bridge_cap(raw_cap1);
    let cap2 = bridge_cap(raw_cap2);
    let ret = same_object_as_from_bridges(cap1, cap2);
    proof {
        assert(cap1.view() == trusted_view_cap(raw_cap1));
        assert(cap2.view() == trusted_view_cap(raw_cap2));
        assert(
            spec_same_object_as_caps(trusted_view_cap(raw_cap1), trusted_view_cap(raw_cap2))
                == spec_same_object_as_caps(cap1.view(), cap2.view())
        );
    }
    assert(same_object_as_exec_contract(raw_cap1, raw_cap2, ret));
    ret
}

pub fn is_cap_revocable_refined(
    raw_derived_cap: &cap,
    raw_src_cap: &cap,
) -> (ret: bool)
    ensures
        is_cap_revocable_exec_contract(raw_derived_cap, raw_src_cap, ret),
{
    let derived_cap = bridge_cap(raw_derived_cap);
    let src_cap = bridge_cap(raw_src_cap);

    let derived_tag = derived_cap.snapshot.tag;
    let src_tag = src_cap.snapshot.tag;

    let ret = if derived_tag == 4u64 {
        src_tag == 4u64 && derived_cap.snapshot.badge != src_cap.snapshot.badge
    } else if derived_tag == 6u64 {
        src_tag == 6u64 && derived_cap.snapshot.badge != src_cap.snapshot.badge
    } else if derived_tag == 16u64 {
        src_tag == 14u64 || src_tag == 11u64 || src_tag == 20u64
    } else if derived_tag == 2u64 {
        true
    } else {
        false
    };

    proof {
        assert(derived_cap.view() == trusted_view_cap(raw_derived_cap));
        assert(src_cap.view() == trusted_view_cap(raw_src_cap));

        assert(derived_cap.wf());
        assert(src_cap.wf());
        lemma_supported_cap_tag_kind_equivalences(derived_tag);
        lemma_supported_cap_tag_kind_equivalences(src_tag);

        if derived_tag == 4u64 {
            assert(derived_cap.view().kind == CapKind::EndpointCap);
            assert(derived_cap.snapshot.badge_present);
            assert(derived_cap.view().badge == Some(derived_cap.snapshot.badge as int));
            if src_tag == 4u64 {
                assert(src_cap.view().kind == CapKind::EndpointCap);
                assert(src_cap.snapshot.badge_present);
                assert(src_cap.view().badge == Some(src_cap.snapshot.badge as int));
            } else {
                assert(src_cap.view().kind != CapKind::EndpointCap);
            }
            assert(
                spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == (
                    (src_tag == 4u64)
                        && derived_cap.snapshot.badge as int != src_cap.snapshot.badge as int
                )
            );
        } else if derived_tag == 6u64 {
            assert(derived_cap.view().kind == CapKind::NotificationCap);
            assert(derived_cap.snapshot.badge_present);
            assert(derived_cap.view().badge == Some(derived_cap.snapshot.badge as int));
            if src_tag == 6u64 {
                assert(src_cap.view().kind == CapKind::NotificationCap);
                assert(src_cap.snapshot.badge_present);
                assert(src_cap.view().badge == Some(src_cap.snapshot.badge as int));
            } else {
                assert(src_cap.view().kind != CapKind::NotificationCap);
            }
            assert(
                spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == (
                    (src_tag == 6u64)
                        && derived_cap.snapshot.badge as int != src_cap.snapshot.badge as int
                )
            );
        } else if derived_tag == 16u64 {
            assert(derived_cap.view().kind == CapKind::IRQHandlerCap);
            assert(
                spec_is_cap_revocable(derived_cap.view(), src_cap.view())
                    == (src_tag == 14u64 || src_tag == 11u64 || src_tag == 20u64)
            );
        } else if derived_tag == 2u64 {
            assert(derived_cap.view().kind == CapKind::UntypedCap);
            assert(spec_is_cap_revocable(derived_cap.view(), src_cap.view()));
        } else {
            assert(
                derived_cap.view().kind != CapKind::EndpointCap
                    && derived_cap.view().kind != CapKind::NotificationCap
                    && derived_cap.view().kind != CapKind::IRQHandlerCap
                    && derived_cap.view().kind != CapKind::UntypedCap
            );
            assert(spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == false);
        }

        assert(spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == ret) by {
            if derived_tag == 4u64 {
                assert(
                    spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == (
                        (src_tag == 4u64)
                            && derived_cap.snapshot.badge as int != src_cap.snapshot.badge as int
                    )
                );
            } else if derived_tag == 6u64 {
                assert(
                    spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == (
                        (src_tag == 6u64)
                            && derived_cap.snapshot.badge as int != src_cap.snapshot.badge as int
                    )
                );
            } else if derived_tag == 16u64 {
                assert(
                    spec_is_cap_revocable(derived_cap.view(), src_cap.view())
                        == (src_tag == 14u64 || src_tag == 11u64 || src_tag == 20u64)
                );
            } else if derived_tag == 2u64 {
                assert(spec_is_cap_revocable(derived_cap.view(), src_cap.view()));
            } else {
                assert(spec_is_cap_revocable(derived_cap.view(), src_cap.view()) == false);
            }
        }
    }

    assert(is_cap_revocable_exec_contract(raw_derived_cap, raw_src_cap, ret));
    ret
}

fn is_long_running_delete_via_is_final_cap_refined(
    raw_slot: &cte_t,
    Ghost(heap): Ghost<ConcreteHeapId>,
    Ghost(state): Ghost<CSpaceState>,
    Ghost(slot): Ghost<SlotId>,
) -> (ret: bool)
    requires
        spec_is_long_running_delete_pre(state, slot),
        is_final_cap_call_pre_at(heap, state, slot, raw_slot),
    ensures
        is_long_running_delete_exec_contract(state, slot, ret),
{
    let is_final = is_final_cap_refined(raw_slot, Ghost(heap), Ghost(state), Ghost(slot));
    let slot_cte = bridge_cte(raw_slot);
    let cap_tag = slot_cte.snapshot.cap.tag;
    let is_null = cap_tag_is_null(cap_tag);
    let is_thread = cap_tag_is_thread(cap_tag);
    let is_zombie = cap_tag_is_zombie(cap_tag);
    let is_cnode = cap_tag_is_cnode(cap_tag);
    let ret =
        !is_null
            && is_final
            && (
                is_thread
                || is_zombie
                || is_cnode
            );
    proof {
        lemma_is_final_cap_call_pre_at_implies_raw_slot_view_matches_state(
            heap,
            state,
            slot,
            raw_slot,
        );
        assert(slot_cte.view() == trusted_view_cte(raw_slot));
        assert(is_null == (slot_cte.view().cap.kind == CapKind::NullCap));
        assert(is_thread == (slot_cte.view().cap.kind == CapKind::ThreadCap));
        assert(is_zombie == (slot_cte.view().cap.kind == CapKind::ZombieCap));
        assert(is_cnode == (slot_cte.view().cap.kind == CapKind::CNodeCap));
        assert(is_null == (trusted_view_cte(raw_slot).cap.kind == CapKind::NullCap));
        assert(is_thread == (trusted_view_cte(raw_slot).cap.kind == CapKind::ThreadCap));
        assert(is_zombie == (trusted_view_cte(raw_slot).cap.kind == CapKind::ZombieCap));
        assert(is_cnode == (trusted_view_cte(raw_slot).cap.kind == CapKind::CNodeCap));
        assert(trusted_view_cte(raw_slot).cap == state.slot_cap(slot));
        assert(is_null == (state.slot_cap(slot).kind == CapKind::NullCap));
        assert(is_thread == (state.slot_cap(slot).kind == CapKind::ThreadCap));
        assert(is_zombie == (state.slot_cap(slot).kind == CapKind::ZombieCap));
        assert(is_cnode == (state.slot_cap(slot).kind == CapKind::CNodeCap));
        assert(is_final == state.is_final_cap(slot));
    }
    assert(is_long_running_delete_exec_contract(state, slot, ret));
    ret
}

pub fn insert_new_cap_refined(
    parent_slot: &mut cte_t,
    slot_ref: &mut cte_t,
    raw_new_cap: &cap,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(parent): Ghost<SlotId>,
    Ghost(slot): Ghost<SlotId>,
)
    requires
        old_state.has_slot(parent),
        old_state.has_slot(slot),
        new_state.has_slot(parent),
        new_state.has_slot(slot),
        insert_new_cap_call_pre_at(
            old_heap,
            old_state,
            parent,
            slot,
            raw_new_cap,
            old(parent_slot),
            old(slot_ref),
        ),
        spec_insert_new_cap_post(
            old_state,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        ),
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
        spec_insert_new_cap(
            old_state,
            new_state,
            parent,
            slot,
            trusted_view_cap(raw_new_cap),
        ),
        new_state.slot_entry(parent)
            == spec_insert_new_cap_expected_parent_entry(
                old_state,
                parent,
                slot,
            ),
        new_state.slot_entry(slot)
            == spec_insert_new_cap_expected_slot_entry(
                old_state,
                parent,
                slot,
                trusted_view_cap(raw_new_cap),
            ),
        trusted_concrete_slot_view_at(new_heap, parent)
            == spec_insert_new_cap_expected_parent_entry(
                old_state,
                parent,
                slot,
            ),
        trusted_concrete_slot_view_at(new_heap, slot)
            == spec_insert_new_cap_expected_slot_entry(
                old_state,
                parent,
                slot,
                trusted_view_cap(raw_new_cap),
            ),
{
    insert_new_cap_exec_step(
        parent_slot,
        slot_ref,
        raw_new_cap,
        Ghost(old_heap),
        Ghost(old_state),
        Ghost(new_heap),
        Ghost(new_state),
        Ghost(parent),
        Ghost(slot),
    );
    assert(insert_new_cap_exec_contract(
        old_state,
        new_heap,
        new_state,
        parent,
        slot,
        raw_new_cap,
    ));
    assert(trusted_cspace_heap_matches_state_at(new_heap, new_state));
    assert(spec_insert_new_cap(
        old_state,
        new_state,
        parent,
        slot,
        trusted_view_cap(raw_new_cap),
    ));
    assert(new_state.slot_entry(parent) == spec_insert_new_cap_expected_parent_entry(
        old_state,
        parent,
        slot,
    ));
    assert(new_state.slot_entry(slot) == spec_insert_new_cap_expected_slot_entry(
        old_state,
        parent,
        slot,
        trusted_view_cap(raw_new_cap),
    ));
    assert(trusted_concrete_slot_view_at(new_heap, parent) == spec_insert_new_cap_expected_parent_entry(
        old_state,
        parent,
        slot,
    ));
    assert(trusted_concrete_slot_view_at(new_heap, slot) == spec_insert_new_cap_expected_slot_entry(
        old_state,
        parent,
        slot,
        trusted_view_cap(raw_new_cap),
    ));
}

pub fn cte_move_refined(
    raw_new_cap: &cap,
    src_slot: &mut cte_t,
    dest_slot: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(src): Ghost<SlotId>,
    Ghost(dest): Ghost<SlotId>,
)
    requires
        old_state.has_slot(src),
        old_state.has_slot(dest),
        new_state.has_slot(src),
        new_state.has_slot(dest),
        cte_move_call_pre_at(old_heap, old_state, src, dest, raw_new_cap, old(src_slot), old(dest_slot)),
        spec_cte_move_post(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        ),
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
        spec_cte_move(
            old_state,
            new_state,
            src,
            dest,
            trusted_view_cap(raw_new_cap),
        ),
        new_state.slot_entry(src) == spec_cte_move_expected_src_entry(),
        new_state.slot_entry(dest)
            == spec_cte_move_expected_dest_entry(
                old_state,
                src,
                trusted_view_cap(raw_new_cap),
            ),
        trusted_concrete_slot_view_at(new_heap, src) == spec_cte_move_expected_src_entry(),
        trusted_concrete_slot_view_at(new_heap, dest)
            == spec_cte_move_expected_dest_entry(
                old_state,
                src,
                trusted_view_cap(raw_new_cap),
            ),
{
    cte_move_exec_step(
        raw_new_cap,
        src_slot,
        dest_slot,
        Ghost(old_heap),
        Ghost(old_state),
        Ghost(new_heap),
        Ghost(new_state),
        Ghost(src),
        Ghost(dest),
    );
    assert(cte_move_exec_contract(
        old_state,
        new_heap,
        new_state,
        src,
        dest,
        raw_new_cap,
    ));
    assert(trusted_cspace_heap_matches_state_at(new_heap, new_state));
    assert(spec_cte_move(
        old_state,
        new_state,
        src,
        dest,
        trusted_view_cap(raw_new_cap),
    ));
    assert(new_state.slot_entry(src) == spec_cte_move_expected_src_entry());
    assert(new_state.slot_entry(dest) == spec_cte_move_expected_dest_entry(
        old_state,
        src,
        trusted_view_cap(raw_new_cap),
    ));
    assert(trusted_concrete_slot_view_at(new_heap, src) == spec_cte_move_expected_src_entry());
    assert(trusted_concrete_slot_view_at(new_heap, dest) == spec_cte_move_expected_dest_entry(
        old_state,
        src,
        trusted_view_cap(raw_new_cap),
    ));
}

pub fn cte_swap_refined(
    raw_cap1: &cap,
    slot1: &mut cte_t,
    raw_cap2: &cap,
    slot2: &mut cte_t,
    Ghost(old_heap): Ghost<ConcreteHeapId>,
    Ghost(old_state): Ghost<CSpaceState>,
    Ghost(new_heap): Ghost<ConcreteHeapId>,
    Ghost(new_state): Ghost<CSpaceState>,
    Ghost(slot1_id): Ghost<SlotId>,
    Ghost(slot2_id): Ghost<SlotId>,
)
    requires
        old_state.has_slot(slot1_id),
        old_state.has_slot(slot2_id),
        new_state.has_slot(slot1_id),
        new_state.has_slot(slot2_id),
        cte_swap_call_pre_at(
            old_heap,
            old_state,
            slot1_id,
            slot2_id,
            raw_cap1,
            raw_cap2,
            old(slot1),
            old(slot2),
        ),
        spec_cte_swap_post(
            old_state,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        ),
    ensures
        trusted_cspace_heap_matches_state_at(new_heap, new_state),
        spec_cte_swap(
            old_state,
            new_state,
            slot1_id,
            slot2_id,
            trusted_view_cap(raw_cap1),
            trusted_view_cap(raw_cap2),
        ),
        new_state.slot_entry(slot1_id)
            == spec_cte_swap_expected_slot1_entry(
                old_state,
                slot1_id,
                slot2_id,
                trusted_view_cap(raw_cap2),
            ),
        new_state.slot_entry(slot2_id)
            == spec_cte_swap_expected_slot2_entry(
                old_state,
                slot1_id,
                slot2_id,
                trusted_view_cap(raw_cap1),
            ),
        trusted_concrete_slot_view_at(new_heap, slot1_id)
            == spec_cte_swap_expected_slot1_entry(
                old_state,
                slot1_id,
                slot2_id,
                trusted_view_cap(raw_cap2),
            ),
        trusted_concrete_slot_view_at(new_heap, slot2_id)
            == spec_cte_swap_expected_slot2_entry(
                old_state,
                slot1_id,
                slot2_id,
                trusted_view_cap(raw_cap1),
            ),
{
    cte_swap_exec_step(
        raw_cap1,
        slot1,
        raw_cap2,
        slot2,
        Ghost(old_heap),
        Ghost(old_state),
        Ghost(new_heap),
        Ghost(new_state),
        Ghost(slot1_id),
        Ghost(slot2_id),
    );
    assert(cte_swap_exec_contract(
        old_state,
        new_heap,
        new_state,
        slot1_id,
        slot2_id,
        raw_cap1,
        raw_cap2,
    ));
    assert(trusted_cspace_heap_matches_state_at(new_heap, new_state));
    assert(spec_cte_swap(
        old_state,
        new_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap1),
        trusted_view_cap(raw_cap2),
    ));
    assert(new_state.slot_entry(slot1_id) == spec_cte_swap_expected_slot1_entry(
        old_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap2),
    ));
    assert(new_state.slot_entry(slot2_id) == spec_cte_swap_expected_slot2_entry(
        old_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap1),
    ));
    assert(trusted_concrete_slot_view_at(new_heap, slot1_id) == spec_cte_swap_expected_slot1_entry(
        old_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap2),
    ));
    assert(trusted_concrete_slot_view_at(new_heap, slot2_id) == spec_cte_swap_expected_slot2_entry(
        old_state,
        slot1_id,
        slot2_id,
        trusted_view_cap(raw_cap1),
    ));
}

pub fn resolve_address_bits_refined(
    raw_root: &cap,
    cap_ptr: usize,
    bits: usize,
    Ghost(state): Ghost<CSpaceState>,
) -> (ret: ResolveAddressBitsRetBridge)
    requires
        resolve_address_bits_bridge_pre(state, raw_root, cap_ptr, bits),
    ensures
        resolve_address_bits_exec_contract(state, raw_root, cap_ptr, bits, ret),
{
    let ret = resolve_address_bits_exec_step(raw_root, cap_ptr, bits, Ghost(state));
    assert(resolve_address_bits_exec_contract(state, raw_root, cap_ptr, bits, ret));
    ret
}

} // verus!
