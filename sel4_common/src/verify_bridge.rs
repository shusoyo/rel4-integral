//! Verification bridge module for spec-facing wrappers in `sel4_common`.
//!
//! This file provides a stable type-level bridge that verification code can depend on
//! without pulling implementation details from generated bitfield code at call sites.

#![allow(dead_code)]

use crate::structures::exception_t;
use crate::structures_gen::{cap, mdb_node};

/// Bridge wrapper for capability objects.
#[repr(transparent)]
#[derive(Clone)]
pub struct BridgeCap(pub cap);

/// Bridge wrapper for capability tags.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BridgeCapTag(pub u64);

/// Bridge wrapper for MDB nodes.
#[repr(transparent)]
#[derive(Clone)]
pub struct BridgeMdbNode(pub mdb_node);

/// Bridge wrapper for kernel exception values.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BridgeException(pub exception_t);

impl BridgeCap {
	#[inline]
	pub fn from_raw(raw: cap) -> Self {
		Self(raw)
	}

	#[inline]
	pub fn as_raw(&self) -> &cap {
		&self.0
	}

	#[inline]
	pub fn into_raw(self) -> cap {
		self.0
	}

	#[inline]
	pub fn tag(&self) -> BridgeCapTag {
		BridgeCapTag(self.0.get_tag() as u64)
	}
}

impl BridgeCapTag {
	#[inline]
	pub fn from_raw(raw: u64) -> Self {
		Self(raw)
	}

	#[inline]
	pub fn as_raw(&self) -> u64 {
		self.0
	}
}

impl BridgeMdbNode {
	#[inline]
	pub fn from_raw(raw: mdb_node) -> Self {
		Self(raw)
	}

	#[inline]
	pub fn as_raw(&self) -> &mdb_node {
		&self.0
	}

	#[inline]
	pub fn into_raw(self) -> mdb_node {
		self.0
	}
}

impl BridgeException {
	#[inline]
	pub fn from_raw(raw: exception_t) -> Self {
		Self(raw)
	}

	#[inline]
	pub fn as_raw(&self) -> exception_t {
		self.0
	}

	#[inline]
	pub fn is_none(&self) -> bool {
		self.0 == exception_t::EXCEPTION_NONE
	}
}

/// Marker item confirming type bridge module is linked.
pub const VERIFY_BRIDGE_ENABLED: bool = true;
