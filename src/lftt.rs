use crate::adjlist::RefEntry;
use crossbeam_utils::atomic::AtomicCell;

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::mem;
use std::ptr;
use std::sync::Arc;

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum OpStatus {
    Active,
    Committed,
    Aborted,
}

#[derive(Debug, Clone)]
pub enum ReturnCode<R> {
    Success,
    Inserted(R),
    Deleted(R),
    Found(R),
    Skip,
    Fail(String),
}

#[derive(Clone)]
pub enum OpType<'a, T, E> {
    Find(u64),
    Insert(u64, Option<T>),
    Connect(&'a RefEntry<'a, 'a, T, E>, u64, E),
    Delete(u64),
    InsertEdge(u64, u64, Option<E>, bool),
    DeleteEdge(u64, u64, bool),
}

pub struct Operator<'a, T, E> {
    pub optype: OpType<'a, T, E>,
}

pub struct Desc<'a, T, E> {
    pub status: AtomicCell<OpStatus>,
    pub size: usize,
    pub ops: std::cell::RefCell<Vec<Operator<'a, T, E>>>,
    pub pending: Vec<AtomicCell<bool>>,
}

impl<'a, T: 'a, E: 'a> Desc<'a, T, E> {
    pub fn new(ops: Vec<Operator<'a, T, E>>) -> Self {
        Self {
            status: AtomicCell::new(OpStatus::Active),
            size: ops.len(),
            pending: (0..ops.len()).map(|_| AtomicCell::new(true)).collect(),
            ops: std::cell::RefCell::new(ops),
        }
    }

    #[must_use]
    pub fn empty() -> Self {
        Self {
            status: AtomicCell::new(OpStatus::Committed),
            size: 0,
            ops: std::cell::RefCell::new(Vec::new()),
            pending: Vec::new(),
        }
    }
}

pub struct NodeDesc<'a, T, E> {
    pub desc: Arc<Desc<'a, T, E>>,
    pub opid: usize,
    pub override_as_find: bool,
    pub override_as_delete: bool,
}

impl<'a, T, E> NodeDesc<'a, T, E> {
    #[inline]
    pub fn new(desc: Arc<Desc<'a, T, E>>, opid: usize) -> Self {
        Self {
            desc,
            opid,
            override_as_find: false,
            override_as_delete: false,
        }
    }
}
