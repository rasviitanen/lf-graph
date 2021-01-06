use crate::adjlist::AdjacencyList;
use crate::adjlist::{IterRefEntry, RefEntry, Node as InternalNode};

use crate::lftt::{OpType, ReturnCode};
use std::{hash::{BuildHasher, Hash, Hasher}, marker::PhantomData, sync::atomic::Ordering::{SeqCst}};

use crossbeam_epoch::{self as epoch, Atomic, Guard, Shared};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};
use std::collections::hash_map::RandomState;
use crate::types::*;

pub type Range<'a, T> = Box<dyn Iterator<Item = T> + 'a>;

pub trait GraphAPI {
    type Id;
    type Vertex;
    type Edge;

    fn add_vertex(&self, vertex: Self::Vertex);
    fn add_edge(&self, v: Self::Id, e: Self::Id);

    fn find_vertex(&self, v: Self::Id) -> Option<Self::Vertex>;

    fn delete_edge(&self, v: Self::Id, e: Self::Id) -> Result<(), ()>;
    fn delete_vertex(&self, v: Self::Id) -> Option<Self::Vertex>;

    fn out_degree(&self, v: Self::Id) -> usize;
    fn in_degree(&self, v: Self::Id) -> usize;

    fn in_neigh(&self, v: Self::Id) -> Range<Self::Edge>;
    fn out_neigh(&self, v: Self::Id) -> Range<Self::Edge>;

    fn vertices(&self) -> Range<Self::Vertex>;
}

pub trait Node {
    fn id(&self) -> usize;
}

struct GraphTxn<'a, 't, K: Eq + Hash, V, E>{
    graph: &'t Graph<'a, K, V, E>,
    operations: Vec<OpType<'a, V, E>>
}

impl<'a: 't, 't, K: Eq + Hash, V, E> GraphTxn<'a, 't, K, V, E> {
    pub fn new(graph: &'t Graph<'a, K, V, E>) -> Self {
        Self {
            graph,
            operations: Vec::new(),
        }
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn insert(&mut self, k: K, v: V) -> &mut Self {
        self.operations.push(OpType::Insert(make_hash(&self.graph.hasher, &k), Some(v)));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn delete_vertex(&mut self, k: K) -> &mut Self {
        self.operations.push(OpType::Delete(make_hash(&self.graph.hasher, &k)));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn find_vertex(&mut self, k: K) -> &mut Self {
        self.operations.push(OpType::Find(make_hash(&self.graph.hasher, &k)));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn insert_edge(&mut self, vertex_key: K, edge_key: K, edge_info: Option<E>) -> &mut Self {
        self.operations.push(OpType::InsertEdge(make_hash(&self.graph.hasher, &vertex_key), make_hash(&self.graph.hasher, &edge_key), edge_info, true));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn delete_edge(&mut self, vertex_key: K, edge_key: K) -> &mut Self {
        self.operations.push(OpType::DeleteEdge(make_hash(&self.graph.hasher, &vertex_key), make_hash(&self.graph.hasher, &edge_key), true));
        self
    }

    pub fn execute(
        &mut self,
    ) -> std::sync::mpsc::Receiver<ReturnCode<RefEntry<'a, 't, V, E>>> {
        self.graph.inner.txn(self.operations.drain(0..).collect()).execute()
    }
}

pub struct Graph<'a, K, V, E, S = RandomState> {
    inner: AdjacencyList<'a, V, E>,
    phantom: PhantomData<K>,
    hasher: S,
}

#[inline]
fn make_hash<K: Hash + ?Sized>(hash_builder: &impl BuildHasher, val: &K) -> u64 {
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

impl<'a, K, V, E> Graph<'a, K, V, E, RandomState> {
    pub fn new() -> Self {
        Self {
            inner: AdjacencyList::new(),
            phantom: PhantomData,
            hasher: RandomState::new(),
        }
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, E> Graph<'a, K, V, E, RandomState> {
    pub fn add_vertex<'t>(
        &'t self,
        key: K,
        value: V,
    ) -> Option<RefEntry<'a, 't, V, E>> {
        let key = make_hash(&self.hasher, &key);
        let op = OpType::Insert(key, Some(value));
        let insertion_txn = self.inner.txn(vec![op]).execute();

        if let Ok(ReturnCode::Inserted(entry)) = insertion_txn.recv() {
            Some(entry)
        } else {
            None
        }
    }

    pub fn add_edge(&self, parent_key: K, edge_key: K, edge: E, direction_in: bool) {
        let parent_key = make_hash(&self.hasher, &parent_key);
        let edge_key = make_hash(&self.hasher, &edge_key);
        let op = OpType::InsertEdge(parent_key, edge_key, Some(edge), direction_in);
        let insert_edge_txn = self.inner.txn(vec![op]);
        insert_edge_txn.execute().recv().expect("Txn failed");
    }

    pub fn add_empty_edge(&self, parent_key: K, edge_key: K, direction_in: bool) {
        let parent_key = make_hash(&self.hasher, &parent_key);
        let edge_key = make_hash(&self.hasher, &edge_key);
        let op = OpType::InsertEdge(parent_key, edge_key, None, direction_in);
        let insert_edge_txn = self.inner.txn(vec![op]);
        insert_edge_txn.execute().recv().expect("Txn failed");
    }

    pub fn connect<'t>(&self, parent: &InternalNode<V, E>, edge_key: K, edge: E, direction_in: bool) {
        let edge_key = make_hash(&self.hasher, &edge_key);
        unsafe {
            AdjacencyList::connect(parent, edge_key, edge, direction_in);
        }
    }

    pub fn iter_vertices<'t>(&'a self) -> IterRefEntry<'a, 't, 't, V, E> {
        let guard = unsafe { &*(&epoch::pin() as *const _) };
        self.inner.iter(guard)
    }

    pub fn find_vertex<'t>(&'t self, key: K) -> Option<RefEntry<'a, 't, V, E>> {
        let key = make_hash(&self.hasher, &key);
        let op = OpType::Find(key);
        let find_txn = self.inner.txn(vec![op]);
        let res = find_txn.execute();

        if let ReturnCode::Found(entry) = res.recv().unwrap() {
            Some(entry)
        } else {
            None
        }
    }

    pub fn delete_vertex<'t>(&'t self, key: K) -> Option<RefEntry<'a, 't, V, E>> {
        let key = make_hash(&self.hasher, &key);
        let op = OpType::Delete(key);
        let insertion_txn = self.inner.txn(vec![op]).execute();

        if let Ok(ReturnCode::Deleted(entry)) = insertion_txn.recv() {
            Some(entry)
        } else {
            None
        }
    }

    pub fn delete_edge<'t>(
        &'t self,
        parent_key: K,
        edge_key: K,
        direction_in: bool,
    ) -> Result<(), ()> {
        let parent_key = make_hash(&self.hasher, &parent_key);
        let edge_key = make_hash(&self.hasher, &edge_key);

        let op = OpType::DeleteEdge(parent_key, edge_key, direction_in);
        let insertion_txn = self.inner.txn(vec![op]).execute();

        if let Ok(ReturnCode::Success) = insertion_txn.recv() {
            Ok(())
        } else {
            Err(())
        }
    }

    fn out_neigh<'t>(&self, node: &'t RefEntry<'a, 't, V, E>) -> Range<'t, &'a E> {
        let guard = unsafe { &*(&epoch::pin() as *const _) };
        Box::new(node.out_edges.as_ref().unwrap().iter(guard).map(|e| e.node.val.as_ref().unwrap()))
    }

    fn in_neigh<'t>(&self, node: &'t RefEntry<'a, 't, V, E>) -> Range<'t, &'a E> {
        let guard = unsafe { &*(&epoch::pin() as *const _) };
        Box::new(node.in_edges.as_ref().unwrap().iter(guard).map(|e| e.node.val.as_ref().unwrap()))
    }
}

#[cfg(test)]
mod graph_tests {
    use super::*;

    #[test]
    fn test_vertex_insertion() {
        let graph = Graph::<u32, u32, u32>::new();
        graph.add_vertex(1, 123);
        graph.add_vertex(2, 345);
        graph.add_vertex(3, 678);
        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].value(), Some(&123));
        assert_eq!(vertices[1].value(), Some(&345));
        assert_eq!(vertices[2].value(), Some(&678));
    }

    #[test]
    fn test_find_vertex() {
        let graph = Graph::<&str, u32, u32>::new();
        graph.add_vertex("vertex1", 123);
        let vertex = graph.find_vertex("vertex1");
        assert!(vertex.is_some());
        assert_eq!(vertex.unwrap().value(), Some(&123));
    }

    #[test]
    fn test_delete_vertex() {
        let graph = Graph::<u32, u32, u32>::new();
        graph.add_vertex(1, 123);
        let vertex = graph.find_vertex(1);
        assert!(vertex.is_some());
        assert_eq!(vertex.unwrap().value(), Some(&123));
        let deleted = graph.delete_vertex(1);
        assert_eq!(deleted.unwrap().value(), Some(&123));
        let vertex = graph.find_vertex(1);
        assert!(vertex.is_none());
    }

    #[test]
    fn test_edge_insertion() {
        let graph = Graph::<u32, u32, bool>::new();
        graph.add_vertex(1, 123);
        graph.add_vertex(2, 123);

        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 0);
        graph.add_edge(1, 2, true, true);
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 1);
    }

    #[test]
    fn test_in_neigh() {
        let graph = Graph::<u32, u32, u32>::new();
        graph.add_vertex(1, 123);
        graph.add_vertex(2, 123);

        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 0);
        graph.add_edge(1, 2, 3, true);


        let in_neigh = graph.in_neigh(&vertices[0]).collect::<Vec<_>>();
        assert_eq!(in_neigh[0], &3);
    }

    #[test]
    fn test_txn_simple() {
    let graph = Graph::<u32, u32, u32>::new();
        GraphTxn::new(&graph)
            .insert(1, 1)
            .insert(2, 2)
            .insert(3, 3)
            .execute();

        let result = GraphTxn::new(&graph)
            .find_vertex(1)
            .find_vertex(2)
            .find_vertex(3)
            .execute();

        for i in 1..=3 {
            if let Ok(ReturnCode::Found(v)) = result.recv() {
                assert_eq!(v.value().unwrap(), &i);
            } else {
                panic!("Could not find inserted vertices");
            }
        }
    }

    #[test]
    fn test_threaded_txn_simple() {
        let graph = Arc::new(Graph::<u32, u32, u32>::new());

        let graph_clone = Arc::clone(&graph);
        let tx1 = std::thread::spawn(move || {
            GraphTxn::new(&graph_clone)
                .insert(1, 1)
                .insert(2, 2)
                .insert(3, 3)
                .execute();
        });

        tx1.join().unwrap();

        let result = GraphTxn::new(&graph)
            .find_vertex(1)
            .find_vertex(2)
            .find_vertex(3)
            .execute();


        for i in 1..=3 {
            if let Ok(ReturnCode::Found(v)) = result.recv() {
                assert_eq!(v.value().unwrap(), &i);
            } else {
                panic!("Could not find inserted vertices, {:?}", i);
            }
        }
    }

    #[test]
    fn test_multiple_txn_simple() {
        let graph = Graph::<u32, u32, u32>::new();

        GraphTxn::new(&graph)
            .insert(1, 1)
            .insert(2, 2)
            .execute();

        GraphTxn::new(&graph)
                .insert(3, 3)
                .insert(4, 4)
                .execute();

        GraphTxn::new(&graph)
                .insert(5, 5)
                .insert(6, 6)
                .execute();

        GraphTxn::new(&graph)
                .insert(7, 7)
                .insert(8, 8)
                .execute();

        let result = GraphTxn::new(&graph)
            .find_vertex(1)
            .find_vertex(2)
            .find_vertex(3)
            .find_vertex(4)
            .find_vertex(5)
            .find_vertex(6)
            .find_vertex(7)
            .find_vertex(8)
            .execute();

        for i in 1..=8 {
            if let Ok(ReturnCode::Found(v)) = result.recv() {
                assert_eq!(v.value().unwrap(), &i);
            } else {
                panic!("Could not find inserted vertices, {:?}", i);
            }
        }
    }
}