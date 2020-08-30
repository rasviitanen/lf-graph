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

    fn num_nodes(&self) -> usize;
    fn num_edges(&self) -> usize;

    fn out_degree(&self, v: Self::Id) -> usize;
    fn in_degree(&self, v: Self::Id) -> usize;

    fn in_neigh(&self, v: Self::Id) -> Range<Self::Edge>;
    fn out_neigh(&self, v: Self::Id) -> Range<Self::Edge>;

    fn vertices(&self) -> Range<Self::Vertex>;
}

use crate::adjlist::AdjacencyList;
use crate::adjlist::{IterRefEntry, Node as InternalNode};

use crate::lftt::{OpType, ReturnCode};
use std::sync::atomic::Ordering::{SeqCst};

use crossbeam_epoch::{self as epoch, Atomic, Guard, Shared};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use crate::types::*;

pub trait Node {
    fn id(&self) -> usize;
}

pub struct Graph<'a, V: Node, E: Node> {
    inner: AdjacencyList<'a, V, E>,
    cache: Arc<RwLock<BTreeMap<NodeId, &'a InternalNode<'a, V, E>>>>,
    directed: bool,
    num_nodes: usize,
    num_edges: usize,
}

impl<'a, V: 'a + Node, E: Node> Graph<'a, V, E> {
    pub fn directed() -> Self {
        Self {
            inner: AdjacencyList::new(),
            cache: Arc::new(RwLock::new(BTreeMap::new())),
            directed: true,
            num_nodes: 0,
            num_edges: 0,
        }
    }

    pub fn undirected() -> Self {
        Self {
            inner: AdjacencyList::new(),
            cache: Arc::new(RwLock::new(BTreeMap::new())),
            directed: false,
            num_nodes: 0,
            num_edges: 0,
        }
    }

    pub fn execute_ops<'t>(
        &'t self,
        ops: Vec<OpType<'a, V, E>>,
    ) -> std::sync::mpsc::Receiver<ReturnCode<Atomic<InternalNode<'a, V, E>>>> {
        self.inner.txn(ops).execute()
    }

    pub fn add_vertex<'t>(
        &'t self,
        value: V,
    ) -> Option<(usize, Atomic<InternalNode<'a, V, E>>)> {
        let key = value.id();
        let op = OpType::Insert(key, Some(value));
        let insertion_txn = self.inner.txn(vec![op]).execute();

        if let Ok(ReturnCode::Inserted(entry)) = insertion_txn.recv() {
            Some((key, entry))
        } else {
            None
        }
    }

    pub fn add_edge(&self, parent_id: usize, edge: E, direction_in: bool) {
        let op = OpType::InsertEdge(parent_id, edge.id(), Some(edge), direction_in);
        let insert_edge_txn = self.inner.txn(vec![op]);
        insert_edge_txn.execute().recv().expect("Txn failed");
    }

    pub fn add_empty_edge(&self, parent: usize, child: usize, direction_in: bool) {
        let op = OpType::InsertEdge(parent, child, None, direction_in);
        let insert_edge_txn = self.inner.txn(vec![op]);
        insert_edge_txn.execute().recv().expect("Txn failed");
    }

    pub fn connect<'t>(parent: &InternalNode<V, E>, child: E, direction_in: bool) {
        unsafe {
            AdjacencyList::connect(parent, child.id(), child, direction_in);
        }
    }

    pub fn iter_vertices<'t>(&'a self) -> IterRefEntry<'a, 't, 't, V, E> {
        let guard = unsafe { &*(&epoch::pin() as *const _) };
        self.inner.iter(guard)
    }

    pub fn find_vertex<'t>(&'t self, key: usize) -> Option<Atomic<InternalNode<'a, V, E>>> {
        let op = OpType::Find(key);
        let find_txn = self.inner.txn(vec![op]);
        let res = find_txn.execute();

        if let ReturnCode::Found(entry) = res.recv().unwrap() {
            Some(entry)
        } else {
            None
        }
    }

    pub fn delete_vertex<'t>(&'t self, key: usize) -> Option<Atomic<InternalNode<'a, V, E>>> {
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
        parent: usize,
        edge: usize,
        direction_in: bool,
    ) -> Result<(), ()> {
        let op = OpType::DeleteEdge(parent, edge, direction_in);
        let insertion_txn = self.inner.txn(vec![op]).execute();

        if let Ok(ReturnCode::Success) = insertion_txn.recv() {
            Ok(())
        } else {
            Err(())
        }
    }

    #[inline]
    fn is_directed(&self) -> bool {
        self.directed
    }

    #[inline]
    fn num_nodes(&self) -> usize {
        self.num_nodes
    }

    #[inline]
    fn num_edges(&self) -> usize {
        if self.directed {
            self.num_edges
        } else {
            self.num_edges * 2
        }
    }

    fn out_degree(&self, v: NodeId) -> usize {
        if v == 0 {
            // Our datastructure cannot handle id 0
            return 0;
        }

        if let Some(found) = self.cache.read().unwrap().get(&v) {
            found.out_edges.as_ref().unwrap().len()
        } else {
            panic!("Vertex not found");
        }
    }

    fn in_degree(&self, v: NodeId) -> usize {
        if v == 0 {
            // Our datastructure cannot handle id 0
            return 0;
        }

        if let Some(found) = self.cache.read().unwrap().get(&v) {
            found.in_edges.as_ref().unwrap().len()
        } else {
            panic!("Vertex not found");
        }
    }

    fn out_neigh(&self, v: NodeId) -> Range<E> {
        unimplemented!();
        // if v == 0 || v == 18446744073709551615 {
        //     // Our datastructure cannot handle id 0
        //     return Box::new(Vec::new().into_iter());
        // }

        // let guard = unsafe { &*(&epoch::pin() as *const _) };
        // if let Some(found) = self.cache.read().unwrap().get(&v) {
        //     // self.find_vertex(v) {
        //     let edges = found.out_edges.as_ref().unwrap();
        //     let picked_edges = edges.iter(guard).map(|e| *e.value().unwrap());
        //     // picked_edges
        //     Box::new(picked_edges)
        // } else {
        //     panic!("Vertex not found");
        // }
    }

    fn in_neigh(&self, v: NodeId) -> Range<E> {
        unimplemented!();

        // if v == 0 {
        //     // Our datastructure cannot handle id 0
        //     return Box::new(Vec::new().into_iter());
        // }

        // let guard = unsafe { &*(&epoch::pin() as *const _) };
        // if let Some(found) = self.cache.read().unwrap().get(&v) {
        //     // self.find_vertex(v) {
        //     let edges = found.in_edges.as_ref().unwrap();
        //     let picked_edges = edges.iter(guard).map(|e| *e.value().unwrap());
        //     // picked_edges
        //     Box::new(picked_edges)
        // } else {
        //     panic!("Vertex not found");
        // }
    }

    fn vertices(&self) -> Range<V> {
        unimplemented!();

        // let guard = unsafe { &*(&epoch::pin() as *const _) };
        // let iter = self.inner.iter(guard).map(|v| CustomNode(v.get().key));
        // Box::new(iter)
    }
}
#[cfg(test)]
mod graph_tests {
    use super::*;

    #[derive(Debug)]
    pub struct Vertex {
        id: usize,
        data: usize,
    }

    #[derive(Debug)]
    pub struct Edge {
        pub points_to: usize,
        pub extra_data: Option<usize>,
    }

    impl Node for Vertex {
        fn id(&self) -> usize {
            self.id
        }
    }

    impl Node for Edge {
        fn id(&self) -> usize {
            self.points_to
        }
    }

    #[test]
    fn test_vertex_insertion() {
        let graph = Graph::<Vertex, Edge>::directed();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        graph.add_vertex(Vertex{ id: 2, data: 345 });
        graph.add_vertex(Vertex{ id: 3, data: 678 });
        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].value().map(|v| v.data), Some(123));
        assert_eq!(vertices[1].value().map(|v| v.data), Some(345));
        assert_eq!(vertices[2].value().map(|v| v.data), Some(678));
    }

    #[test]
    fn test_edge_insertion() {
        let graph = Graph::<Vertex, Edge>::directed();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        graph.add_vertex(Vertex{ id: 2, data: 123 });

        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 0);
        graph.add_edge(1, Edge {
            points_to: 2,
            extra_data: Some(12345),
        }, true);
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 1);
    }
}