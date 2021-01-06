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

use crate::adjlist::AdjacencyList;
use crate::adjlist::{IterRefEntry, RefEntry, Node as InternalNode};

use crate::lftt::{OpType, ReturnCode};
use std::sync::atomic::Ordering::{SeqCst};

use crossbeam_epoch::{self as epoch, Atomic, Guard, Shared};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use crate::types::*;

pub trait Node {
    fn id(&self) -> usize;
}

struct GraphTxn<'a, 't, V: Node, E: Node>{
    graph: &'t Graph<'a, V, E>,
    operations: Vec<OpType<'a, V, E>>
}

impl<'a: 't, 't, V: Node, E: Node> GraphTxn<'a, 't, V, E> {
    pub fn new(graph: &'t Graph<'a, V, E>) -> Self {
        Self {
            graph,
            operations: Vec::new(),
        }
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn insert(&mut self, v: V) -> &mut Self {
        self.operations.push(OpType::Insert(v.id(), Some(v)));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn delete_vertex(&mut self, key: usize) -> &mut Self {
        self.operations.push(OpType::Delete(key));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn find_vertex(&mut self, key: usize) -> &mut Self {
        self.operations.push(OpType::Find(key));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn insert_edge(&mut self, vertex_key: usize, edge_key: usize, edge_info: Option<E>) -> &mut Self {
        self.operations.push(OpType::InsertEdge(vertex_key, edge_key, edge_info, true));
        self
    }

    #[must_use = "Transaction does nothing unless executed"]
    pub fn delete_edge(&mut self, vertex_key: usize, edge_key: usize) -> &mut Self {
        self.operations.push(OpType::DeleteEdge(vertex_key, edge_key, true));
        self
    }

    pub fn execute(
        &mut self,
    ) -> std::sync::mpsc::Receiver<ReturnCode<RefEntry<'a, 't, V, E>>> {
        self.graph.inner.txn(self.operations.drain(0..).collect()).execute()
    }
}

pub struct Graph<'a, V: Node, E: Node> {
    inner: AdjacencyList<'a, V, E>,
}

impl<'a, V: 'a + Node, E: Node> Graph<'a, V, E> {
    pub fn new() -> Self {
        Self {
            inner: AdjacencyList::new(),
        }
    }

    pub fn add_vertex<'t>(
        &'t self,
        value: V,
    ) -> Option<(usize, RefEntry<'a, 't, V, E>)> {
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

    pub fn find_vertex<'t>(&'t self, key: usize) -> Option<RefEntry<'a, 't, V, E>> {
        let op = OpType::Find(key);
        let find_txn = self.inner.txn(vec![op]);
        let res = find_txn.execute();

        if let ReturnCode::Found(entry) = res.recv().unwrap() {
            Some(entry)
        } else {
            None
        }
    }

    pub fn delete_vertex<'t>(&'t self, key: usize) -> Option<RefEntry<'a, 't, V, E>> {
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
        let graph = Graph::<Vertex, Edge>::new();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        graph.add_vertex(Vertex{ id: 2, data: 345 });
        graph.add_vertex(Vertex{ id: 3, data: 678 });
        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].value().map(|v| v.data), Some(123));
        assert_eq!(vertices[1].value().map(|v| v.data), Some(345));
        assert_eq!(vertices[2].value().map(|v| v.data), Some(678));
    }

    #[test]
    fn test_find_vertex() {
        let graph = Graph::<Vertex, Edge>::new();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        let vertex = graph.find_vertex(1);
        assert!(vertex.is_some());
        assert_eq!(vertex.unwrap().value().map(|v| v.data), Some(123));
    }

    #[test]
    fn test_delete_vertex() {
        let graph = Graph::<Vertex, Edge>::new();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        let vertex = graph.find_vertex(1);
        assert!(vertex.is_some());
        assert_eq!(vertex.unwrap().value().map(|v| v.data), Some(123));
        let deleted = graph.delete_vertex(1);
        assert_eq!(deleted.unwrap().value().map(|v| v.data), Some(123));
        let vertex = graph.find_vertex(1);
        assert!(vertex.is_none());
    }

    #[test]
    fn test_edge_insertion() {
        let graph = Graph::<Vertex, Edge>::new();
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


    #[test]
    fn test_in_neigh() {
        let graph = Graph::<Vertex, Edge>::new();
        graph.add_vertex(Vertex{ id: 1, data: 123 });
        graph.add_vertex(Vertex{ id: 2, data: 123 });

        let vertices: Vec<_> =  graph.iter_vertices().collect();
        assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 0);
        graph.add_edge(1, Edge {
            points_to: 2,
            extra_data: Some(12345),
        }, true);


        let in_neigh = graph.in_neigh(&vertices[0]).collect::<Vec<_>>();
        assert_eq!(in_neigh[0].points_to, 2);
    }


    #[test]
    fn test_txn_simple() {
        let graph = Graph::<Vertex, Edge>::new();
        GraphTxn::new(&graph)
            .insert(Vertex { id: 1, data: 123 } )
            .insert(Vertex { id: 2, data: 456 } )
            .insert(Vertex { id: 3, data: 789 } )
            .execute();

        let result = GraphTxn::new(&graph)
            .find_vertex(1)
            .find_vertex(2)
            .find_vertex(3)
            .execute();

        for i in 1..=3 {
            if let Ok(ReturnCode::Found(v)) = result.recv() {
                assert_eq!(v.value().unwrap().id, i);
            } else {
                panic!("Could not find inserted vertices");
            }
        }
    }

    #[test]
    fn test_threaded_txn_simple() {
        let graph = Arc::new(Graph::<Vertex, Edge>::new());

        let graph_clone = Arc::clone(&graph);
        let tx1 = std::thread::spawn(move || {
            GraphTxn::new(&graph_clone)
                .insert(Vertex { id: 1, data: 123 } )
                .insert(Vertex { id: 2, data: 456 } )
                .insert(Vertex { id: 3, data: 789 } )
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
                assert_eq!(v.value().unwrap().id, i);
            } else {
                panic!("Could not find inserted vertices, {:?}", i);
            }
        }
    }

    #[test]
    fn test_multiple_txn_simple() {
        let graph = Graph::<Vertex, Edge>::new();

        GraphTxn::new(&graph)
            .insert(Vertex { id: 1, data: 1 } )
            .insert(Vertex { id: 2, data: 2 } )
            .execute();

        GraphTxn::new(&graph)
                .insert(Vertex { id: 3, data: 3 } )
                .insert(Vertex { id: 4, data: 4 } )
                .execute();

        GraphTxn::new(&graph)
                .insert(Vertex { id: 5, data: 5 } )
                .insert(Vertex { id: 6, data: 6 } )
                .execute();

        GraphTxn::new(&graph)
                .insert(Vertex { id: 7, data: 7 } )
                .insert(Vertex { id: 8, data: 8 } )
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
                assert_eq!(v.value().unwrap().id, i);
            } else {
                panic!("Could not find inserted vertices, {:?}", i);
            }
        }
    }
}