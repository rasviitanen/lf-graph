mod adjlist;
mod lftt;
mod mdlist;
mod types;
mod graph;

// use crate::adjlist::AdjacencyList;
// use crate::adjlist::{IterRefEntry, Node};

// use crate::lftt::{OpType, ReturnCode};
// use std::sync::atomic::Ordering::{SeqCst};

// use crossbeam_epoch::{self as epoch, Atomic, Guard, Shared};
// use std::collections::BTreeMap;
// use std::sync::{Arc, RwLock};

// use crate::graph::{Range};
// use crate::types::*;

// #[derive(Clone, Copy)]
// pub struct CustomNode(usize);

// impl GraphNode for CustomNode {
//     #[inline]
//     fn node_id(&self) -> NodeId {
//         self.0
//     }
// }

// pub trait Edge<'a, T> {
//     fn key(&self) -> usize;
//     fn as_node(&self) -> Shared<'a, Node<'a, T, Self>>
//     where
//         Self: std::marker::Sized;
// }

// pub trait Vertex {
//     fn key(&self) -> usize;
// }

// unsafe impl Send for EdgeInfo {}
// unsafe impl Sync for EdgeInfo {}

// #[derive(Copy, Clone, Debug)]
// pub struct EdgeInfo {
//     // pub vertex_ref: RefEntry<'a, 'a, T, Self>,
//     pub node_id: NodeId,
//     pub weight: Option<Weight>,
// }

// impl WeightedEdge for EdgeInfo {
//     fn get_weight(&self) -> usize {
//         self.weight.expect("Weights must be assigned before used")
//     }

//     fn set_weight(&mut self, weight: usize) {
//         self.weight.replace(weight);
//     }
// }

// impl GraphNode for EdgeInfo {
//     fn node_id(&self) -> NodeId {
//         self.node_id
//     }
// }

// pub struct Graph<'a, T: Copy + Clone + Into<usize>> {
//     inner: AdjacencyList<'a, T, EdgeInfo>,
//     cache: Arc<RwLock<BTreeMap<NodeId, &'a Node<'a, T, E>>>>,
//     directed: bool,
//     num_nodes: usize,
//     num_edges: usize,
// }

// type E = EdgeInfo;

// impl<'a, T: 'a + Copy + Clone + Into<usize>> Graph<'a, T> {
//     pub fn directed() -> Self {
//         Self {
//             inner: AdjacencyList::new(),
//             cache: Arc::new(RwLock::new(BTreeMap::new())),
//             directed: true,
//             num_nodes: 0,
//             num_edges: 0,
//         }
//     }

//     pub fn undirected() -> Self {
//         Self {
//             inner: AdjacencyList::new(),
//             cache: Arc::new(RwLock::new(BTreeMap::new())),
//             directed: false,
//             num_nodes: 0,
//             num_edges: 0,
//         }
//     }

//     pub fn execute_ops<'t>(
//         &'t self,
//         ops: Vec<OpType<'a, T, E>>,
//     ) -> std::sync::mpsc::Receiver<ReturnCode<Atomic<Node<'a, T, E>>>> {
//         self.inner.txn(ops).execute()
//     }

//     pub fn add_vertex<'t>(
//         &'t self,
//         key: usize,
//         value: Option<T>,
//     ) -> Option<(usize, Atomic<Node<'a, T, E>>)> {
//         let op = OpType::Insert(key, value);
//         let insertion_txn = self.inner.txn(vec![op]).execute();

//         if let Ok(ReturnCode::Inserted(entry)) = insertion_txn.recv() {
//             Some((key, entry))
//         } else {
//             None
//         }
//     }

//     pub fn add_edge(&self, parent_id: usize, edge_info: E, direction_in: bool) {
//         let op = OpType::InsertEdge(parent_id, edge_info.node_id, Some(edge_info), direction_in);
//         let insert_edge_txn = self.inner.txn(vec![op]);
//         insert_edge_txn.execute().recv().expect("Txn failed");
//     }

//     pub fn add_empty_edge(&self, parent: usize, child: usize, direction_in: bool) {
//         let op = OpType::InsertEdge(parent, child, None, direction_in);
//         let insert_edge_txn = self.inner.txn(vec![op]);
//         insert_edge_txn.execute().recv().expect("Txn failed");
//     }

//     pub fn connect<'t>(parent: &Node<T, E>, child: E, direction_in: bool) {
//         unsafe {
//             AdjacencyList::connect(parent, child.node_id, child, direction_in);
//         }
//     }

//     pub fn iter_vertices<'t>(&'a self) -> IterRefEntry<'a, 't, 't, T, E> {
//         let guard = unsafe { &*(&epoch::pin() as *const _) };
//         self.inner.iter(guard)
//     }

//     pub fn find_vertex<'t>(&'t self, key: usize) -> Option<Atomic<Node<'a, T, E>>> {
//         let op = OpType::Find(key);
//         let find_txn = self.inner.txn(vec![op]);
//         let res = find_txn.execute();

//         if let ReturnCode::Found(entry) = res.recv().unwrap() {
//             Some(entry)
//         } else {
//             None
//         }
//     }

//     pub fn delete_vertex<'t>(&'t self, key: usize) -> Option<Atomic<Node<'a, T, E>>> {
//         let op = OpType::Delete(key);
//         let insertion_txn = self.inner.txn(vec![op]).execute();

//         if let Ok(ReturnCode::Deleted(entry)) = insertion_txn.recv() {
//             Some(entry)
//         } else {
//             None
//         }
//     }

//     pub fn delete_edge<'t>(
//         &'t self,
//         parent: usize,
//         edge: usize,
//         direction_in: bool,
//     ) -> Result<(), ()> {
//         let op = OpType::DeleteEdge(parent, edge, direction_in);
//         let insertion_txn = self.inner.txn(vec![op]).execute();

//         if let Ok(ReturnCode::Success) = insertion_txn.recv() {
//             Ok(())
//         } else {
//             Err(())
//         }
//     }

//     fn build_directed(num_nodes: usize, edge_list: &EdgeList) -> Self {
//         let mut graph = Graph::directed();
//         let guard = unsafe { &*(&epoch::pin() as *const _) };
//         for v in 1..num_nodes {
//             let inserted = graph.add_vertex(v, None);
//             graph
//                 .cache
//                 .write()
//                 .expect("Could not write")
//                 .insert(v, unsafe {
//                     inserted.unwrap().1.load(SeqCst, guard).deref()
//                 });
//         }

//         graph.num_nodes = num_nodes;

//         for (v, e, w) in edge_list {
//             if *v == 0 || *e == 0 {
//                 // Our datastructure cannot handle id 0
//                 continue;
//             }

//             let edge_info_ev = EdgeInfo {
//                 node_id: *v,
//                 weight: w.as_ref().map(|x| *x),
//             };

//             let edge_info_ve = EdgeInfo {
//                 node_id: *e,
//                 weight: w.as_ref().map(|x| *x),
//             };

//             graph.num_edges += 1;

//             if let (Some(en), Some(vn)) = (
//                 graph.cache.read().unwrap().get(e),
//                 graph.cache.read().unwrap().get(v),
//             ) {
//                 Self::connect(en, edge_info_ev, true);
//                 Self::connect(vn, edge_info_ve, false);
//             }
//         }

//         graph
//     }

//     fn build_undirected(num_nodes: usize, edge_list: &EdgeList) -> Self {
//         let mut graph = Graph::undirected();
//         let guard = unsafe { &*(&epoch::pin() as *const _) };

//         for v in 1..num_nodes {
//             let inserted = graph.add_vertex(v, None);
//             graph
//                 .cache
//                 .write()
//                 .expect("Could not write")
//                 .insert(v, unsafe {
//                     inserted.unwrap().1.load(SeqCst, guard).deref()
//                 });
//         }

//         graph.num_nodes = num_nodes;

//         for (v, e, w) in edge_list {
//             if *v == 0 || *e == 0 {
//                 // Our datastructure cannot handle id 0
//                 continue;
//             }

//             let edge_info_ev = EdgeInfo {
//                 node_id: *v,
//                 weight: w.as_ref().map(|x| *x),
//             };

//             let edge_info_ve = EdgeInfo {
//                 node_id: *e,
//                 weight: w.as_ref().map(|x| *x),
//             };

//             graph.num_edges += 1;

//             if let (Some(en), Some(vn)) = (
//                 graph.cache.read().unwrap().get(e),
//                 graph.cache.read().unwrap().get(v),
//             ) {
//                 Self::connect(en, edge_info_ev, false);
//                 Self::connect(vn, edge_info_ve, false);
//             }
//         }

//         graph
//     }

//     #[inline]
//     fn is_directed(&self) -> bool {
//         self.directed
//     }

//     #[inline]
//     fn num_nodes(&self) -> usize {
//         self.num_nodes
//     }

//     #[inline]
//     fn num_edges(&self) -> usize {
//         if self.directed {
//             self.num_edges
//         } else {
//             self.num_edges * 2
//         }
//     }

//     fn out_degree(&self, v: NodeId) -> usize {
//         if v == 0 {
//             // Our datastructure cannot handle id 0
//             return 0;
//         }

//         if let Some(found) = self.cache.read().unwrap().get(&v) {
//             found.out_edges.as_ref().unwrap().len()
//         } else {
//             panic!("Vertex not found");
//         }
//     }

//     fn in_degree(&self, v: NodeId) -> usize {
//         if v == 0 {
//             // Our datastructure cannot handle id 0
//             return 0;
//         }

//         if let Some(found) = self.cache.read().unwrap().get(&v) {
//             found.in_edges.as_ref().unwrap().len()
//         } else {
//             panic!("Vertex not found");
//         }
//     }

//     fn out_neigh(&self, v: NodeId) -> Range<E> {
//         if v == 0 || v == 18446744073709551615 {
//             // Our datastructure cannot handle id 0
//             return Box::new(Vec::new().into_iter());
//         }

//         let guard = unsafe { &*(&epoch::pin() as *const _) };
//         if let Some(found) = self.cache.read().unwrap().get(&v) {
//             // self.find_vertex(v) {
//             let edges = found.out_edges.as_ref().unwrap();
//             let picked_edges = edges.iter(guard).map(|e| *e.value().unwrap());
//             // picked_edges
//             Box::new(picked_edges)
//         } else {
//             panic!("Vertex not found");
//         }
//     }

//     fn in_neigh(&self, v: NodeId) -> Range<E> {
//         if v == 0 {
//             // Our datastructure cannot handle id 0
//             return Box::new(Vec::new().into_iter());
//         }

//         let guard = unsafe { &*(&epoch::pin() as *const _) };
//         if let Some(found) = self.cache.read().unwrap().get(&v) {
//             // self.find_vertex(v) {
//             let edges = found.in_edges.as_ref().unwrap();
//             let picked_edges = edges.iter(guard).map(|e| *e.value().unwrap());
//             // picked_edges
//             Box::new(picked_edges)
//         } else {
//             panic!("Vertex not found");
//         }
//     }

//     fn vertices(&self) -> Range<CustomNode> {
//         let guard = unsafe { &*(&epoch::pin() as *const _) };
//         let iter = self.inner.iter(guard).map(|v| CustomNode(v.get().key));
//         Box::new(iter)
//     }
// }
// #[cfg(test)]
// mod graph_tests {
//     use super::*;

//     #[test]
//     fn test_vertex_insertion() {
//         let graph = Graph::<usize>::directed();
//         graph.add_vertex(1, Some(123));
//         graph.add_vertex(2, Some(456));
//         graph.add_vertex(3, Some(789));
//         let vertices: Vec<_> =  graph.iter_vertices().collect();
//         assert_eq!(vertices[0].value(), Some(123));
//         assert_eq!(vertices[1].value(), Some(456));
//         assert_eq!(vertices[2].value(), Some(789));
//     }

//     #[test]
//     fn test_edge_insertion() {
//         let graph = Graph::<usize>::directed();
//         graph.add_vertex(1, Some(123));
//         graph.add_vertex(2, Some(456));

//         let vertices: Vec<_> =  graph.iter_vertices().collect();
//         assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 0);
//         graph.add_edge(1, EdgeInfo {
//             node_id: 2,
//             weight: None,
//         }, true);
//         assert_eq!(vertices[0].in_edges.as_ref().unwrap().len(), 1);
//     }
// }