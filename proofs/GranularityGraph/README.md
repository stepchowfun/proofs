# Granularity graphs

This directory presents an original notion we call the *granularity graph*.

Informally speaking, a granularity graph is a graph in which nodes can be
"unfolded" in a sense to reveal further graph structure, the nodes of which can
themselves be unfolded, and so on.

In the other direction, a granularity graph is organized into subgraphs which
can be "folded" into single nodes, resulting in a coarser view of the graph
which can be folded further, until ultimately the entire graph has been folded
into a single *root* node.

Granularity graphs permit sharing of substructure as long as such sharing
interacts coherently with folding/unfolding.

## Variations

- Granularity graphs are directed by default, but can be made undirected by
  postulating the following axiom:

  ```coq
  Axiom symmetry : forall g n1 n2, edge g n1 n2 -> edge g n2 n1.
  ```
- Granularity graphs by default do not allow for cyclic unfolding in which
  multiple nodes are mutually contained within each other, although such models
  can be admitted by removing the `containment` axiom.
