# Granularity graphs

This directory presents an original notion we call *granularity graph*.

Informally speaking, a granularity graph is a graph in which nodes can be
"unfolded" in a sense to reveal further graph structure, the nodes of which can
themselves be unfolded, and so on.

In the other direction, a granularity graph is organized into subgraphs which
can be "folded" into single nodes, resulting in a coarser view of the graph
which can be folded further, until ultimately the entire graph has been folded
into a single *root* node.

Granularity graphs permit sharing of substructure, but any such sharing must be
made explicit: if two nodes share any substructure, there must be an edge
between them.

## Variations

- Granularity graphs are directed by default, but can be made undirected by
  postulating a symmetry axiom.
- Granularity graphs by default do not allow for cyclic unfolding in which
  multiple nodes are mutually contained within each other, although such models
  can be admitted by removing the antisymmetry axiom.
- Sharing of substructure can be forbidden with an additional axiom.
