# Context graphs

This directory presents an original notion we call *context graph*.

Informally speaking, a context graph is a graph in which each node can be
"unfolded" in a sense to reveal further graph structure, the nodes of which can
themselves be unfolded, and so on.

In the other direction, a context graph is organized into subgraphs which can
be "folded" into single nodes, resulting in a coarser view of the graph which
can be further folded, until ultimately the entire graph has been folded into
a single *root* node.

Context graphs permit sharing of substructure, but any such sharing must be
made explicit: if two nodes share any substructure, there must be an edge
between them.

Each edge of a context graph is associated with a particular node called its
*context*. The context of an edge is the node that unfolded to reveal that
edge. All the edges sharing a context can be considered to belong to the same
foldable subgraph.

Context graphs support two notions of reachability from one node to another:

- `B` is *horizontally reachable* from `A` in context `C` when there is a
  (possibly empty) path from `A` to `B` consisting only of edges in context
  `C`.
- `B` is *vertically reachable* from `A` when `A` and `B` are the same node or
  there is a node `C` which is horizontally reachable from `A` in context `A`
  and `B` is vertically reachable from `C`.

Informally speaking, vertical reachability is allowed to unfold nodes to reach
the target (or, equivalently, fold subgraphs to reach the source), whereas
horizontal reachability is not.

Every node is required to be vertically reachable from the root.

## Variations

- Context graphs are directed by default, but can be made undirected by
  postulating a symmetry axiom.
- Context graphs by default do not allow for cyclic unfolding in which multiple
  nodes are mutually contained within each other, although such models can be
  admitted by removing the antisymmetry axiom.
- Sharing of substructure can be forbidden with an additional axiom.
