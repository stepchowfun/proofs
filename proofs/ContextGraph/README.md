# Context graphs

This directory introduces an original notion we call *context graph*.

Informally speaking, a context graph is a graph in which each node can be
"exploded" in a sense to reveal further graph structure, the nodes of which can
themselves be exploded, and so on.

In the other direction, a context graph is organized into subgraphs which can
be "collapsed" into single nodes, resulting in a coarser view of the graph which
can be further collapsed, until ultimately the entire graph has been collapsed
into a single *root* node.

Context graphs are directed by default, but can be made undirected by
introducing a symmetry axiom. Context graphs support sharing of substructure in
the sense that an individual node may show up in the exploded subgraphs of
multiple nodes, although an additional axiom can be postulated to forbid such
sharing. Context graphs by default do not allow for cyclic exploding in which
distinct nodes are mutually contained within each other, although such models
can be admitted by removing the antisymmetry axiom.

Each edge of a context graph is associated with a particular node called its
*context*. The context of an edge is the node that needs to be exploded to
reveal that edge. All the edges sharing a context can be considered to belong
to the same collapsible subgraph.

Context graphs support two notions of reachability from one node to another:

- `B` is *horizontally reachable* from `A` in context `C` when there is a
  (possibly empty) path from `A` to `B` consisting only of edges in context `C`.
- `B` is *vertically reachable* from `A` when `A` and `B` are the same node or
  there is a node `C` which is horizontally reachable from `A` in context `A`
  and `B` is vertically reachable from `C`.

Informally speaking, vertical reachability is allowed to explode nodes to reach
the target (or, equivalently, collapse subgraphs to reach the source), whereas
horizontal reachability is not.

Every node is required to be vertically reachable from the root.