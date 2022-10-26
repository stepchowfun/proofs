# Context graphs

This directory introduces an original notion we call *context graph*.
Informally speaking, a context graph is a graph in which each node can be
"exploded" in a sense to reveal further graph structure, the nodes of which can
themselves be exploded, and so on. In the other direction, a context graph is
organized into subgraphs which can be "collapsed" into individual nodes,
resulting in a coarser view of the graph that can be further collapsed, until
ultimately the entire graph has been collapsed into a single *root* node.
Context graphs support sharing of substructure in the sense that an individual
node may show up in the exploded subgraphs of multiple nodes, although an
additional axiom can be postulated to forbid such sharing. Context graphs by
default do not allow for cyclic exploding, although such models can be admitted
by removing the "antisymmetry" axiom.
