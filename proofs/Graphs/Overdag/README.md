# Overdags

This directory presents an original notion we call the *overdag*.

An overdag is locally structured like a graph but globally structured like a
directed, acyclic graph.

## Variations

- Overdags are directed by default, but can be made undirected by postulating
  the following axiom:

  ```coq
  Axiom symmetry : forall n1 n2, edge n1 n2 -> edge n2 n1.
  ```
