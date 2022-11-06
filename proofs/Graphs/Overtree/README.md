# Overtrees

This directory presents an original notion we call the *overtree*.

An overtree is locally structured like an arbitrary graph but globally
structured like a directed, rooted tree.

## Variations

- Overtrees are directed by default, but can be made undirected by postulating
  the following axiom:

  ```coq
  Axiom symmetry : forall n1 n2, edge n1 n2 -> edge n2 n1.
  ```
