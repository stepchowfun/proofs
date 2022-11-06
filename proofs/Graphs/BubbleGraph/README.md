# Bubble graphs

This directory presents an original notion we call the *bubble graph*.

A bubble graph is a rooted graph with a set of subgraphs which are also rooted.

## Variations

- Bubble graphs are directed by default, but can be made undirected by postulating
  the following axiom:

  ```coq
  Axiom symmetry : forall n1 n2, edge n1 n2 -> edge n2 n1.
  ```
