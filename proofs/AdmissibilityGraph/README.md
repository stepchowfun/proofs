# Admissibility graphs

An *admissibility graph* is a specification for which dependencies should be allowed between components in a system. Admissibility graphs can encode access policies such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. The edges are directed and indicate member ⭢ group relationships between nodes.

In addition to the usual graph structure, an admissibility graph is equipped with two predicates on nodes:

1. `trusted(X)`: informally, indicates whether node `X` inherits egress access from the groups containing it
2. `exported(X)`: informally, indicates whether node `X` inherits ingress access from the groups containing it

The following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
1. If there is an edge `X` ⭢ `Y`, `X` is allowed to depend on `Y`.
1. If there is an edge `X` ⭢ `Y`, `Y` is allowed to depend on `X`.
2. If there is an edge `X` ⭢ `Y` and `trusted(X)` holds and `Y` is allowed to depend on `Z`, then `X` is allowed to depend on `Z`.
3. If there is an edge `X` ⭢ `Y` and `exported(X)` holds and `Z` is allowed to depend on `Y`, then `Z` is allowed to depend on `X`.
4. No other dependencies are allowed.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (admission).** `X` is allowed to depend on `Y` iff there is a path of edges from `X` to some `U` in which the source of every edge is `trusted` and a path of edges from `Y` to some `V` in which the source of every edge is `exported` and `U` = `V` or there is an edge `U` ⭢ `V` or `V` ⭢ `U`.

**Theorem (duality).** Given two admissibility graphs `G₁` and `G₂` with the same set of nodes and edges such `trusted(X)` in `G₁` implies `exported(X)` in `G₂` and `exported(X)` in `G₁` implies `trusted(X)` in `G₂`, then if `G₁` allows some `X` to depend on some `Y`, `G₂` allows `Y` to depend on `X`.

**Theorem (transposition).** Given two admissibility graphs `G₁` and `G₂` with the same set of nodes and edges such that `trusted(X)` in `G₁` is equivalent to `exported(X)` in `G₂` and `exported(X)` in `G₁` is equivalent to `trusted(X)` in `G₂`, then `G₁` allows some `X` to depend on some `Y` [iff](https://en.wikipedia.org/wiki/If_and_only_if) `G₂` allows `Y` to depend on `X`.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *N* be the number of nodes, let *E* be the number of edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the admissibility graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X` ⭢ `Y` in the admissibility graph, the auxiliary graph has edges `Xₑ` ⭢ `Yᵢ` and `Yₑ` ⭢ `Xᵢ`.
  - If `trusted(X)` holds, the auxiliary graph also has an edge `Xₑ` ⭢ `Yₑ`.
  - If `exported(X)` holds, the auxiliary graph also has an edge `Yᵢ` ⭢ `Xᵢ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
