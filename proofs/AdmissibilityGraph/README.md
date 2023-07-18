# Admissibility graphs

An *admissibility graph* is a specification for which dependencies should be allowed between the components in a system. Admissibility graphs represent access policies such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. There are two types of directed edges:

- `trusts(X, Y)`: informally, indicates that `X` can depend on `Y` and that `Y` can depend on any node that `X` can depend on.
- `exports(X, Y)`: informally, indicates that `Y` can depend on `X` and that any node that can depend on `X` can also depend on `Y`.

To make those informal descriptions more precise, the following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
2. If there is an edge `trusts(X, Y)`, `X` is allowed to depend on `Y`.
   - Also, if `X` is allowed to depend on some `Z`, then `Y` is also allowed to depend on `Z`.
3. If there is an edge `exports(X, Y)`, `Y` is allowed to depend on `X`.
   - Also, if some `Z` is allowed to depend on `X`, then `Z` is also allowed to depend on `Y`.
4. No other dependencies are allowed.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (admission).** `X` is allowed to depend on `Y` [iff](https://en.wikipedia.org/wiki/If_and_only_if) there is a path of `trusts` edges from `X` to some `U` and a path of `exports` edges from `Y` to some `V` and `U` = `V` or there is an edge `trusts(U, V)` or `exports(V, U)`.

**Theorem (duality).** Given two admissibility graphs `G₁` and `G₂` with the same set of nodes and edges such `trusts(X, Y)` in `G₁` implies `exports(X, Y)` in `G₂` and `exports(X, Y)` in `G₁` implies `trusts(X, Y)` in `G₂`, then if `G₁` allows some `X` to depend on some `Y`, `G₂` allows `Y` to depend on `X`.

**Theorem (transposition).** Given two admissibility graphs `G₁` and `G₂` with the same set of nodes and edges such that `trusted(X, Y)` in `G₁` is equivalent to `exports(X, Y)` in `G₂` and `exports(X, Y)` in `G₁` is equivalent to `trusts(X, Y)` in `G₂`, then `G₁` allows some `X` to depend on some `Y` iff `G₂` allows `Y` to depend on `X`.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *N* be the number of nodes, let *E* be the total number of `trusts` and `exports` edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the admissibility graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `trusts(X, Y)` in the admissibility graph, the auxiliary graph has edges `Xₑ` ⭢ `Yᵢ` and `Yₑ` ⭢ `Xₑ`.
- For every edge `exports(X, Y)` in the admissibility graph, the auxiliary graph has edges `Yₑ` ⭢ `Xᵢ` and `Xₑ` ⭢ `Yₑ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
