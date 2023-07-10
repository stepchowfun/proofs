# Proxy graphs

A *proxy graph* is a specification for which dependencies should be allowed between components in a system. Proxy graphs can encode patterns such as encapsulation and sandboxing, and they can be understood as a generalization of [admissibility graphs](https://github.com/stepchowfun/proofs/tree/main/proofs/AdmissibilityGraph).

## Definition

The nodes are the components of the system. The edges are directed and indicate member ⭢ group relationships between nodes.

In addition to the usual graph structure, a proxy graph is equipped with two predicates on nodes:

1. `egress(X)` indicates whether node `X` allows egress through the groups containing it.
2. `ingress(X)` indicates whether node `X` allows ingress through the groups containing it.

The following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
2. If `egress(X)` holds and there is an edge `X` ⭢ `Y` and `Y` is allowed to depend on `Z`, then `X` is allowed to depend on `Z`.
3. If `ingress(X)` holds and there is an edge `X` ⭢ `Y` and `Z` is allowed to depend on `Y`, then `Z` is allowed to depend on `X`.
4. No other dependencies are allowed.

Given an edge `X` ⭢ `Y`, `egress(X)` means that `Y` can be understood as a forward proxy in front of `X`, and `ingress(X)` means that `Y` can be understood as reverse proxy in front of `X`. These analogies are where the name "proxy graph" comes from.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (admission).** `X` is allowed to depend on `Y` iff there is a path of edges from `X` to some `Z` in which `egress` holds for the source of every edge followed by a path of edges from `Z` to `Y` in which `ingress` holds for the target of every edge.

**Theorem (duality).** Given two proxy graphs `G₁` and `G₂` with the same set of nodes and edges such `egress(X)` in `G₁` implies `ingress(X)` in `G₂` and `ingress(X)` in `G₁` implies `egress(X)` in `G₂`, then if `G₁` allows some `X` to depend on some `Y`, `G₂` allows `Y` to depend on `X`.

**Theorem (transposition).** Given two proxy graphs `G₁` and `G₂` with the same set of nodes and edges such that `egress(X)` in `G₁` is equivalent to `ingress(X)` in `G₂` and `ingress(X)` in `G₁` is equivalent to `egress(X)` in `G₂`, then `G₁` allows some `X` to depend on some `Y` [iff](https://en.wikipedia.org/wiki/If_and_only_if) `G₂` allows `Y` to depend on `X`.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given proxy graph containing the same nodes. Let *N* be the number of nodes, let *E* be the number of edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the proxy graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X` ⭢ `Y` in the proxy graph such that `egress(X)` holds, the auxiliary graph has an edge `Xₑ` ⭢ `Yₑ`.
- For every edge `X` ⭢ `Y` in the proxy graph such that `ingress(Y)` holds, the auxiliary graph has an edge `Xᵢ` ⭢ `Yᵢ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the proxy graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
