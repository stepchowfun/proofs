# Proxy graphs

A *proxy graph* is a specification for which dependencies should be allowed between components in a system. Proxy graphs can encode patterns such as encapsulation and sandboxing, and they can be understood as a generalization of [admissibility graphs](https://github.com/stepchowfun/proofs/tree/main/proofs/AdmissibilityGraph).

## Definition

The nodes are the components of the system. There are two types of directed edges:

1. Egress extension: `X` ⭢ₑ `Y`
2. Ingress extension: `X` ⭢ᵢ `Y`

The following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
3. If there is an edge `X` ⭢ₑ `Y` and `Y` is allowed to depend on `Z`, then `X` is allowed to depend on `Z`.
2. If `X` is allowed to depend on `Y` and there is an edge `Y` ⭢ᵢ `Z`, then `X` is allowed to depend on `Z`.
4. No other dependencies are allowed.

Given an edge `X` ⭢ₑ `Y`, `Y` can be understood as a forward proxy in front of `X`. Likewise, given an edge `X` ⭢ᵢ `Y`, `X` can be understood as a reverse proxy in front of `Y`. These analogies are where the name "proxy graph" comes from.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (admission).** `X` is allowed to depend on `Y` iff there is a path of ⭢ₑ edges from `X` to some `Z` followed by a path of ⭢ᵢ edges from `Z` to `Y`.

**Theorem (duality).** Given two proxy graphs `G₁` and `G₂` with the same set of nodes such that edges `X` ⭢ᵢ `Y` in `G₁` imply edges `Y` ⭢ₑ `X` in `G₂` and edges `X` ⭢ₑ `Y` in `G₁` imply edges `Y` ⭢ᵢ `X` in `G₂`, then if `G₁` allows some `X` to depend on some `Y`, `G₂` allows `Y` to depend on `X`.

**Theorem (transposition).** Given two proxy graphs `G₁` and `G₂` with the same set of nodes such that edges `X` ⭢ᵢ `Y` in `G₁` correspond to edges `Y` ⭢ₑ `X` in `G₂` and edges `X` ⭢ₑ `Y` in `G₁` correspond to edges `Y` ⭢ᵢ `X` in `G₂`, then `G₁` allows some `X` to depend on some `Y` [iff](https://en.wikipedia.org/wiki/If_and_only_if) `G₂` allows `Y` to depend on `X`.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given proxy graph containing the same nodes. Let *N* be the number of nodes, let *E* be the number of edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the proxy graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X` ⭢ₑ `Y` in the proxy graph, the auxiliary graph has an edge `Xₑ` ⭢ `Yₑ`.
- For every edge `X` ⭢ᵢ `Y` in the proxy graph, the auxiliary graph has an edge `Xᵢ` ⭢ `Yᵢ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the proxy graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
