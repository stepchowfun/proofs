# Admissibility graphs

An *admissibility graph* is a specification for which dependencies should be allowed between the components in a system. Admissibility graphs represent access policies such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. There are two types of directed edges:

- `X trusts Y`: informally, indicates that `X` can depend on `Y` and that `Y` can depend on any node that `X` can depend on.
- `X exports Y`: informally, indicates that `Y` can depend on `X` and that any node that can depend on `X` can also depend on `Y`.

To make those informal descriptions more precise, the following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
2. If there is an edge `X trusts Y`, then `X` is allowed to depend on `Y`.
   - Also, if `X` is allowed to depend on some `Z`, then `Y` is allowed to depend on `Z`.
3. If there is an edge `X exports Y`, then `Y` is allowed to depend on `X`.
   - Also, if some `Z` is allowed to depend on `X`, then `Z` is allowed to depend on `Y`.
4. No other dependencies are allowed.

## Wooden admissibility graphs

If `X trusts Y` or `X exports Y`, we say `X` is a *parent* of `Y` and `Y` is a *child* of `X`. An important special case which enables additional reasoning power at the expense of flexibility is to limit each node to having at most one parent. The resulting structure is called a *wooden admissibility graph*.

## Closure concepts

Some of the theorems below are stated in terms of the following reflexive transitive closures:

- If there is a (possibly empty) chain of `trusts` relationships from `X` to `Y`, we say `X` is *trusting* of `Y`.
- If there is a (possibly empty) chain of `exports` relationships from `X` to `Y`, we say `X` is *exporting* `Y`.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (reflection).** Given two admissibility graphs with the same nodes that have matching edges between all pairs of *distinct* nodes, then they allow the same dependencies. In other words, nothing is gained by having a node trust or export itself.

**Theorem (admission).** `X` is allowed to depend on `Y` [iff](https://en.wikipedia.org/wiki/If_and_only_if) there some `U` is trusting of `X` and some `V` is exporting `Y` and `U` = `V` or there is an edge `U trusts V` or `V exports U`.

**Theorem (duality).** Given two admissibility graphs `G₁` and `G₂` with the same set of nodes and edges such `X trusts Y` in `G₁` implies `X exports Y` in `G₂` and `X exports Y` in `G₁` implies `X trusts Y` in `G₂`, then if `G₁` allows some `X` to depend on some `Y`, `G₂` allows `Y` to depend on `X`.

**Theorem (encapsulation).** In a wooden admissibility graph in which `X trusts Y`, `Z` is allowed to depend on `Y` iff `X` is trusting of `Z` or (`X exports Y` and `Z` is allowed to depend on `X`) or (`Y` exports some `W` and `W` is trusting of `Z`).

**Theorem (sandboxing).** In a wooden admissibility graph in which `X exports Y`, `Y` is allowed to depend on `Z` iff `X` is exporting `Z` or (`X trusts Y` and `X` is allowed to depend on `Z`) or (`Y` trusts some `W` and `W` is exporting `Z`).

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *N* be the number of nodes, let *E* be the total number of `trusts` and `exports` edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the admissibility graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X trusts Y` in the admissibility graph, the auxiliary graph has edges `Xₑ` ⭢ `Yᵢ` and `Yₑ` ⭢ `Xₑ`.
- For every edge `X exports Y` in the admissibility graph, the auxiliary graph has edges `Yₑ` ⭢ `Xᵢ` and `Xₑ` ⭢ `Yₑ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
