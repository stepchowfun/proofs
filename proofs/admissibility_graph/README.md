# Admissibility graphs

An *admissibility graph* is a specification for which dependencies should be allowed between the components in a system. Admissibility graphs represent access policies such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. There are two types of directed edges:

- `X` *trusts* `Y`: informally, indicates that `X` can depend on `Y` and that `Y` can depend on any node that `X` can depend on.
- `X` *exports* `Y`: informally, indicates that `Y` can depend on `X` and that any node that can depend on `X` can also depend on `Y`.

To make those informal descriptions more precise, the following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
2. If `X` trusts `Y`:
   - `X` is allowed to depend on `Y`.
   - If `X` is allowed to depend on some `Z`, then `Y` is also allowed to depend on `Z`.
3. If `X` exports `Y`:
   - `Y` is allowed to depend on `X`.
   - If some `Z` is allowed to depend on `X`, then `Z` is also allowed to depend on `Y`.
4. No other dependencies are allowed.

If `X` trusts `Y` or `X` exports `Y`, we say `X` is a *parent* of `Y` and `Y` is a *child* of `X`. The *transpose* of an admissibility graph is the graph formed by swapping the edge types: `X` trusts `Y` becomes `X` exports `Y` and vice versa.

## Closure concepts

Some of the definitions and theorems below are stated in terms of the following reflexive transitive closures:

- If there is a (possibly empty) chain of trusts relationships from `X` to `Y`, we say `X` is *trusting* of `Y`.
- If there is a (possibly empty) chain of exports relationships from `X` to `Y`, we say `X` is *exporting* `Y`.
- If there is a (possibly empty) chain of parent-child relationships from `X` to `Y`, we say `X` is an *ancestor* of `Y`.

So the trusting and exporting relations are subsets of the ancestor relation.

## Modularity concepts

The following definitions formalize the idea that a *module* is self-contained.

- `X` *covers* `Y`: if `Y` is an ancestor of `Z` and `W` is a parent of `Z`, then `X` is an ancestor of `W`.
- `X` is a *module*: if `X` is a parent of `Y`, `X` covers `Y`.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (duality).** Given an admissibility graph `G`, `G` allows `X` to depend on `Y` iff the transpose of `G` allows `Y` to depend on `X`.

**Theorem (reflection).** If two admissibility graphs with the same nodes have corresponding edges between all pairs of *distinct* nodes, then they allow the same dependencies. In other words, nothing is gained by having a node trust or export itself.

**Theorem (admission).** `X` is allowed to depend on `Y` iff there some `U` is trusting of `X` and some `V` is exporting `Y` and (`U` = `V` or there is an edge `U` trusts `V` or `V` exports `U`).

**Theorem (coverage extension).** If `X` is an ancestor of `Y` and `U` is an ancestor of `V`, then `X` covers `V` if `Y` covers `U`.

**Theorem (encapsulation).** If `M` is a module and an ancestor of `X` and if some `Y` is allowed to depend on `X`, then either `M` is an ancestor of `Y` or `M` is exporting `X`.

**Theorem (sandboxing).** If `M` is a module and an ancestor of `X` and if `X` is allowed to depend on some `Y`, then either `M` is an ancestor of `Y` or `M` is trusting of `X`.

Some of these theorems are direct consequences of more general theorems which are proven as well.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *N* be the number of nodes, let *E* be the total number of trusts and exports edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the admissibility graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X` trusts `Y` in the admissibility graph, the auxiliary graph has edges `Xₑ` ⭢ `Yᵢ` and `Yₑ` ⭢ `Xₑ`.
- For every edge `X` exports `Y` in the admissibility graph, the auxiliary graph has edges `Yₑ` ⭢ `Xᵢ` and `Xₑ` ⭢ `Yₑ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't allowed.
