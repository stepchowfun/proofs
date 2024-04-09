# Admissibility graphs

An *admissibility graph* is a specification for which dependencies should be allowed between the components in a system. Admissibility graphs represent access policies such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. There are two types of directed edges:

- `X` *trusts* `Y`: informally, indicates that `X` can depend on `Y` and that `Y` can depend on any node that `X` can depend on.
- `X` *exports* `Y`: informally, indicates that `Y` can depend on `X` and that any node that can depend on `X` can also depend on `Y`.

To make those informal descriptions more precise, the following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
2. If `X` trusts `Y`, `X` is allowed to depend on `Y`.
3. If `X` exports `Y`, `Y` is allowed to depend on `X`.
4. If `X` trusts `Y` and `X` is allowed to depend on some `Z`, then `Y` is also allowed to depend on `Z`.
5. If `X` exports `Y` and some `Z` is allowed to depend on `X`, then `Z` is also allowed to depend on `Y`.
6. No other dependencies are allowed (i.e., the relation is defined inductively by the previous axioms).

If `X` trusts `Y` or `X` exports `Y`, we say `X` is a *parent* of `Y` and `Y` is a *child* of `X`. The *transpose* of an admissibility graph is the graph formed by swapping the edge types: `X` trusts `Y` becomes `X` exports `Y` and vice versa.

## Reflexive transitive closures

Some of the definitions and theorems below are stated in terms of the following reflexive transitive closures:

- If there is a (possibly empty) chain of trusts relationships from `X` to `Y`, we say `X` is *trusting* of `Y`.
- If there is a (possibly empty) chain of exports relationships from `X` to `Y`, we say `X` is *exporting* `Y`.
- If there is a (possibly empty) chain of parent-child relationships from `X` to `Y`, we say `X` is an *ancestor* of `Y` and `Y` is a *descendant* of `X`.

So the trusting and exporting relations are subsets of the ancestor relation.

It may be desirable to require the ancestor relation to be antisymmetric, but none of the theorems below rely on that.

## Derived notions

The notions of *trust* and *export* are primitive in the framework of admissibility graphs. Several derived notions are useful as well:

- `M` is a *module* if for all `X`, `Y`, and `Z`, if `M` is a parent of `X` and `Z` is a parent of `Y`, then `X` is an ancestor of `Y` implies `M` is an ancestor of `Z`.
- `X` is *encapsulated* within `M` if `M` is a module and an ancestor of `X` which is not exporting `X`.
- `X` is *sandboxed* within `M` if `M` is a module and an ancestor of `X` which is not trusting of `X`.

## Theorems

This development contains verified proofs of the following theorems:

**Theorem (duality).** Given an admissibility graph `G`, `G` allows `X` to depend on `Y` iff the transpose of `G` allows `Y` to depend on `X`.

**Theorem (reflection).** If two admissibility graphs with the same nodes have corresponding edges between all pairs of *distinct* nodes, then they allow the same dependencies. In other words, nothing is gained by having a node trust or export itself.

**Theorem (admission).** `X` is allowed to depend on `Y` iff there some `U` is trusting of `X` and some `V` is exporting `Y` and (`U` = `V` or there is an edge `U` trusts `V` or `V` exports `U`).

**Theorem (encapsulation).** If `X` is encapsulated within `M` and `Y` is allowed to depend on `X`, then `M` is an ancestor of `Y`.

> [!TIP]
> This theorem is intended to explain why encapsulation matters: informally, (1) the definition of `X` can be updated without affecting non-descendants `N` of `M`, and (2) if `X` has mutable state, then `N` need not be considered when reasoning about that state (e.g., to prove an invariant) unless `X` depends on `N`.

**Theorem (sandboxing).** If `X` is sandboxed within `M` and `X` is allowed to depend on `Y`, then `M` is an ancestor of `Y`.

> [!TIP]
> This theorem is intended to explain why sandboxing matters: informally, (1) the definition of any node `N` that isn't a descendant of `M` can be updated without affecting `X`, and (2) if `N` has mutable state, then `X` need not be considered when reasoning about that state (e.g., to prove an invariant) unless `N` depends on `X`.

## An algorithm to validate dependencies

We may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *N* be the number of nodes, let *E* be the total number of trusts and exports edges, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as the smallest graph satisfying:

- For every node `X` in the admissibility graph, the auxiliary graph has two nodes `Xₑ` and `Xᵢ` and an edge `Xₑ` ⭢ `Xᵢ`.
- For every edge `X` trusts `Y` in the admissibility graph, the auxiliary graph has edges `Xₑ` ⭢ `Yᵢ` and `Yₑ` ⭢ `Xₑ`.
- For every edge `X` exports `Y` in the admissibility graph, the auxiliary graph has edges `Yₑ` ⭢ `Xᵢ` and `Xₑ` ⭢ `Yₑ`.

Then, to check that a dependency `X` ⭢ `Y` is allowed, it suffices to check that `Yᵢ` is reachable from `Xₑ` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `Yᵢ` reachable from some source `Xₑ` (e.g., with a depth-first strategy), we discover all the nodes which that source is allowed to depend on, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `Xₑ`, we can discover all the dependencies allowed by the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash set) aren't allowed.
