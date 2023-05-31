# Proxy graphs

A *proxy graph* is a specification for which dependencies should be allowed between components in a system. It can be understood as a more general and lower level form of [admissibility graph](https://github.com/stepchowfun/proofs/tree/main/proofs/AdmissibilityGraph). Proxy graphs can encode patterns such as encapsulation and sandboxing.

## Definition

The nodes are the components of the system. There are two types of directed edges:

1. Egress extension: X ⭢ₑ Y
2. Ingress extension: X ⭢ᵢ Y

The following axioms determine which dependencies are allowed.

1. Every node is allowed to depend on itself.
3. If there is an edge X ⭢ₑ Y and Y is allowed to depend on Z, then X is allowed to depend on Z.
2. If X is allowed to depend on Y and there is an edge Y ⭢ᵢ Z, then X is allowed to depend on Z.
4. No other dependencies are allowed.

Given an edge X ⭢ₑ Y, Y can be understood as a forward proxy in front of X. Likewise, given an edge X ⭢ᵢ Y, X can be understood as a reverse proxy in front of Y. These analogies are where the name "proxy graph" comes from.

## Theorems

This development contains verified proofs of the following two theorems:

**Theorem (admission).** X is allowed to depend on Y iff there is a path of ⭢ₑ edges from X to some Z followed by a path of Y ⭢ᵢ Z edges from Z to Y.

**Theorem (duality).** Given two proxy graphs G₁ and G₂ with the same set of nodes such that edges X ⭢ᵢ Y in G₁ imply edges Y ⭢ₑ X in G₂ and edges X ⭢ₑ Y in G₁ imply edges Y ⭢ᵢ X in G₂, then if G₁ allows some X to depend on some Y, G₂ allows Y to depend on X.