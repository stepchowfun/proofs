# Proxy graphs

A *proxy graph* is a specification for which dependencies should be admitted between components in a system. It can be understood as a more general and lower level form of [admissibility graph](https://github.com/stepchowfun/proofs/tree/main/proofs/AdmissibilityGraph). Proxy graphs can encode patterns such as encapsulation and sandboxing.

The nodes are the components of the system. There are two types of directed edges:

1. Egress extension: X ⭢ₑ Y
2. Ingress extension: X ⭢ᵢ Y

The following axioms determine which dependencies are admitted.

1. Every node can depend on itself.
3. If X ⭢ₑ Y and Y can depend on Z, then X can depend on Z.
2. If X can depend on Y and Y ⭢ᵢ Z, then X can depend on Z.
4. No other dependencies are admitted.
