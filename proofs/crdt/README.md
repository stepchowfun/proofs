# Conflict-free replicated data types

A *conflict-free replicated data type* (*CRDT*) is an abstract data type supporting replication in such a way that replicas can be modified independently and later reconciled with strong eventual consistency. Broadly speaking, there are two main formulations of this concept: state-based CRDTs and operation-based CRDTs. The files in this directory develop the mathematical theory of both approaches including proofs of strong convergence and the equivalence of the two formulations.
