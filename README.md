# Proofs

A selection of formal proofs in [Coq](https://coq.inria.fr/).

[![Build status](https://github.com/stepchowfun/proofs/workflows/Continuous%20integration/badge.svg?branch=main)](https://github.com/stepchowfun/proofs/actions?query=branch%3Amain)

## Instructions

Make sure you have the dependencies listed below. Then you can run `make` to verify the proofs. You can also use `make lint` to invoke the linters. The build artifacts can be removed with `make clean`.

## Dependencies

The build system depends on the following:

- [GNU Make](https://www.gnu.org/software/make/) >= 3.79.1
- [Coq](https://coq.inria.fr/) >= 8.15.0

You also need the usual set of Unix tools, such as `echo`, `find`, etc.
