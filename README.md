# Proofs

[![Build status](https://github.com/stepchowfun/proofs/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/stepchowfun/proofs/actions?query=branch%3Amain)

This is my personal repository of formally verified mathematics, including results from category theory, type theory, domain theory, etc., and some original research. All the proofs are verified using the [Lean theorem prover](https://lean-lang.org/) or the [Rocq proof assistant](https://rocq-prover.org/).

If you want to set up your own repository of formally verified mathematics, you can simply fork this repository and replace the contents of the [`proofs_lean`](https://github.com/stepchowfun/proofs/tree/main/proofs_lean)<!-- [dir:proofs_lean] --> or the [`proofs_rocq`](https://github.com/stepchowfun/proofs/tree/main/proofs_rocq)<!-- [dir:proofs_rocq] --> directories with your own proofs. Setting up a Rocq project from scratch isn't particularly straightforward, so this scaffolding can save you time.

If you're new to Lean, there are good educational resources available [here](https://lean-lang.org/learn/).

If you're new to Rocq, start with the tutorial [here](https://github.com/stepchowfun/proofs/tree/main/proofs_rocq/tutorial)<!-- [dir:proofs_rocq/tutorial] -->. I recommend [Software Foundations](https://softwarefoundations.cis.upenn.edu/) and [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) for further learning.

## Instructions

Make sure you have the dependencies listed below. Then you can run `lake build` to verify the Lean proofs or `make` to verify the Rocq proofs. If you change anything, you can run those commands again to incrementally verify the affected proofs. The build artifacts can be removed with `lake clean` (for Lean) or `make clean` (for Rocq).

To write proofs, you'll want to use an IDE that supports interactive theorem proving. For Lean, use the [Lean 4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extension for [Visual Studio Code](https://code.visualstudio.com/). For Rocq, my recommendation is [VsRocq](https://github.com/rocq-prover/vsrocq), which is also a Visual Studio Code extension.

### Dependencies

You'll need the following:

- [Lean](https://lean-lang.org/)
  - Make sure to update your [`PATH`](https://en.wikipedia.org/wiki/PATH_\(variable\)) to include the location of the `lake` binary.
- [Rocq](https://rocq-prover.org/)
  - Make sure to update your `PATH` to include the location of the `rocq` binary.
- [GNU Make](https://www.gnu.org/software/make/)
  - You also need these common Unix tools: `cp`, `find`, and `rm`. If you have `make`, you probably already have those other programs too.
