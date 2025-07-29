# Proofs

[![Build status](https://github.com/stepchowfun/proofs/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/stepchowfun/proofs/actions?query=branch%3Amain)

This is my personal repository of formally verified mathematics, including results from category theory, type theory, domain theory, etc., and some original research. All the proofs are verified using the [Rocq proof assistant](https://rocq-prover.org/).

If you want to set up your own repository of formally verified mathematics, you can simply fork this repository and replace the contents of the [`proofs`](https://github.com/stepchowfun/proofs/tree/main/proofs)<!-- [dir:proofs] --> directory with your own proofs. Setting up a Rocq project from scratch isn't particularly straightforward, so this scaffolding can save you time.

If you're new to Rocq, start with the tutorial [here](https://github.com/stepchowfun/proofs/tree/main/proofs/tutorial)<!-- [dir:proofs/tutorial] -->. I recommend [Software Foundations](https://softwarefoundations.cis.upenn.edu/) and [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) for further learning.

## Instructions

Make sure you have the dependencies listed below. Then you can run `make` in this directory to verify all the proofs. If you change anything, you can run `make` again to incrementally verify the affected proofs. The build artifacts can be removed with `make clean`.

To write proofs, you'll want to use an IDE that supports interactive theorem proving. My recommendation is [VsRocq](https://github.com/rocq-prover/vsrocq), which is a plugin for [Visual Studio Code](https://code.visualstudio.com/).

### Dependencies

You'll need the following:

- [Rocq](https://rocq-prover.org/) >= 9.0.0
  - Make sure to update your [`PATH`](https://en.wikipedia.org/wiki/PATH_\(variable\)) to include the location of the `rocq` binary.
- [GNU Make](https://www.gnu.org/software/make/) >= 3.79.1
  - You also need these common Unix tools: `cp`, `find`, and `rm`. If you have `make`, you probably already have those other programs too.
