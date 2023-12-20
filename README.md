# Proofs

[![Build status](https://github.com/stepchowfun/proofs/workflows/Continuous%20integration/badge.svg?branch=main)](https://github.com/stepchowfun/proofs/actions?query=branch%3Amain)

This is my personal repository of formally verified mathematics, including results from category theory, type theory, domain theory, etc., and some original research. All the proofs are verified using the [Coq proof assistant](https://coq.inria.fr/).

If you want to set up your own repository of formally verified mathematics, you can simply fork this repository and replace the contents of the [`proofs`](https://github.com/stepchowfun/proofs/tree/main/proofs) directory with your own proofs. Setting up a Coq project from scratch is not particularly straightforward, so this scaffolding can save you time.

If you are new to Coq, the repository contains a tutorial [here](https://github.com/stepchowfun/proofs/tree/main/proofs/tutorial). I recommend [Software Foundations](https://softwarefoundations.cis.upenn.edu/) and [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) for further learning.

## Instructions

Make sure you have the dependencies listed below. Then you can run `make` in this directory to verify all the proofs. If you change anything, run `make` again to incrementally verify the affected proofs. The build artifacts can be removed with `make clean`.

To write proofs, you'll want to use an IDE that supports interactive theorem proving. My general recommendation is [VsCoq](https://github.com/coq-community/vscoq), which is a plugin for [Visual Studio Code](https://code.visualstudio.com/). However, you may find the built-in [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) easier if you're new to interactive theorem proving, since it has buttons you can click on to step through your proofs.

### Dependencies

You'll need the following:

- [Coq](https://coq.inria.fr/) >= 8.17.1
  - Make sure to update your [`PATH`](https://en.wikipedia.org/wiki/PATH_\(variable\)) to include the location of the Coq binaries (`coqc`, `coqdep`, etc.).
- [GNU Make](https://www.gnu.org/software/make/) >= 3.79.1
  - You also need these common Unix tools: `cp`, `find`, and `rm`. If you have `make`, you probably already have those other programs too.
