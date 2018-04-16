# Proofs

A selection of formal developments in [Coq](https://coq.inria.fr/).

[![Build Status](https://travis-ci.org/stepchowfun/proofs.svg?branch=master)](https://travis-ci.org/stepchowfun/proofs)

## Instructions

Make sure you have the dependencies listed below. Then you can run `make` to verify the proofs. You can also use `make lint` to invoke the linters. The build artifacts can be removed with `make clean`.

You can also verify the proofs inside a [Docker](https://www.docker.com/) container. First, make sure you have Docker installed. Next, run `make docker-deps` to build a Docker image containing the dependencies. Then use `make docker-build` to run the build system inside a container based on that image. The container will be deleted automatically when the build is finished.

## Dependencies

The build system depends on the following:

- [GNU Make](https://www.gnu.org/software/make/) >= 3.79.1
- [Coq](https://coq.inria.fr/) >= 8.7.2

You also need the usual set of Unix tools, such as `echo`, `grep`, etc.
