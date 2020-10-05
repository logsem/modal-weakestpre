# Modal Weakest Precondition
[![Build Status](https://travis-ci.com/logsem/modal-weakestpre.svg?branch=main)](https://travis-ci.com/logsem/modal-weakestpre)

A modality-parametric weakest precondition theory for the
[Iris](https://gitlab.mpi-sws.org/iris/iris/) program logic framework in Coq.

## Building the theory

The project can be built locally or by using the provided
[Dockerfile](Dockerfile), see the [Using Docker](/#using-docker) section for
details on the latter.

### Prerequisites 

The project is known to compile with:

- Coq 8.12.0
- Development versions of [Iris](https://gitlab.mpi-sws.org/iris/iris/) and
  [std++](https://gitlab.mpi-sws.org/iris/stdpp) as specified in the
  [modal-weakestpre.opam](modal-weakestpre.opam) file

The dependencies can be obtained using opam; see [this
guide](https://opam.ocaml.org/doc/Install.html) for how to install opam. To
obtain the dependencies, you have to add the following repositories to the opam
registry by invoking

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
    opam update

Once you got opam set up, run `make build-dep` to install the right versions of
the dependencies.

### Building
Run `make -jN` to build the full development, where `N` is the number of CPU
cores on your machine.

### Installing
Run `make install` to install the development as a local Coq package for use in
your own developments.

### Using Docker
The development can be built using
[Docker](https://docs.docker.com/get-docker/). To speed up compilation time, the
dependencies have been prepared and compiled separately in
[Dockerfile.deps](Dockerfile.deps) and published in a Dockerhub
[repository](https://hub.docker.com/repository/docker/simongregersen/modal-weakestpre). This
image can be built locally by running `make docker-build-deps`.

Run `make docker-build` to build [Dockerfile](Dockerfile) and the development
with the pre-compiled dependencies.

## Documentation

Documentation can be generated using
[coqdoc](https://coq.inria.fr/refman/using/tools/coqdoc.html) by running `make
html`. Afterwards, a [table of contents](html/toc.html) is generated from which
the documentation can be accessed.



