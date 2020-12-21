## Installation Instructions

See [INSTALL.md](https://github.com/PrincetonUniversity/certicoq/INSTALL.md)  for installation instructions.

### Prerequisites

  To install the compiler, you need OCaml and Coq.8.9.1.

  We depend on the following Coq packages:

  `ExtLib` and `MetaCoq` (which requires `Equations`).
   All three packages are currently installed using git modules (see below).

### Building the dependencies

  From the `certicoq/` directory, run:

    # make submodules

### Building the compiler

  From the `certicoq/` directory, run:

    # make -j4

  After the sources are successfully compiled, you can compile and
  install the CertiCoq plugin with:

    # make install

  To test the installation, go to 'certicoq/benchmarks' and run

    # make all

## 