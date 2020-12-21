# Installing CertiCoq

### Prerequisites

To install the compiler, you need OCaml (tested with `4.07.1` ) and Coq 8.12.

We depend on the following Coq packages:  
`ExtLib` and `MetaCoq` (which requires `Equations`).

### Building the dependencies

 You can install the dependencies using git modules. From the `certicoq/` directory, run:

    # make submodules

Alternatively, you may install these dependencies independenly. 

#### MetaCoq

You'll need to install the `8.12` branch from [MetaCoq's github](https://github.com/MetaCoq/metacoq/tree/coq-8.12).

#### ExtLib and Equations

You may install [ExtLib](https://github.com/coq-community/coq-ext-lib) (v0.11.3) and [Equations](https://github.com/mattam82/Coq-Equations) (v1.2.3) from sources or from opam or from their source code.

### Building the compiler

  From the `certicoq/` directory, run:

    # make -j4

  After the sources are successfully compiled, you can compile and
  install the CertiCoq plugin with:

    # make install

  To test the installation, you can go to `certicoq/benchmarks` and run

    # make all

## 