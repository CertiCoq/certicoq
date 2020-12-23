# Installing CertiCoq

### Prerequisites

To install the compiler, you need OCaml (tested with `4.07.1` ) and Coq 8.12.

CertiCoq depends on the following Coq packages:  
`ExtLib` and `MetaCoq` (which requires `Equations`).

#### Building the dependencies

##### Ext-lib

You can install [ExtLib](https://github.com/coq-community/coq-ext-lib) (v0.11.2) from the source code or from opam with `opam install coq-ext-lib.0.11.2`.

##### Equations

You can install [Equations](https://github.com/mattam82/Coq-Equations) (v1.2.3) from opam or from their source code or from opam with `opam install coq-equations.1.2.3+8.12`.

##### MetaCoq

Currently, MetaCoq needs to be installed manually from the `coq-8.12` branch in [MetaCoq's github](https://github.com/MetaCoq/metacoq/tree/coq-8.12). 

#### Submodules 

Alternatively, you may install Equations and MetaCoq using git modules.  From the `certicoq/` directory, run:

    # make submodules


### Building the compiler

  From the `certicoq/` directory, run:

    # make -j4

  After the sources are successfully compiled, you can compile and
  install the CertiCoq plugin with:

    # make install

  To test the installation, you can go to `certicoq/benchmarks` and run

    # make all
