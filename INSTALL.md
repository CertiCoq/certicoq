# Installing CertiCoq

### Prerequisites

To install the compiler, you need OCaml (tested with `4.07.1` ) and Coq 8.12.

CertiCoq depends on the following Coq packages:  
`ExtLib` and `MetaCoq` (which requires `Equations`).

#### Building the dependencies

The dependencies can either be installed manually (from sources or via `opam`) or automatically via provided submodules.

##### Manual installation of dependencies

###### Ext-lib

You can install [ExtLib](https://github.com/coq-community/coq-ext-lib) (v0.11.2) from the source code or from opam with `opam install coq-ext-lib.0.11.2`.

###### Equations

You can install [Equations](https://github.com/mattam82/Coq-Equations) (v1.2.3) from opam or from their source code or from opam with `opam install coq-equations.1.2.3+8.12`.

###### MetaCoq

Currently, MetaCoq needs to be installed manually from the `coq-8.12` branch in [MetaCoq's github](https://github.com/MetaCoq/metacoq/tree/coq-8.12). 

##### Installation of dependencies via submodules

Make sure that you do not have any of the dependencies installed already.
From the `certicoq/` directory, run:

    # make submodules
    
Note that this approach will only work if your installation path for Coq is writable without root privileges, this should for instance be the case if Coq was installed via `opam`.

### Building the compiler

  From the `certicoq/` directory, run:

    # make -j4

  After the sources are successfully compiled, you can compile and
  install the CertiCoq plugin with:

    # make install

  To test the installation, you can go to `certicoq/benchmarks` and run

    # make all
