# Installing CertiCoq

### Prerequisites

To install the compiler, you need OCaml (tested with `4.07.1` ) and Coq 8.12.1.

CertiCoq depends on the following Coq packages:  
`ExtLib`, `Equations` `MetaCoq`.

#### Building the dependencies

The source code of the dependencies is provided in the directory
`submodules`.  The dependencies are preinstalled in the VM. You only
need to install these if you are compiling CertiCoq in your machine.

Note that installing released versions of Equations and MetaCoq will
not work as CertiCoq depends on specific (unreleased) versions of
these packages. We recommend installing all dependencies from the
provided source code.

To install the dependencies type the following commands from the
top-level CertiCoq directory.

###### Ext-lib

    # cd submodules/coq-ext-lib
    # make
    # make install
      

###### Equations

    # cd submodules/Equations
    # bash configure.sh
    # make
    # make install

###### MetaCoq

    # cd submodules/metacoq
    # bash configure.sh local
    # make all
    # make translations    
    # make install


### Building the compiler

  From the `certicoq/` directory, run:

    # make

  After the sources are successfully compiled, you can compile and
  install the CertiCoq plugin with:

    # make install

  To test the installation, you can go to `certicoq/benchmarks` and run

    # make all
