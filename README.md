# CertiCoq

## Overview

CertiCoq is a compiler for Gallina, the specification language of the
[Coq proof assistant](https://coq.inria.fr/refman/index.html), to
Clight a subset of the C language.

Large parts of the CertiCoq compiler are verified whereas others are
in the process of being verified.

## Documentation

The [CertiCoq Wiki](https://github.com/PrincetonUniversity/certicoq/wiki) has instructions
for using the CertiCoq plugin to compile Gallina to C and interfacing with the generated C code.

You can also look at some demos
[here](https://github.com/PrincetonUniversity/certicoq/blob/master/benchmarks/tests.v)
and
[here](https://github.com/PrincetonUniversity/certicoq/blob/master/benchmarks/axioms/tests.v).

## Authors

At its initial prerelease, this software is copyright (c) 2018 by
Abhishek Anand, Andrew Appel, Greg Morrisett, Zoe Paraskevopoulou,
Randy Pollack, Olivier Savary Belanger, and Matthieu Sozeau.

## License

The authors intend to open-source license this software during the first quarter of 2018. Until that time: Throughout 2018, you are free to download, examine, install, and use this software for academic or research purposes.


## Installing CertiCoq

### Prerequisites

  To install the compiler, you need OCaml and Coq.8.9.1.

  We depend on the following Coq packages:

  `ExtLib` and `MetaCoq` (which requires `Equations`).
   All three packages are currently install using git modules (see below).

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

## Directory structure

* `theories/` contains the sources of the compiler
* `plugin/` contains the CertiCoq plugin for Coq 
* `benchmarks/` contains our bechmark suite

Structure of the theories directory:

* `theories/common`: contains common code utilities 
* `theories/Compiler`: contains the toplevel CertiCoq pipeline 
* `theories/L1g`: 1st pass, moves from (MetaCoq's) λbox to our similar L1g
* `theories/L2k_noCnstrParams`: 2nd pass, eta expands constructors and removes constructor parameters 
* `theories/L4_deBruijn`: 3rd pass, let-bind environment
* `theories/L6_PCPS` contains the λ_ANF pipeline (and CPS/ANF conversions to λ_ANF)
* `theories/L7` contains our C code generator
* `theories/compcert` contains a local copy of the compcert compiler