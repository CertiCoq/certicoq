# CertiCoq

<p align="center">
<img src="ANONYMIZED" alt="MetaCoq" width="100px"/>
</p>

## Overview

CertiCoq is a compiler for Gallina, the specification language of the [Coq proof assistant](https://coq.inria.fr/refman/index.html). CertiCoq targets Clight, a subset of the C language that can be compiled with any C compiler, including the [CompCert](http://compcert.org) verified compiler.

Large parts of the CertiCoq compiler have been verified whereas others are in the process of being verified.

## Documentation

The [CertiCoq Wiki](ANONYMIZED) has instructions for using the [CertiCoq plugin](ANONYMIZED) to compile Gallina to C and interfacing with the generated C code.

You can also find some demos [here](ANONYMIZED) and [here](ANONYMIZED).

## Installation Instructions

See [INSTALL.md](INSTALL.md)  for installation instructions.

## Current Members

ANONYMIZED

## Past Members and Contributors

ANONYMIZED

## License 

CertiCoq is open source and distributed under the [MIT license](LICENSE.md).

## Directory structure

* `theories/` contains the sources of the compiler
* `plugin/` contains the CertiCoq plugin for Coq 
* `benchmarks/` contains the benchmark suite
* `glue/` contains the glue code generator

Structure of the theories directory:

* `theories/common`: contains common code utilities 
* `theories/Compiler`: contains the toplevel CertiCoq pipeline 
* `theories/L1g`: 1st pass, moves from (MetaCoq's) λbox to our similar L1g
* `theories/L2k_noCnstrParams`: 2nd pass, eta expands constructors and removes constructor parameters 
* `theories/L4_deBruijn`: 3rd pass, let-bind environment
* `theories/L6_PCPS` contains the λANF pipeline (and conversions -- direct and CPS -- to λANF)
* `theories/L7` contains the C code generator.
* `theories/compcert` contains a local copy of the compcert compiler


## Bugs 

We use github's [issue tracker](https://github.com/PrincetonUniversity/certicoq/issues) to keep track of bugs and feature requests.
