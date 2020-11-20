The CertiCoq project
====================

## INSTALLATION INSTRUCTIONS

### Prerequisites

  To install the compiler, you need OCaml and Coq.8.9.1.

  We depend on the following packages:

  ExtLib and MetaCoq (which requires Equations)

  We provide local copies for these packages. (see below)
  An opam installation of ExtLib may work, but we need a
  particular branch of MetaCoq that is not available in opam. 

### Building the dependencies

  From the `certicoq/` directory, run:

   # sh make_submodules.sh

### Building the compiler
  
  From the `certicoq/` directory, run:

    # make -j4

  To install Certicoq, do the following. This steps the above build steps.

    # make install

  To test the installation, go to 'certicoq/benchmarks' and run

    # make all

## Directory structure

* theories/ contains the sources of the compiler
* plugin/ contains the CertiCoq plugin for Coq 
* benchmarks/ contains our bechmark suite

Structure of the theories directory:

* theories/common: contains common code utilities 
* theories/Compiler: contains the CertiCoq pipeline 
* theories/L1g: 1st pass, moves from (MetaCoq's) λbox to our similar L1g
* theories/L2k_noCnstrParams: 2nd pass, eta expands constructors and removes constructor parameters 
* theories/L4_deBruijn: 3rd pass, let-bind environment
* theories/L6_PCPS contains the λ_ANF pipeline (and CPS/ANF conversions to λ_ANF)
* theories/L7 contains our C code generator
* theories/compcert contains a local copy of the compcert compiler