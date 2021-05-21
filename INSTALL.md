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


### Running the benchmarks

  From the `certicoq/` directory, run:
  
    # cd benchmarks/ocaml
    # make all
    # cd ..
    # make all


  That is, first run `make all` in the directory `benchmarks/ocaml`
  and then `make all` in the directory `benchmarks`.  The last command
  will run CertiCoq to generate the required *.c files and will
  compile them with the C compiler (the actual CertiCoq commands for
  compilation are in the file `benchmarks/tests.v`. Most of the
  benchmarks are imported from `benchmarks/lib`).

  Then to run the benchmarks run:

  ## sh run_benchmarks.sh N

  Where N is the number of runs for each benchmark (in the paper N =
  10). Each run is a separate process and within each process time is
  measured for 10 iterations of the benchmark program (to exclude
  process startup time).

  The script run_benchmarks.sh generates a table with the following
  columns:

  Benchmark  CertiCoq  Ratio  Dev    CertiCoqO  Ratio  Dev    CertiCoqL  Ratio  Dev    CertiCoqCC  Ratio  Dev    ocamlc   Ratio  Dev    ocamlopt  Ratio  Dev

  Benchmark  : the name of the benchmarks
  CertiCoq   : the execution time of the base CertiCoq -O0 configuration (without the lambda lifting configuration).
  CertiCoqO  : the execution time of the CertiCoq -O1 configuration (with the lambda lifting optimization).
  CertiCoqL  : the execution time of the CertiCoq -O1 -lift-all configuration (with the non-selective lambda).
  CertiCoqCC : the execution time of the base CertiCoq -O0 configuration compiled with CompCert
  ocamlc     : the execution time using the OCaml bytecode compiler
  ocamlopt   : the execution time using the OCaml native compiler

  ratio      : the execution time of each configuration relative to CertiCoq -O0
  dev        : Standard deviation  (for the N processes)

  The table in section 6 of the paper is generated from that table. 
  A sample output is in benchmarks/sample_output.txt.