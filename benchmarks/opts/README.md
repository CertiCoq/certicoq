CertiCoq Benchmarks
-------------------
To compile the Coq benchmarks to C, compile and run the C files simply run

  # make all

This will also compile the necessary libraries located in ./lib. To avoid
recompiling the library in the future compile with

  # make

To clean and recompile the library run

  # make cleanlib
  # make lib

To run the compiled benchmarks:

   # sh run.sh X

where X is the number of times each test runs. Running `make` will invoke `sh run.sh 10`.


How to add new benchmarks
-------------------------
To add a new benchmark

1) Go to tests.v and add your benchmark program at the end of the file. The
   top-level definition that is compiled should be defined in the file tests.v
   (not just imported). Write command to compile both the LambdaANF and ANF versions
   (otherwise the bencmarking automation will not work.

2) Create a file named <benchmark_name>_main.c to run the benchmark and print
   the result

3) Go to file TESTS, add the name of the new benchmark at the end of the file.
