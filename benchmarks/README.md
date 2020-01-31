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

Some of these benchmarks are featured in Olivier Savary Belanger's thesis [1],
for an old version of the compiler.

How to add new benchmarks
-------------------------
To add a new benchmark

1) Go to tests.v and add your bencmark program at the end of the file. The
   top-level definition that is complied should be defined in the file tests.v
   (not just imported). Write command to compile both the CPS and ANF versions
   (otherwise the bencmarking automation will not work.

2) Create a file named <benchmark_name>_main.c to run the benchmark and print
   the result

3) Go to file TESTS, add the name of the new benchmark at the end of the file.


References
----------
[1] Savary Belanger, Olivier. Verified Extraction for Coq. PhD Thesis, Princeton University, 2019.