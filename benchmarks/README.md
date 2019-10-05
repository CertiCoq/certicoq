CertiCoq Benchmarks
  as featured in
"Verified Extraction for Coq"
  a thesis by
Olivier Savary Belanger
===========================

This file describes the procedure to extract and compile (using CertiCoq and Compcert), and run the benchmarks described in Chapter 5 of "Verified Extraction for Coq" [1]. 

INSTALLATION:
---------------------------
Before running the benchmarks:
1) Install CertiCoq (see ../README.md)
  a) To get the average time of 10 runs for each phase, go to ../theories/extraction/extraction.v and comment out every versions of AstCommon.timePhase other than T2.
  b) To get the whole compilation time, go to ../theories/extraction/extraction.v and comment out every versions of AstCommon.timePhase other than T1
2) Install Compcert (version 3.6)


RUNNING THE BENCHMARKS:
---------------------------
To run all the benchmarks, run the "benchmarks" Make target in the current folder:
# make benchmarks
File "benchmarks.expected" was generated using
# make benchmarks > benchmarks.expected
with AstCommon.timePhase T2.


Bibliography
------------
[1] Savary Belanger, Olivier. Verified Extraction for Coq. PhD Thesis, Princeton University, 2019.