#!/usr/bin/env bash
n=25
for (( i=1; i<=$n; ++i)); do
  echo -------------------- run $i --------------------
  coqc -R ../theories/compcert compcert -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib tests.v
done
