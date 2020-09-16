#!/bin/sh

FILES=`cat TESTS`

echo "Running each test ${1} times"

for f in $FILES
do
    echo "Running ${f} in direct-style"
    ./${f} $1
    echo "Running ${f} in CPS"
    ./${f}_cps $1
    echo "Running ${f} in direct-style with O1"
    ./${f}_opt $1
    echo "Running ${f} in CPS with O1"
    ./${f}_cps_opt $1
done
