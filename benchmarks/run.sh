#!/bin/sh

FILES=`cat TESTS`

echo "Running each test ${1} times"

for f in $FILES
do
    echo "Running ${f} in direct-style"
    ./${f} $1
    echo "Running ${f} in CPS"
    ./${f}_cps $1
done
