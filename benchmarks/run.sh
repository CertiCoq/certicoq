#!/bin/sh

FILES=`cat TESTS`

for f in $FILES
do
    echo "Running ${f} in direct-style"
    ./${f}
    echo "Running ${f} in CPS"
    ./${f}_cps
done
