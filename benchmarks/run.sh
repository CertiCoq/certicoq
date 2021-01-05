#!/bin/sh

FILES=`cat TESTS`

echo "Running each test ${1} times"

for f in $FILES
do
    echo "Running ${f} in direct-style"
    ./${f} $1
    echo "Running ${f} in direct-style after dearg"
    ./${f}_dearg $1
    echo "Running ${f} in CPS"
    ./${f}_cps $1
    echo "Running ${f} in CPS after dearg"
    ./${f}_dearg_cps $1
    echo "Running ${f} in direct-style with O1"
    ./${f}_opt $1
    echo "Running ${f} in direct-style with O1 after dearg"
    ./${f}_dearg_opt $1
    echo "Running ${f} in CPS with O1"
    ./${f}_cps_opt $1
    echo "Running ${f} in CPS with O1 after dearg"
    ./${f}_dearg_cps_opt $1
done
