#!/bin/sh

FILES=`cat TESTS`

echo "Running each test ${1} times"

for f in $FILES
do
    if [ -f "${f}_opt" ]; then
        echo "Running ${f} in direct-style with O1"
        ./${f}_opt $1 > /tmp/${f}_opt.txt
    fi

    for i in {1..5}
    do
	if [ -f "${f}_opt${i}" ]; then
            echo "Running ${f} in direct-style with O1"
            ./${f}_opt${i} $1 > /tmp/${f}_opt${i}.txt
	    diff /tmp/${f}_opt.txt /tmp/${f}_opt${i}.txt || exit 1
	fi
    done
done

true
