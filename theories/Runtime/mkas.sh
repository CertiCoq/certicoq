#!/bin/sh
sh mkllvm.sh $1
clang -w -S -O2 -fomit-frame-pointer $1.c
clang -w -S -O2 -fomit-frame-pointer $1CC.ll
ccomp -w -S -O2 $1.c -o $1ccomp.s
rm $1CC.ll
