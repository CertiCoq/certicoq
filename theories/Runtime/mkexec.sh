#!/bin/sh
sh mkllvm.sh $1
clang -w -O2 -fomit-frame-pointer main.c gc.c $1.c -o $1c.out
clang -w -O2 -fomit-frame-pointer main.c gc.c $1.ll -o $1.out
clang -w -O2 -fomit-frame-pointer main.c gc.c $1CC.ll -o $1CC.out
rm $1.ll
rm $1CC.ll
