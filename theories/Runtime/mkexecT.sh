#!/bin/sh
sh mkllvm.sh $1
clang -w -O2 -fomit-frame-pointer mainT.c gc.c $1.c -o $1.out
clang -w -O2 -fomit-frame-pointer mainT.c gc.c $1CC.ll -o $1CC.out
clang -w -O2 mainT.c gc.c $1.c -o $1Frame.out
clang -w -O2 mainT.c gc.c $1CC.ll -o $1CCFrame.out
ccomp -w -O2 mainT.c gc.c $1.c -o $1ccomp.out

rm $1CC.ll
