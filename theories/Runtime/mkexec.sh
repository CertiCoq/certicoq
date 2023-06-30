#!/bin/sh
sh mkllvm.sh $1
clang-11 -w -O2 -fomit-frame-pointer main.c gc.c $1.c -o $1.out
clang-11 -w -O2 -fomit-frame-pointer main.c gc.c $1CC.ll -o $1CC.out
clang-11 -w -O2 main.c gc.c $1.c -o $1Frame.out
clang-11 -w -O2 main.c gc.c $1CC.ll -o $1CCFrame.out
ccomp -w -O2 main.c gc.c $1.c -o $1ccomp.out
if [ "$2" = '-make-ocaml' ]; then
    ocamlbuild $1.native
    ocamlbuild $1.byte
fi
rm $1CC.ll
