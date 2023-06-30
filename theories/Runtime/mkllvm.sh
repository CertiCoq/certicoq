#!/bin/sh
clang-11 -w -S -O2 -fomit-frame-pointer $1.c -emit-llvm
python mod.py $1.ll $1CC.ll
rm $1.ll
