#!/bin/sh
clang -w -S -O2 -fomit-frame-pointer $1.ll
clang -w -S -O2 -fomit-frame-pointer $1CC.ll
rm $1.ll
rm $1CC.ll
