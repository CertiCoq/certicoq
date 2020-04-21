#!/bin/sh

file=${1-pipeline.native}
ocamlbuild -lib Str $file
./$file
