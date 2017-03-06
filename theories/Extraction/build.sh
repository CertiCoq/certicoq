#!/bin/sh

file=${1-allInstances.native}
ocamlbuild -lib Str $file
./$file
