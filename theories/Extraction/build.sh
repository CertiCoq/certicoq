#!/bin/sh

ocamlbuild -lib Str $1 ; ./$1
