#!/bin/sh

cd submodules

cd coq-ext-lib
make
if [ $? -eq 0 ]
then
    echo "coq-ext-lib looks upto date"
else
    echo "(re)building coq-ext-lib"
    coq_makefile -f _CoqProject -o Makefile
    make clean
    make all
    make install
fi
cd ..

cd SquiggleEq
make
if [ $? -eq 0 ]
then
    echo "Squiggleeq looks upto date"
else
    echo "(re)building SquiggleEq"
    make clean
    make all
    make install
fi
cd ..

cd Equations
make
if [ $? -eq 0 ]
then
    echo "Equations looks upto date"
else
    echo "(re)building Equations"
    coq_makefile -f _CoqProject -o Makefile
    make clean
    make all
    make install
fi
cd ..

cd Template-Coq
make
if [ $? -eq 0 ]
then
    echo "MetaCoq looks upto date"
else
    ./configure.sh local
    make clean
    make all
    make install
fi
