#!/usr/bin/env bash

cd submodules

cd paramcoq
make coq install
if [ $? -eq 0 ]
then
    echo "paramcoq looks up-to-date"
else
    echo "(re)building paramcoq"
    make clean
    make coq
    make install
fi
cd ..

cd coq-ext-lib
coq_makefile -f _CoqProject -o Makefile
make all install
if [ $? -eq 0 ]
then
    echo "coq-ext-lib looks up-to-date"
else
    echo "(re)building coq-ext-lib"
    make clean
    make all
    make install
fi
cd ..

cd SquiggleEq
make all install
if [ $? -eq 0 ]
then
    echo "Squiggleeq looks up-to-date"
else
    echo "(re)building SquiggleEq"
    make clean
    make all
    make install
fi
cd ..

cd Equations
coq_makefile -f _CoqProject -o Makefile
make all install
if [ $? -eq 0 ]
then
    echo "Equations looks up-to-date"
else
    echo "(re)building Equations"
    make clean
    make all
    make install
fi
cd ..

cd Template-Coq
./configure.sh local
make all install
if [ $? -eq 0 ]
then
    echo "MetaCoq looks up-to-date"
else
    echo "(Re)building MetaCoq"
    ./configure.sh local
    make clean
    make all
    make install
fi
