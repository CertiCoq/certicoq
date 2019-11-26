#!/usr/bin/env bash

DOCLEAN=$1

clean() {
    if [[ "$DOCLEAN" == "noclean" ]]; then
        echo "Warning: not cleaning"
    else
        git clean -dfx
    fi
}

cd submodules

cd paramcoq
echo "Rebuilding paramcoq"
clean
make
make install
cd ..

cd coq-ext-lib
echo "Rebuilding coq-ext-lib"
clean
coq_makefile -f _CoqProject -o Makefile
make all
make install
cd ..

cd SquiggleEq
echo "Rebuilding SquiggleEq"
clean
make all
make install
cd ..

cd Equations
echo "Rebuilding Equations"
clean
coq_makefile -f _CoqProject -o Makefile
make all
make install
cd ..

cd MetaCoq
echo "Rebuilding MetaCoq"
clean
./configure.sh local
make all
make install
