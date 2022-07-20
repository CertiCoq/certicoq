#!/usr/bin/env bash

PLUGIN=$1
EPATH=

if [ "${PLUGIN}" == "plugin" ]
then 
    echo "Building optimized ML plugin"
    EPATH="theories/Extraction"
else
    if [ "${PLUGIN}" == "cplugin" ]
    then
        echo "Building vanila ML plugin"
        EPATH="theories/ExtractionVanilla"
    else
        echo "Don't know which plugin to build"
        exit 1
    fi 
fi

if [ ! -f "${PLUGIN}/extraction/astCommon.ml" ]
then
    bash clean_extraction.sh "${PLUGIN}"
else
    if [ "${EPATH}/AstCommon.ml" -nt "${PLUGIN}/extraction/astCommon.ml" ]
	then
	    bash clean_extraction.sh "${PLUGIN}"
    fi
fi

cd ${PLUGIN}
exec make -f Makefile
