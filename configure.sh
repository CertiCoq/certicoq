#!/usr/bin/env bash

# Removes all generated makefiles
make -f Makefile mrproper

# Dependencies for local or global builds.
# When building the packages separately, dependencies are not set as everything
# should already be available in $(COQMF_LIB)/user-contrib/MetaCoq/*
# For local builds, we set specific dependencies of each subproject in */metacoq-config

# CWD=`pwd`

if [[ "$1" = "global" ]] || [[ "$1" = "--enable-global" ]]
then
    echo "Building CertiCoq globally"
    echo "CERTICOQ_CONFIG = global" > Makefile.conf
else    
    echo "Building CertiCoq locally (default)"
    echo "CERTICOQ_CONFIG = local" > Makefile.conf
fi
