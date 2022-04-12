#!/usr/bin/env bash

PLUGIN=$1
EPATH=

echo "Plugin: " ${PLUGIN}

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

# For compat with OS X which has an incompatible sed which can be replaced by GNU sed
SED=`which gsed || which sed`

echo "Cleaning result of extraction"

rm -rf ${PLUGIN}/extraction || true

if [ ! -d "${PLUGIN}/extraction" ]
then
    mkdir ${PLUGIN}/extraction
fi

# Copy the extracted code to the extraction destination
cd ${EPATH}

# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=../../"${PLUGIN}"/extraction/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Copying " $i "to" $newi;
  cp $i $newi;
done

cd ../..

# Speciale case for files that are only uppercase!
cd ${PLUGIN}/extraction
mv aST.ml AST.ml
mv aST.mli AST.mli
mv fLT.ml FLT.ml
mv fLT.mli FLT.mli
# Work around a compiler bug in module name resolution
${SED} -f ../extraction.sed -i compile0.ml
# We compile with -rectypes, so these definitions are badly interepreted
${SED} -e "s/type int = int/type nonrec int = int/" -i integers.mli
${SED} -e "s/type int = int/type nonrec int = int/" -i integers.ml
cd ../..
