#!/usr/bin/env bash

# For compat with OS X which has an incompatible sed which can be replaced by GNU sed
SED=`which gsed || which sed`

echo "Cleaning result of extraction"

rm -rf plugin/extraction || true

if [ ! -d "plugin/extraction" ]
then
    mkdir plugin/extraction
fi

# Copy the extracted code to the extraction destination
cd theories/Extraction

# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=../../plugin/extraction/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Copying " $i "to" $newi;
  cp $i $newi;
done

cd ../..

# Speciale case for files that are only uppercase!
cd plugin/extraction
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
