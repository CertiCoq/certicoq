#env /bin/sh

echo "Cleaning result of extraction"

if [ ! -d "plugin/extraction" ]
then
    mkdir plugin/extraction
fi

# Move extracted modules to build the certicoq compiler plugin
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
# rm -f basicAst.* ast0.* astUtils.* specif.* peanoNat.* list0.* datatypes.* decimal.* ascii.* univ0.* binPosDef.*
# rm -f binPos.* binNat.* binNums.* binInt.* binIntDef.* bool.* nat0.* string0.* basics.*
# rm -f checker0.* typing.* retyping.* univSubst.* stringMap.*
# rm -f astUtils.* universes.* pretty.* char.*
# rm -f classes0*
# rm -f numeral.*
# Work around a compiler bug in module name resolution
sed -f ../extraction.sed -i bak compile0.ml
# We compile with -rectypes, so these definitions are badly interepreted
sed -e "s/type int = int/type nonrec int = int/" -i bak integers.mli
sed -e "s/type int = int/type nonrec int = int/" -i bak integers.ml
cd ../..
