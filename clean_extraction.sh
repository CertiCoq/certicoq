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

# Remove extracted modules already linked in template_coq plugins.
cd plugin/extraction
rm -f ast0.* ast1.* specif.* peanoNat.* list0.* datatypes.* decimal.* ascii.* univ0.* binPosDef.*
rm -f binPos.* binNat.* binNums.* binInt.* binIntDef.* bool.* nat0.* string0.* basics.*
rm -f checker0.* typing.* retyping.* uGraph0.* extract.* stringMap.*
cd ../..
