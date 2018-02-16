#env /bin/sh

echo "Cleaning result of extraction"

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

# Remove extracted modules already linked in template_coq_plugin.
cd plugin/extraction
rm -f ast0.* specif.* peanoNat.* list0.* datatypes.* ascii.* univ0.* binPosDef.* binPos.* binNat.* binNums.* binInt.* binIntDef.* bool.* nat0.* string0.* basics.*
cd ../..