#env /bin/sh

echo "Cleaning result of extraction"

# Remove modules already built as part of template-plugin
cd Extraction

# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=../plugin/`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Copying " $i "to" $newi;
  cp $i $newi;
done

cd ..

cd plugin
rm -f datatypes.* ascii.* binPosDef.* binPos.* binNat.* binNums.* bool.* nat0.* string0.*
cd ..