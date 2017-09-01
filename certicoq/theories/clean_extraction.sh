#env /bin/sh

echo "Cleaning result of extraction"

# Remove modules already built as part of template-plugin
cd Extraction
rm -f Datatypes.* Ascii.* BinPosDef.* BinPos.* BinNat.* BinNums.* Bool.* Nat0.* String0.*

# Uncapitalize modules to circumvent a bug of coqdep with mllib files
for i in *.ml*
  do
  newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
  echo "Moving " $i "to" $newi;
  mv $i $newi;
done

cd ..