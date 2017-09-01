#env /bin/sh

if [ -f Extraction/AstCommon.ml ]
then
    sh clean_extraction.sh
fi

make -f Makefile.plugin ${@}