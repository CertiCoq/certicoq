#env /bin/sh
if [ ! -f "plugin/astCommon.ml" ]
then
    sh clean_extraction.sh
else
    a=`stat -f "%m" Extraction/AstCommon.ml`
    b=`stat -f "%m" plugin/astCommon.ml`
    if [ "$a" -gt "$b" ]
	then
	sh clean_extraction.sh
    fi
fi

exec make -f Makefile.plugin ${@}
