#env /bin/sh
sh clean_extraction.sh
cd plugin
exec make -f Makefile ${@}
