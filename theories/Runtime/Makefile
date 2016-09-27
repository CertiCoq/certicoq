CC=gcc
CFLAGS=  -g -O3

# CFLAGS=  -m32 -g -O3   ///use this for 32-bit x86 mode


all: gc.o nogc.o gctest gctest2 ocamltest ocamltest-nonopt

time: all
	time ./gctest 10000000
	time ./gctest2 10000000
	time ./ocamltest 10000000
	time ./ocamltest-nonopt 10000000

gctest: gctest.o gc.o
	${CC} ${CFLAGS} gctest.o gc.o -o gctest

gctest2: gctest2.o gc.o
	${CC} ${CFLAGS} gctest.o gc.o -o gctest2

ocamltest: ocamltest.ml
	ocamlopt ocamltest.ml -o ocamltest

ocamltest-nonopt: ocamltest.ml
	ocamlc ocamltest.ml -o ocamltest-nonopt


gc.o: gc.c config.h values.h
nogc.o: nogc.c config.h values.h
gctest.o: gctest.c config.h values.h
gctest2.o: gctest2.c config.h values.h

gctest.s: gctest.c config.h values.h
	${CC} ${CFLAGS} -S gctest.c

clean:
	rm -f *.o gctest gctest2 gctest.s ocamltest ocamltest-nonopt *.cmi *.cmx *.cmo;
	rm -rf oprofile_data

