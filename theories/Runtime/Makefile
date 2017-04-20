CC=gcc
CFLAGS= -g -O2
# CFLAGS= -g -O3 -fcall-used-rdi -fcall-used-rsi -fcall-used-rbx -fomit-frame-pointer
TIME= /bin/time -f "%U %P"

# CFLAGS=  -m32 -g -O3   ///use this for 32-bit x86 mode


three: main.o threePlusFour.o nogc.o
	${CC} ${CFLAGS} main.o threePlusFour.o nogc.o -o three

threePlusFour.o: threePlusFour.c gc.h

all: gc.o nogc.o gctest gctest2 gctest3 gctest4 ocamltest ocamltest-nonopt

time: all
	${TIME} ./gctest 10000000 >/dev/null
	${TIME} ./gctest2 10000000 >/dev/null
	${TIME} ./gctest3 10000000 >/dev/null
	${TIME} ./gctest4 10000000 >/dev/null
	${TIME} ./ocamltest 10000000 >/dev/null
	${TIME} ./ocamltest-nonopt 10000000 >/dev/null

gctest: testmain.o gctest.o gc.o testmain.o
	${CC} ${CFLAGS} testmain.o gctest.o gc.o -o gctest

gctest2: gctest2.o gc.o testmain.o
	${CC} ${CFLAGS} testmain.o gctest2.o gc.o -o gctest2

gctest3: gctest3.o gc.o testmain.o
	${CC} ${CFLAGS} testmain.o gctest3.o gc.o -o gctest3

gctest4: gctest4.o gc.o
	${CC} ${CFLAGS} testmain.o gctest4.o gc.o -o gctest4

ocamltest: ocamltest.ml
	ocamlopt ocamltest.ml -o ocamltest

ocamltest-nonopt: ocamltest.ml
	ocamlc ocamltest.ml -o ocamltest-nonopt


main.o: main.c config.h values.h gc.h
testmain.o: testmain.c config.h values.h gc.h
gc.o: gc.c config.h values.h gc.h
nogc.o: nogc.c config.h values.h gc.h
gctest.o: config.h values.h gc.h
gctest2.o: config.h values.h gc.h
gctest3.o: config.h values.h gc.h
gctest4.o: config.h values.h gc.h

gctest.s: config.h values.h
gctest2.s: config.h values.h
gctest3.s: config.h values.h
gctest4.s: config.h values.h

%.s: %.c
	${CC} ${CFLAGS} -S $<
%.o: %.c
	${CC} ${CFLAGS} -c $<
clean:
	rm -f *.o gctest gctest2 gctest3 gctest4 gctest.s gctest2.s gctest3.s gctest4.s ocamltest ocamltest-nonopt *.cmi *.cmx *.cmo;
	rm -rf oprofile_data

