CC=gcc
CFLAGS=  -g -O3

# CFLAGS=  -m32 -g -O3   ///use this for 32-bit x86 mode


all: gc.o nogc.o gctest

gctest: gctest.o gc.o
	${CC} ${CFLAGS} gctest.o gc.o -o gctest


gc.o: gc.c config.h values.h
nogc.o: nogc.c config.h values.h
gctest.o: gctest.c config.h values.h

gctest.s: gctest.c config.h values.h
	${CC} ${CFLAGS} -S gctest.c

clean:
	rm -f *.o gctest gctest.s
