all: copy demo demo1 demo2

copy:
	cp ../../theories/Runtime/gc.c ./
	cp ../../theories/Runtime/gc.h ./
	cp ../../theories/Runtime/values.h ./
	cp ../../theories/Runtime/main.c ./
	cp ../../theories/Runtime/config.h ./
demo: tests.v
	coqc tests.v

demo1: maindemo1.c tests.demo1.c
	gcc -o demo1 -Wno-everything -O2 maindemo1.c gc.c tests.demo1.c

demo2: maindemo2.c tests.demo2.c
	gcc -o demo2 -Wno-everything -O2 maindemo2.c gc.c tests.demo2.c
