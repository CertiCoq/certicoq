all: copy demo demo1 demo2
clos_all : clos clos_opt clos_old
is_valid_all : is_valid is_valid_old is_valid_opt

copy:
	cp ../../theories/Runtime/gc_stack.c ./
	cp ../../theories/Runtime/gc_stack.h ./
	cp ../../theories/Runtime/values.h ./
	cp ../../theories/Runtime/main.c ./
	cp ../../theories/Runtime/config.h ./
demo: tests.v
	coqc tests.v

demo1: maindemo1.c tests.demo1.c
	gcc -o demo1 -Wno-everything -O2 maindemo1.c gc_stack.c tests.demo1.c

demo2: maindemo2.c tests.demo2.c
	gcc -o demo2 -Wno-everything -O2 maindemo2.c gc_stack.c tests.demo2.c


clos: main.c tests.clos.c
	gcc -o clos -Wno-everything -O2 mainclos.c gc_stack.c tests.clos.c

clos_opt: main.c tests.clos_opt.c
	gcc -o clos_opt -Wno-everything -O2 mainclos.c gc_stack.c tests.clos_opt.c

clos_old: main.c tests.clos_old.c
	gcc -o clos_old -Wno-everything -O2 mainclos.c gc_stack.c tests.clos_old.c


is_valid: main.c tests.is_valid.c
	gcc -o is_valid -Wno-everything -O2 main.c gc_stack.c tests.is_valid.c

is_valid_opt: main.c tests.is_valid_opt.c
	gcc -o is_valid_opt -Wno-everything -O2 main.c gc_stack.c tests.is_valid_opt.c

is_valid_old: main.c tests.is_valid_old.c
	gcc -o is_valid_old -Wno-everything -O2 main.c gc_stack.c tests.is_valid_old.c


