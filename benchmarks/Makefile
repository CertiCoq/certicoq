COQOPTS = -R ../plugin CertiCoq.Plugin -I ../plugin -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib
CCOMPILER=gcc
CFILES= demo1 demo2 list_sum vs_easy vs_hard Binom.main Color.main

cfiles: $(CFILES)
all: copy lib tests cfiles

copy:
	cp ../theories/Runtime/gc.c ./
	cp ../theories/Runtime/gc.h ./
	cp ../theories/Runtime/gc_stack.c ./
	cp ../theories/Runtime/gc_stack.h ./
	cp ../theories/Runtime/values.h ./
	cp ../theories/Runtime/main.c ./
	cp ../theories/Runtime/config.h ./

clean:
	$(MAKE) clean -C lib
	rm -f ./gc.c
	rm -f ./gc.h
	rm -f ./values.h
	rm -f ./main.c
	rm -f ./config.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./*.vo

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

tests: tests.v
	coqc $(COQOPTS) tests.v

$(CFILES): 
	$(CCOMPILER) -o $@_cps -Wno-everything -O2 $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue.CertiCoq.Benchmarks.tests.$@.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue.CertiCoq.Benchmarks.tests.$@.c
