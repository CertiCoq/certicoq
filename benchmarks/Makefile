COQOPTS = -R ../plugin CertiCoq.Plugin -I ../plugin -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
CFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%_cps.c, $(TESTS)) $(patsubst %, CertiCoq.Benchmarks.tests.%.c, $(TESTS))
# Names of the generated executables
EXEC=$(TESTS) $(patsubst %, %_cps, $(TESTS))

default: copy exec run
all: copy lib exec run

.PHONY: all default clean lib cleanlib tests run

$(CFILES): tests
exec: $(TESTS)

copy:
	cp ../theories/Runtime/gc.c ./
	cp ../theories/Runtime/gc.h ./
	cp ../theories/Runtime/gc_stack.c ./
	cp ../theories/Runtime/gc_stack.h ./
	cp ../theories/Runtime/values.h ./
	cp ../theories/Runtime/main.c ./
	cp ../theories/Runtime/config.h ./

clean:
	rm -f ./gc.c
	rm -f ./gc.h
	rm -f ./gc_stack.c
	rm -f ./gc_stack.h
	rm -f ./values.h
	rm -f ./main.c
	rm -f ./config.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./*.vo
	rm -f ./*.glob
	rm -f $(EXEC)

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

cleanlib:
	$(MAKE) clean -C lib

tests: tests.v
	coqc $(COQOPTS) tests.v

$(TESTS): $(CFILES)
	$(CCOMPILER) -o $@_cps -Wno-everything -O2 $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue.CertiCoq.Benchmarks.tests.$@_cps.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue.CertiCoq.Benchmarks.tests.$@.c

run: run.sh
	sh run.sh
