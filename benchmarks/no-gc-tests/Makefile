COQOPTS = -R ./ CertiCoq.Benchmarks
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
CFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%_cps.c, $(TESTS)) $(patsubst %, CertiCoq.Benchmarks.tests.%.c, $(TESTS))
# Names of the generated executables
EXEC=$(TESTS) $(patsubst %, %_cps, $(TESTS)) $(patsubst %, %_cps_opt, $(TESTS)) $(patsubst %, %_opt, $(TESTS))
INCLUDE=../../runtime

all: tests exec run
default: exec run

.PHONY: all default clean tests run $(TESTS)

$(CFILES): tests
exec: $(TESTS)

clean:
	# rm -f ./m.h
	# rm -f ./gc.c
	# rm -f ./gc.h
	# rm -f ./gc_stack.c
	# rm -f ./gc_stack.h
	# rm -f ./values.h
	rm -f ./main.c
	# rm -f ./config.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./glue_*.h
	rm -f ./glue_*.c
	rm -f ./*.vo
	rm -f ./*.vos
	rm -f ./*.vok
	rm -f ./*.glob
	rm -f ${EXEC}

cleanexec:
	rm -f $(EXEC)

tests: tests.v
	coqc $(COQOPTS) tests.v

## Compile with the default C compiler
$(TESTS): $(CFILES)
	$(CCOMPILER) -o $@ 			-w -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) $@_main.c $(INCLUDE)/gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue_$@.c


run: run.sh
	sh run.sh 10
