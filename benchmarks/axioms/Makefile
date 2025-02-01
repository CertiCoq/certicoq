COQOPTS = -R ./ CertiRocq.Benchmarks -R ../lib CertiRocq.Benchmarks.lib
CCOMPILER=gcc
INCLUDE=../../runtime

# Names of the tests
TESTS=print_lst fibn list_sum_int63 list_sum_int63_tinfo
# Names of the generated C files
CFILES=$(patsubst %, CertiRocq.Benchmarks.tests.%.c, $(TESTS)) glue.c

default: exec

.PHONY: compile exec clean

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob
	rm -f $(TESTS)
	rm -f glue.*

compile: tests.v
	coqc $(COQOPTS) tests.v

$(CFILES): compile

fibn: CertiRocq.Benchmarks.tests.fibn.c glue.c int63.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c CertiRocq.Benchmarks.tests.fibn.c glue.c int63.c

print_lst: CertiRocq.Benchmarks.tests.print_lst.c glue.c print.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c CertiRocq.Benchmarks.tests.print_lst.c glue.c print.c

list_sum_int63: CertiRocq.Benchmarks.tests.list_sum_int63.c glue.c int63.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c CertiRocq.Benchmarks.tests.list_sum_int63.c glue.c int63.c

list_sum_int63_tinfo: CertiRocq.Benchmarks.tests.list_sum_int63_tinfo.c glue.c int63_tinfo.c
	$(CCOMPILER) -o $@ -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c CertiRocq.Benchmarks.tests.list_sum_int63_tinfo.c glue.c int63_tinfo.c

exec: $(TESTS)
