COQOPTS = -R ./ CertiCoq.Benchmarks -R ../lib CertiCoq.Benchmarks.lib
CCOMPILER=gcc

default: copy tests print_lst

.PHONY: default clean tests print_lst

copy:
	cp ../../theories/Runtime/gc.c ./
	cp ../../theories/Runtime/gc.h ./
	cp ../../theories/Runtime/gc_stack.c ./
	cp ../../theories/Runtime/gc_stack.h ./
	cp ../../theories/Runtime/values.h ./
	cp ../../theories/Runtime/main.c ./
	cp ../../theories/Runtime/config.h ./

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

tests: tests.v
	coqc $(COQOPTS) tests.v

print_lst:
	$(CCOMPILER) -o print_lst -Wno-everything -O2 -fomit-frame-pointer main.c gc_stack.c CertiCoq.Benchmarks.tests.print_lst.c glue.CertiCoq.Benchmarks.tests.print_lst.c print.c
	$(CCOMPILER) -o fibn -Wno-everything -O2 -fomit-frame-pointer main.c gc_stack.c CertiCoq.Benchmarks.tests.fibn.c glue.CertiCoq.Benchmarks.tests.fibn.c int63.c
	$(CCOMPILER) -o list_sum_int63 -Wno-everything -O2 -fomit-frame-pointer main.c gc_stack.c CertiCoq.Benchmarks.tests.list_sum_int63.c glue.CertiCoq.Benchmarks.tests.list_sum_int63.c int63.c
	$(CCOMPILER) -o list_sum_int63_tinfo -Wno-everything -O2 -fomit-frame-pointer main.c gc_stack.c CertiCoq.Benchmarks.tests.list_sum_int63_tinfo.c glue.CertiCoq.Benchmarks.tests.list_sum_int63_tinfo.c int63_tinfo.c
