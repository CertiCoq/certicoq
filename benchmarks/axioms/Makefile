COQOPTS = -R ../plugin CertiCoq.Plugin -I ../plugin -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib
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
	cp ../../theories/Runtime/mod.py ./

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
	$(CCOMPILER) -o print_lst -Wno-everything -O2 -fomit-frame-pointer print_lst_main.c gc.c CertiCoq.Benchmarks.tests.print_lst.c glue.CertiCoq.Benchmarks.tests.print_lst.c print.c
