CCOMPILER=gcc

default: copy prog

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

prog:
	$(CCOMPILER) -o prog_cps -Wno-everything -O2 prog_main.c gc.c Top.prog_cps.c glue.Top.prog_cps.c
	# $(CCOMPILER) -o prog -Wno-everything -O2 prog_main.c gc_stack.c CertiCoq.Benchmarks.tests.prog.c glue.CertiCoq.Benchmarks.tests.prog.c
