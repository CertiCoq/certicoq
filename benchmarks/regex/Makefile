QUAL=CertiCoq.Benchmarks.regex
QUALS=CertiCoq.Benchmarks.regex.regex
COQOPTS = -R ./ $(QUAL)
CCOMPILER=gcc

default: coq prog
INCLUDE=../../runtime

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
	rm -f ./ffi.*.*.c
	rm -f ./ffi.*.*.h
	rm -f ./*.vo
	rm -f ./*.glob

coq:
	coqc $(COQOPTS) regex.v

prog:
	$(CCOMPILER) -o prog -Wno-everything -lpcre -O2 -I$(INCLUDE) prog_main.c $(INCLUDE)/gc_stack.c $(QUALS).prog.c glue.$(QUALS).prog.c ffi.$(QUALS).RegexFFI.c -g

debug:
	$(CCOMPILER) -o prog -Wno-everything -lpcre -I$(INCLUDE) prog_main.c $(INCLUDE)/gc_stack.c $(QUALS).prog.c glue.$(QUALS).prog.c ffi.$(QUALS).RegexFFI.c -g
