QUAL=CertiCoq.Benchmarks.regex
QUALS=CertiCoq.Benchmarks.regex.regex
COQOPTS = -R ./ $(QUAL)
CCOMPILER=gcc

default: coq copy prog

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
	rm -f ./ffi.*.*.c
	rm -f ./ffi.*.*.h
	rm -f ./*.vo
	rm -f ./*.glob

coq:
	coqc $(COQOPTS) regex.v

prog:
	$(CCOMPILER) -o prog -Wno-everything -lpcre -O2 prog_main.c gc.c $(QUALS).prog.c glue.$(QUALS).prog.c ffi.$(QUALS).RegexFFI.c -g

debug:
	$(CCOMPILER) -o prog -Wno-everything -lpcre prog_main.c gc.c $(QUALS).prog.c glue.$(QUALS).prog.c ffi.$(QUALS).RegexFFI.c -g
