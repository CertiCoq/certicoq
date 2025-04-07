QUAL=CertiCoq.Benchmarks.hash
QUALS=CertiCoq.Benchmarks.hash.hash
COQOPTS = -R ./ $(QUAL)
CCOMPILER=gcc

default: coq copy prog

copy:
	cp ../../Runtime/gc_stack.c ./
	cp ../../Runtime/gc_stack.h ./
	cp ../../Runtime/values.h ./
	cp ../../Runtime/config.h ./

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
	coqc $(COQOPTS) hash.v

prog:
	$(CCOMPILER) -o prog -Wno-everything -O2 prog_main.c gc_stack.c $(QUALS).prog.c prog_glue.c ffi.$(QUALS).IO_Impl.c ffi.$(QUALS).StringFFI.c ffi.$(QUALS).HashFFI.c

debug:
	$(CCOMPILER) -o prog -Wno-everything prog_main.c gc_stack.c $(QUALS).prog.c prog_glue.c ffi.$(QUALS).IO_Impl.c ffi.$(QUALS).StringFFI.c ffi.$(QUALS).HashFFI.c -g
