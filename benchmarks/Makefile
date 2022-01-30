COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
CFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%_cps.c, $(TESTS)) $(patsubst %, CertiCoq.Benchmarks.tests.%.c, $(TESTS))
# Names of the generated executables
EXEC=$(TESTS) $(patsubst %, %_cps, $(TESTS)) $(patsubst %, %_cps_opt, $(TESTS)) $(patsubst %, %_opt, $(TESTS))

all: copy lib tests exec run
default: copy exec run

.PHONY: all default clean lib cleanlib tests run copy $(TESTS)

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
	cp ../theories/Runtime/mod.py ./

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
	rm -f ./*.vos
	rm -f ./*.vok
	rm -f ./*.glob
	rm -f ${EXEC}

cleanexec:
	rm -f $(EXEC)

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

cleanlib:
	$(MAKE) clean -C lib

tests: tests.v
	coqc $(COQOPTS) tests.v

## Compile with the default C compiler
$(TESTS): $(CFILES)
	$(CCOMPILER) -o $@ -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue.CertiCoq.Benchmarks.tests.$@.c
	$(CCOMPILER) -o $@_opt -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@_opt.c glue.CertiCoq.Benchmarks.tests.$@_opt.c
	$(CCOMPILER) -o $@_opt_ll -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@_opt_ll.c glue.CertiCoq.Benchmarks.tests.$@_opt_ll.c
	ccomp -o $@_ccomp -O2 $@_main.c gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue.CertiCoq.Benchmarks.tests.$@.c
	# $(CCOMPILER) -o $@_cps -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue.CertiCoq.Benchmarks.tests.$@_cps.c
	# $(CCOMPILER) -o $@_cps_opt -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps_opt.c glue.CertiCoq.Benchmarks.tests.$@_cps_opt.c


## Compile with compcert
# $(TESTS): $(CFILES)
# 	ccomp -o $@_cps_ccomp -O2 $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue.CertiCoq.Benchmarks.tests.$@_cps.c
# 	

## Compile with Clang, generate LLVM, and modify the calling convention
# $(TESTS): $(CFILES)
#         # From Matthew's scripts
#         # Compile to LLVM
# 	clang -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@.c -emit-llvm
#         # Run script to modify the calling convention
# 	python mod.py CertiCoq.Benchmarks.tests.$@.ll CertiCoq.Benchmarks.tests.$@CC.ll
# 	rm CertiCoq.Benchmarks.tests.$@.ll
#         # Compile to machine code		
# 	clang -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue.CertiCoq.Benchmarks.tests.$@.c CertiCoq.Benchmarks.tests.$@CC.ll -o $@
#         # Same for CPS	
# 	clang -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_cps.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_cps.ll CertiCoq.Benchmarks.tests.$@_cpsCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_cps.ll
# 	clang -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c glue.CertiCoq.Benchmarks.tests.$@.c CertiCoq.Benchmarks.tests.$@_cpsCC.ll -o $@_cps
#         # Same for -direct -O 1 	
# 	clang -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_opt.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_opt.ll CertiCoq.Benchmarks.tests.$@_optCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_opt.ll
# 	clang -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue.CertiCoq.Benchmarks.tests.$@.c CertiCoq.Benchmarks.tests.$@_optCC.ll -o $@_opt
#         # Same for CPS -O 1 	
# 	clang -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_cps_opt.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_cps_opt.ll CertiCoq.Benchmarks.tests.$@_cps_optCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_cps_opt.ll
# 	clang -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c glue.CertiCoq.Benchmarks.tests.$@.c CertiCoq.Benchmarks.tests.$@_cps_optCC.ll -o $@_cps_opt
#         # Same for -direct -O 1 -lift-all (i.e. -anf-config 9) 	
# 	clang -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_opt_ll.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_opt_ll.ll CertiCoq.Benchmarks.tests.$@_opt_llCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_opt_ll.ll
# 	clang -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue.CertiCoq.Benchmarks.tests.$@.c CertiCoq.Benchmarks.tests.$@_opt_llCC.ll -o $@_opt_ll

run: run.sh
	sh run.sh 10
