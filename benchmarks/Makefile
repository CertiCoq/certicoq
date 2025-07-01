COQOPTS = -R ./ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
CFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%_cps.c, $(TESTS)) $(patsubst %, CertiCoq.Benchmarks.tests.%.c, $(TESTS))
# Names of the generated executables
EXEC=$(TESTS) $(patsubst %, %_cps, $(TESTS)) $(patsubst %, %_cps_opt, $(TESTS)) $(patsubst %, %_opt, $(TESTS))
INCLUDE=../runtime

all: lib tests exec run run_wasm
default: exec run

.PHONY: all default clean lib cleanlib tests run $(TESTS)

$(CFILES): tests
exec: $(TESTS)

# copy:
# 	cp ../theories/Runtime/m.h ./
# 	cp ../theories/Runtime/gc.c ./
# 	cp ../theories/Runtime/gc.h ./
# 	cp ../theories/Runtime/gc_stack.c ./
# 	cp ../theories/Runtime/gc_stack.h ./
# 	cp ../theories/Runtime/values.h ./
# 	cp ../theories/Runtime/main.c ./
# 	cp ../theories/Runtime/config.h ./
# 	cp ../theories/Runtime/mod.py ./

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
	$(CCOMPILER) -o $@ 			-w -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) $@_main.c $(INCLUDE)/gc_stack.c CertiCoq.Benchmarks.tests.$@.c glue_$@.c
	$(CCOMPILER) -o $@_opt 		-w -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) $@_main.c $(INCLUDE)/gc_stack.c CertiCoq.Benchmarks.tests.$@_opt.c glue_$@.c
	$(CCOMPILER) -o $@_opt_ll 	-w -Wno-everything -O2 -fomit-frame-pointer -I$(INCLUDE) $@_main.c $(INCLUDE)/gc_stack.c CertiCoq.Benchmarks.tests.$@_opt_ll.c glue_$@.c
	# ccomp -o $@_ccomp -O2 $@$@_.c__
	# $(CCOMPILER) -o $@_cps -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue_$@_cps.c
	# $(CCOMPILER) -o $@_cps_opt -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps_opt.c glue_$@_cps.c


## Compile with compcert
# $(TESTS): $(CFILES)
# 	ccomp -o $@_cps_ccomp -O2 $@_main.c gc.c CertiCoq.Benchmarks.tests.$@_cps.c glue_$@_cps.c
# 	

## Compile with Clang, generate LLVM, and modify the calling convention
# $(TESTS): $(CFILES)
#         # From Matthew's scripts
#         # Compile to LLVM
# 	clang-11 -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@.c -emit-llvm
#         # Run script to modify the calling convention
# 	python mod.py CertiCoq.Benchmarks.tests.$@.ll CertiCoq.Benchmarks.tests.$@CC.ll
# 	rm CertiCoq.Benchmarks.tests.$@.ll
#         # Compile to machine code		
# 	clang-11 -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue_$@.c CertiCoq.Benchmarks.tests.$@CC.ll -o $@
#         # Same for CPS	
# 	clang-11 -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_cps.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_cps.ll CertiCoq.Benchmarks.tests.$@_cpsCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_cps.ll
# 	clang-11 -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c glue_$@.c CertiCoq.Benchmarks.tests.$@_cpsCC.ll -o $@_cps
#         # Same for -direct -O 1 	
# 	clang-11 -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_opt.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_opt.ll CertiCoq.Benchmarks.tests.$@_optCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_opt.ll
# 	clang-11 -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue_$@.c CertiCoq.Benchmarks.tests.$@_optCC.ll -o $@_opt
#         # Same for CPS -O 1 	
# 	clang-11 -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_cps_opt.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_cps_opt.ll CertiCoq.Benchmarks.tests.$@_cps_optCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_cps_opt.ll
# 	clang-11 -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc.c glue_$@.c CertiCoq.Benchmarks.tests.$@_cps_optCC.ll -o $@_cps_opt
#         # Same for -direct -O 1 -lift-all (i.e. -anf-config 9) 	
# 	clang-11 -Wno-everything -S -O2 -fomit-frame-pointer CertiCoq.Benchmarks.tests.$@_opt_ll.c -emit-llvm
# 	python mod.py CertiCoq.Benchmarks.tests.$@_opt_ll.ll CertiCoq.Benchmarks.tests.$@_opt_llCC.ll
# 	rm CertiCoq.Benchmarks.tests.$@_opt_ll.ll
# 	clang-11 -Wno-everything -O2 -fomit-frame-pointer $@_main.c gc_stack.c glue_$@.c CertiCoq.Benchmarks.tests.$@_opt_llCC.ll -o $@_opt_ll

run: run.sh
	sh run.sh 10

run_wasm:
	@echo "\nRunning CertiCoq-Wasm test suite"
	make -C wasm run_tests
	@echo "\nRunning CertiCoq-Wasm primitive unit tests"
	make -C wasm run_primitive_unit_tests
