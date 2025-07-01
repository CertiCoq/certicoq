COQOPTS = -R ../ CertiCoq.Benchmarks -R lib CertiCoq.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WASMFILES=$(patsubst %, CertiCoq.Benchmarks.tests.%.wasm, $(TESTS))

OS=$(shell uname)
STACKSIZE=$(if $(filter Linux,$(OS)),unlimited,65532)

all: run_tests run_primitive_unit_tests

.PHONY: all default clean lib cleanlib tests $(TESTS)

$(WASMFILES): tests

lib/Makefile:
	cd ../lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C ../lib

cleanlib:
	$(MAKE) clean -C ../lib

run_tests: lib tests.v $(WASMFILES)
	ulimit -s $(STACKSIZE) && coqc $(COQOPTS) tests.v
	ulimit -s $(STACKSIZE) && ./run_wasm_benchmarks.py

run_primitive_unit_tests: lib
	coqc -quiet -R ./ CertiCoq.Benchmarks uint63_unit_tests.v
	node --stack-size=10000000 js/run_uint63_unit_tests.js

clean:
	rm -f *.wat *.wasm *.cwasm *.tests.*.js *.ir
	rm -f *.vo *.vos *.vok *.glob
