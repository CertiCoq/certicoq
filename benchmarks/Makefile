CCOMPILER=gcc

all: benchmarks # copy demo demo1 demo2

benchmarks: copy benchmark binom color vs sha runbenchmarks

copy:
	cp ../theories/Runtime/gc.c ./
	cp ../theories/Runtime/gc.h ./
	cp ../theories/Runtime/values.h ./
	cp ../theories/Runtime/main.c ./
	cp ../theories/Runtime/config.h ./

clean:
	rm -f ./gc.c
	rm -f ./gc.h
	rm -f ./values.h
	rm -f ./main.c
	rm -f ./config.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h

demo: demo.v
	coqc demo.v

demo1: maindemo1.c demo.demo1.c glue.demo.demo1.c
	$(CCOMPILER) -o demo1 -w -O2 maindemo1.c gc.c demo.demo1.c glue.demo.demo1.c

demo2: maindemo2.c demo.demo2.c glue.demo.demo2.c
	$(CCOMPILER) -o demo2 -w -O2 maindemo2.c gc.c demo.demo2.c glue.demo.demo2.c

# vs: demo.is_valid.c
# 	$(CCOMPILER) -o vs -w -O2 mainvs.c gc.c demo.is_valid.c

binom: CertiCoq.Benchmarks.Binom.main.c
	$(CCOMPILER) -o binom -w -O2 main.c gc.c CertiCoq.Benchmarks.Binom.main.c

sha: benchmark_certicoq.benchsha.c
	$(CCOMPILER) -o sha -w -O2 main.c gc.c benchmark_certicoq.benchsha.c


color: CertiCoq.Benchmarks.Color.main.c
	$(CCOMPILER) -o color -w -O2 main.c gc.c CertiCoq.Benchmarks.Color.main.c

vs: CertiCoq.Benchmarks.vs.main_h.c
	$(CCOMPILER) -o vs -w -O2 main.c gc.c CertiCoq.Benchmarks.vs.main_h.c

benchmark: benchmark_certicoq.v
	coqc benchmark_certicoq.v

runbenchmarks:
	echo "binom"
	./binom
	echo "color"
	./color
	echo "vs"
	./vs
	echo "sha"
	./sha
