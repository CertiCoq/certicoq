all: copy demo demo1 demo2

benchmarks: copy benchmark binom color vs sha runbenchmarks

copy:
	cp ../theories/Runtime/gc.c ./
	cp ../theories/Runtime/gc.h ./
	cp ../theories/Runtime/values.h ./
	cp ../theories/Runtime/main.c ./
	cp ../theories/Runtime/config.h ./
demo: demo.v
	coqc demo.v

demo1: maindemo1.c demo.demo1.c
	gcc -o demo1 -Wno-everything -O2 maindemo1.c gc.c demo.demo1.c

demo2: maindemo2.c demo.demo2.c
	gcc -o demo2 -Wno-everything -O2 maindemo2.c gc.c demo.demo2.c

#vs: demo.is_valid.c
#	gcc -o vs -Wno-everything -O2 mainvs.c gc.c demo.is_valid.c

binom: CertiCoq.Benchmarks.Binom.main.c
	gcc -o binom -Wno-everything -O2 main.c gc.c CertiCoq.Benchmarks.Binom.main.c

sha: benchmark_certicoq.benchsha.c
	gcc -o sha -Wno-everything -O2 main.c gc.c benchmark_certicoq.benchsha.c


color: CertiCoq.Benchmarks.Color.main.c
	gcc -o color -Wno-everything -O2 main.c gc.c CertiCoq.Benchmarks.Color.main.c

vs: CertiCoq.Benchmarks.vs.main_h.c
	gcc -o vs -Wno-everything -O2 main.c gc.c CertiCoq.Benchmarks.vs.main_h.c



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
