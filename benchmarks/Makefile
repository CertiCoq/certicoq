COQOPTS = -R ../plugin CertiCoq.Plugin -I ../plugin -R lib Benchmarks

all: copy demo demo1 demo2
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
	rm -f ./*.vo

demo: demo.v
	coqc $(COQOPTS) demo.v

demo0: maindemo0.c gc.c CertiCoq.Benchmarks.demo.demo0.c glue.CertiCoq.Benchmarks.demo.demo0.c
	$(CCOMPILER) -o demo0 -Wno-everything -O2 $+

demo1: maindemo1.c gc.c CertiCoq.Benchmarks.demo.demo1.c glue.CertiCoq.Benchmarks.demo.demo1.c
	$(CCOMPILER) -o demo1 -Wno-everything -O2 $+

demo2: maindemo2.c gc.c CertiCoq.Benchmarks.demo.demo2.c glue.CertiCoq.Benchmarks.demo.demo2.c
	$(CCOMPILER) -o demo2 -Wno-everything -O2 $+

vs: CertiCoq.Benchmarks.demo.is_valid.c
	$(CCOMPILER) -o vs -Wno-everything -O2 mainvs.c gc.c $<

%.vo: %.v
	coqc ${COQOPTS} $<
