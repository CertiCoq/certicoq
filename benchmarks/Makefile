COQOPTS = -R ../plugin CertiCoq.Plugin -I ../plugin -R ../benchmarks CertiCoq.Benchmarks

all: copy demo demo1 demo2

copy:
	cp ../theories/Runtime/gc.c ./
	cp ../theories/Runtime/gc.h ./
	cp ../theories/Runtime/values.h ./
	cp ../theories/Runtime/main.c ./
	cp ../theories/Runtime/config.h ./
demo: demo.v
	coqc $(COQOPTS) demo.v

demo0: maindemo0.c gc.c CertiCoq.Benchmarks.demo.demo0.c
	gcc -o demo0 -Wno-everything -O2 $+

demo1: maindemo1.c gc.c CertiCoq.Benchmarks.demo.demo1.c
	gcc -o demo1 -Wno-everything -O2 $+

demo2: maindemo2.c gc.c CertiCoq.Benchmarks.demo.demo2.c
	gcc -o demo2 -Wno-everything -O2 $+

vs: CertiCoq.Benchmarks.demo.is_valid.c
	gcc -o vs -Wno-everything -O2 mainvs.c gc.c $<

%.vo: %.v
	coqc ${COQOPTS} $<
