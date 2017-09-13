MODULES    := $(patsubst %.v,%,$(wildcard *.v))
TESTS      := 
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R ../theories ExtLib

.PHONY: coq clean admit depgraph toplevel whitespace

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) \
          | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
          > Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) \
          | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
          > Makefile.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

whitespace:
	@ ./../tools/whitespace.sh $(MODULES:%=%.v)

admit:
	@ grep -n -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)
