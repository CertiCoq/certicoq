DATA       := Monads Set Map Graph
PACKAGES   := Core Tactics Structures Data $(DATA:%=Data/%) Generic Relations Programming Recur
EXCLUDES   := Generic/DerivingData Structures/PMonad
MODULES    := $(foreach pkg,$(PACKAGES),$(patsubst %.v,%,$(wildcard $(pkg)/*.v))) ExtLib
MODULES    := $(filter-out $(EXCLUDES),$(MODULES)) ExtLib Tactics
TESTS      :=
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . ExtLib

.PHONY: coq clean admit depgraph toplevel whitespace

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	@ coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

install: Makefile.coq coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	@ for i in $(VS:%.v=%.vo); do \
         rm -f $(shell coqc -where)/user-contrib/ExtLib/$$i; \
        done


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
