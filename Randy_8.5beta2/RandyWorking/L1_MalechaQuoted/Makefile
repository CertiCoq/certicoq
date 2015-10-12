VFILES:=L1.v\
  malecha_L1.v\
  wNorm.v\
  wcbvEval.v\
  awndEval.v\
  wndEval.v\
  program.v\
  term.v

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VFILES)
	coq_makefile -R ../common Common -R . L1 $(VFILES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
