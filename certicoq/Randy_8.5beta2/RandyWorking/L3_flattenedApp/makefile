VFILES:=L3.v\
 unaryApplications.v\
 wNorm.v\
 wcbvEval.v\
 wndEval.v\
 program.v\
 term.v

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VFILES)
	coq_makefile -R ../common Common -R\
	                ../L1_MalechaQuoted L1 -R\
	                ../L2_typeStrippedL1 L2 -R\
	                . L3 $(VFILES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
