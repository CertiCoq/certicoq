VFILES:=RandyPrelude.v AstCommon.v exceptionMonad.v Common.v

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VFILES)
	coq_makefile -R . Common $(VFILES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
