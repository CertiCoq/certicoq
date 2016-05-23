
all: theories/Makefile libraries/Makefile
	$(MAKE) -C libraries
	$(MAKE) -C libraries/SquiggleEq
	$(MAKE) -C theories
	

theories/Makefile:
	cd theories;coq_makefile -f _CoqProject -o Makefile

libraries/Makefile:
	cd libraries;coq_makefile -f _CoqProject -o Makefile


	
