all: certicoqc certicoqchk

certicoqc: 
	$(MAKE) -C certicoqc

certicoqchk:
	$(MAKE) -C certicoqchk

test:
	$(MAKE) -C certicoqc test
	$(MAKE) -C certicoqchk test

install:
	$(MAKE) -C certicoqc install
	$(MAKE) -C certicoqchk install
