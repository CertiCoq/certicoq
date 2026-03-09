.PHONY: all certirocqc certirocqchk test install clean

all: certirocqc certirocqchk

certirocqc:
	$(MAKE) -C certirocqc

certirocqchk:
	$(MAKE) -C certirocqchk

test:
	$(MAKE) -C certirocqc test
	$(MAKE) -C certirocqchk test

install:
	$(MAKE) -C certirocqc install
	$(MAKE) -C certirocqchk install

clean:
	$(MAKE) -C certirocqc clean
	$(MAKE) -C certirocqchk clean
