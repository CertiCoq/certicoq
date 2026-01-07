DIRS=lib axioms ocaml opt wasm
CLEAN_DIRS=$(addprefix clean,$(DIRS))

.PHONY: all clean plugin $(DIRS) $(CLEAN_DIRS)

default: all

all: $(DIRS)

$(DIRS): plugin

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C $@

axioms ocaml opt wasm: lib
	$(MAKE) -C $@ run

plugin:
	$(MAKE) -C .. $@

$(CLEAN_DIRS): clean%:
	$(MAKE) -C $* clean

clean: $(CLEAN_DIRS)
