CCOMPILER := $(shell { command -v clang-11 || command -v clang; } 2>/dev/null)

-include ../../Makefile.conf

ifeq '$(CERTICOQ_CONFIG)' 'local'
  ifeq ($(shell which cygpath 2>/dev/null),)
  OCAMLPATH := $(shell pwd)/../../cplugin/:$(OCAMLPATH)
  else
  OCAMLPATH := $(shell cygpath -m `pwd`)/../../cplugin/;$(OCAMLPATH)
  endif
  export OCAMLPATH

  COQOPTS = -Q ../../theories/Codegen CertiCoq.Codegen -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/LambdaANF CertiCoq.LambdaANF -Q ../../theories/LambdaBoxLocal CertiCoq.LambdaBoxLocal \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/Glue CertiCoq.Glue \
	-Q ../../theories/LambdaBoxMut CertiCoq.LambdaBoxMut \
	-Q ../../plugin CertiCoq.Plugin \
	-I ../../plugin \
	-Q ../../cplugin CertiCoq.VanillaPlugin \
	-I ../../cplugin \
	-Q . CertiCoq.CertiCoqCheck \
	-I .
  TESTCOQOPTS = $(COQOPTS)
else
  COQOPTS = -I . -Q . CertiCoq.CertiCoqCheck
  TESTCOQOPTS = 
endif

PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiCoq/CertiCoqCheck
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -package coq-metacoq-template-ocaml.plugin -open Metacoq_template_plugin -package coq-certicoq-vanilla.plugin -open Certicoq_vanilla_plugin \
	-I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.c CertiCoq.CertiCoqCheck.compile.certicoqchk.c
CFILES = certicoqchk_wrapper.c ${GENCFILES}

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = ${RUNTIME_DIR}/gc_stack.o ${RUNTIME_DIR}/prim_floats.o ${RUNTIME_DIR}/prim_string.o ${RUNTIME_DIR}/prim_int63.o ${RUNTIME_DIR}/coq_ffi.o

CCOMPILEROPTS = -fPIC -g -c -I . -I ${RUNTIME_DIR} -I ${OCAMLLIB} -w -Wno-everything -O2
# ccomp: CCOMPILEROPTS = -g -c -I . -I ${OCAMLLIB} -O2

.PHONY: certicoqchk
.PRECIOUS: $(GENCFILES)

plugin: compile.vo certicoqchk

test: test.vo

test.vo: test.v
	ulimit -Ss 65500 && coqc ${TESTCOQOPTS} test.v

clean: 
	make -f Makefile.certicoqchk clean
	rm -f *.cm* *.o *.vo

Makefile.certicoqchk: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.certicoqchk

certicoqchk: Makefile.certicoqchk certicoqchk_plugin.cmxs
	$(MAKE) -f Makefile.certicoqchk

compile.vo ${GENCFILES} &: compile.v
	coqc ${COQOPTS} $<

%.o: %.c
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certicoqchk_plugin.cmxs: certicoqchk_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} -shared -o $@ $+

certicoqchk_plugin.cmx: certicoqchk_plugin_wrapper.cmx certicoqchk.cmx g_certicoqchk.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoqchk_plugin.cmxa: certicoqchk_plugin.cmx
	ocamlfind opt -linkall ${OCAMLOPTS} -a -o $@ $<

g_certicoqchk.ml: g_certicoqchk.mlg certicoqchk.cmx certicoqchk_plugin_wrapper.cmx
	coqpp $<

certicoqchk_wrapper.c: compile.vo

certicoqchk_plugin_wrapper.cmx: certicoqchk_wrapper.o

certicoqchk.cmx: certicoqchk_plugin_wrapper.cmx certicoqchk_plugin_wrapper.cmi

# %.mli: %.ml
# 	[ -f "$@" ] || ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin -o $@ $<

install: Loader.vo certicoqchk_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 Loader.v Loader.vo certicoqchk_plugin.cmx* "$(COQLIBINSTALL)"
	make -f Makefile.certicoqchk install
	ocamlfind install -add coq-certicoqchk certicoqchk_plugin.cmx* certicoqchk_plugin.cmi

.PHONY: plugin test

.NOTPARALLEL:
