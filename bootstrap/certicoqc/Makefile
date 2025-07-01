# clang compiler 
CCOMPILER := $(shell { command -v clang-11 || command -v clang || command -v gcc; } 2>/dev/null)
# clang options
CCOMPILEROPTS = -fPIC -fomit-frame-pointer -g -c -I . -I $(RUNTIME_DIR) -I ${OCAMLLIB} -w -Wno-everything -O2
UNAME=$(shell uname -s)
ifeq '$(UNAME)' 'Darwin'
  SED= $(shell which gsed)
  ifeq '$(SED)' ''
   $(error "Must have gsed installed on MacOS, try e.g. brew install gsed")
  endif
else
SED=`which gsed || which sed`
endif

# CompCert compiler
CCOMPCOMPILER := $(CCOMPILER)
# $(shell { command -v ccomp; } 2>/dev/null)
# ccomp options
CCOMPCOMPILEROPTS = $(CCOMPILEROPTS)
# -g -c -I . -I $(RUNTIME_DIR) -I ${OCAMLLIB} -w -flongdouble -O2

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
	-Q ../../theories/CodegenWasm CertiCoq.CodegenWasm\
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/Glue CertiCoq.Glue \
	-Q ../../theories/LambdaBoxMut CertiCoq.LambdaBoxMut \
	-Q ../../plugin CertiCoq.Plugin \
	-I ../../plugin \
	-Q ../../cplugin CertiCoq.VanillaPlugin \
	-I ../../cplugin \
	-Q theories CertiCoq.CertiCoqC \
	-I .

  TESTCOQOPTS = $(COQOPTS)
else
 ifeq '$(CERTICOQ_CONFIG)' 'global'
  COQOPTS = -I . -Q theories CertiCoq.CertiCoqC
  TESTCOQOPTS = 
 else
  $(error "Must first set CERTICOQ_CONFIG by running ./configure.sh")
 endif
endif

PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiCoq/CertiCoqC
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -package coq-metacoq-template-ocaml.plugin -open Metacoq_template_plugin -package coq-certicoq-vanilla.plugin -open Certicoq_vanilla_plugin \
	-I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  
GENCFILES = glue.c CertiCoq.CertiCoqC.CertiCoqC.certicoqc.c
CFILES = certicoqc_wrapper.c $(GENCFILES)

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = $(RUNTIME_DIR)/gc_stack.o $(RUNTIME_DIR)/prim_floats.o $(RUNTIME_DIR)/prim_int63.o $(RUNTIME_DIR)/coq_c_ffi.o

VFILES = theories/Loader.v theories/PrimInt63.v theories/PrimFloats.v theories/CertiCoqC.v

.PHONY: runtime certicoqc

all: plugin

plugin: theories/compile.vo certicoqc

runtime: $(RUNTIME_FILES:.o=.c)
	cd $(RUNTIME_DIR) && $(MAKE)

Makefile.certicoqc: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.certicoqc

certicoqc: runtime Makefile.certicoqc certicoqc_plugin.cmxs
	$(MAKE) -f Makefile.certicoqc

test: test.vo

test.vo: test.v
	mkdir -p tests
	ulimit -a
	ulimit -H -a
	ulimit -Ss unlimited && ulimit -s unlimited && coqc $(TESTCOQOPTS) test.v

clean: Makefile.certicoqc
	make -f Makefile.certicoqc clean
	rm -f *.cm* *.o *.vo theories/*.vo

theories/CertiCoqC.vo: theories/CertiCoqC.v
	coqc $(COQOPTS) $<

theories/compile.v: theories/CertiCoqC.vo

theories/compile.vo CertiCoq.CertiCoqC.compile.certicoqc.c &: theories/compile.v
	coqc $(COQOPTS) $<

g_certicoqc.ml: g_certicoqc.mlg certicoqc.cmx certicoqc_plugin_wrapper.cmx
	coqpp $<

certicoqc.cmx: certicoqc_plugin_wrapper.cmx

.PRECIOUS: $(GENCFILES)

$(GENCFILES:%.c=%.o): %.o: %.c
	$(SED) -f unicode.sed -i $<
	$(CCOMPCOMPILER) $(CCOMPCOMPILEROPTS) -o $@ $<

certicoqc_wrapper.o: %.o: %.c
	$(SED) -f unicode.sed -i $<
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certicoqc_plugin.cmx: certicoqc_plugin_wrapper.cmx certicoqc.cmx g_certicoqc.cmx
	ocamlfind opt $(OCAMLOPTS) -pack -o $@ $+

certicoqc_plugin.cmxa: certicoqc_plugin.cmx
	ocamlfind opt -linkall $(OCAMLOPTS) -a -o $@ $<

certicoqc_plugin.cmxs: certicoqc_plugin.cmxa $(CFILES:.c=.o) $(RUNTIME_FILES)
	ocamlfind ocamlopt $(OCAMLOPTS) -shared -o $@ $+

.PRECIOUS: %.cmi
%.cmi: %.mli
	ocamlfind opt $(PKGS) $(OCAMLOPTS) -for-pack Certicoqc_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c $(PKGS) $(OCAMLOPTS) -for-pack Certicoqc_plugin -o $@ $<

install: theories/compile.vo certicoqc_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 theories/CertiCoqC.v theories/CertiCoqC.vo theories/compile.v theories/compile.vo certicoqc_plugin.cmx* "$(COQLIBINSTALL)"
	make -f Makefile.certicoqc install
	ocamlfind install -add coq-certicoqc certicoqc_plugin.cmx* certicoqc_plugin.cmi

.PHONY: plugin test

.NOTPARALLEL:
