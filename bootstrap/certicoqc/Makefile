CCOMPILER = clang # ccomp # gcc takes ages

PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiCoq/CertiCoqC
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -I ${COQLIB}/user-contrib/MetaCoq/Template -open Metacoq_template_plugin -I ../../cplugin -open Certicoq_vanilla_plugin \
	-I . -linkpkg -dontlink str,unix,dynlink,threads,zarith  -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.CertiCoqC.compile.certicoqc.c CertiCoq.CertiCoqC.compile.certicoqc.c
CFILES = certicoqc_wrapper.c ${GENCFILES}

RUNTIME_DIR = ../../plugin/runtime
RUNTIME_FILES = ${RUNTIME_DIR}/gc_stack.o ${RUNTIME_DIR}/prim_floats.o ${RUNTIME_DIR}/prim_int63.o ${RUNTIME_DIR}/coq_c_ffi.o

# ffi.CertiCoq.CertiCoqC.compile.QuoteFFI.c
COQOPTS = -Q ../../theories/L7 CertiCoq.L7 -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/L6_PCPS CertiCoq.L6 -Q ../../theories/L4_deBruijn CertiCoq.L4 \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/Glue CertiCoq.Glue \
	-Q ../../theories/L2k_noCnstrParams CertiCoq.L2k \
	-Q ../../plugin CertiCoq.Plugin \
	-I ../../plugin \
	-Q ../../cplugin CertiCoq.VanillaPlugin \
	-I ../../cplugin \
	-Q theories CertiCoq.CertiCoqC

VFILES = theories/Loader.v theories/PrimInt63.v theories/PrimFloats.v theories/CertiCoqC.v

CCOMPILEROPTS = -fPIC -g -c -I . -I ../../plugin/runtime -I ${OCAMLLIB} -w -Wno-everything -O2
# ccomp CCOMPOPTS = -g -c -I . -I ${OCAMLLIB} -Wno-int-conversion -O2

.PHONY: certicoqc

plugin: theories/compile.vo certicoqc

Makefile.certicoqc: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.certicoqc
	
certicoqc: Makefile.certicoqc certicoqc_plugin.cmxs
	$(MAKE) -f Makefile.certicoqc

test: test.vo

test.vo: test.v
	mkdir -p tests
	ulimit -Ss 65500 && ulimit -a && coqc -I . ${COQOPTS} test.v

clean: 
	rm *.cm* *.o *.vo

theories/compile.vo ${GENCFILES} &: theories/compile.v
	coqc ${COQOPTS} $<

%.o: %.c
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certicoqc_plugin.cmxs: certicoqc_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} -shared -linkall -o $@ $+

certicoqc_plugin.cmx: certicoqc_plugin_wrapper.cmx certicoqc.cmx g_certicoqc.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoqc_plugin.cmxa: certicoqc_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_certicoqc.ml: g_certicoqc.mlg certicoqc.cmx certicoqc_plugin_wrapper.cmx
	coqpp $<

certicoqc_wrapper.c: theories/compile.vo

certicoqc.cmx: certicoqc_plugin_wrapper.cmx

%.mli: %.ml
	[ -f "$@" ] || ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin -o $@ $<

install: theories/compile.vo certicoqc_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 theories/compile.v theories/compile.vo certicoqc_plugin.cmx* "$(COQLIBINSTALL)"
	make -f Makefile.certicoqc install

.PHONY: plugin test