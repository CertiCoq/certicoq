CCOMPILER = clang # ccomp # gcc

PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiCoq/CertiCoqCheck
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -I ${COQLIB}/user-contrib/MetaCoq/Template -open Metacoq_template_plugin -I ../../cplugin -open Certicoq_vanilla_plugin \
	-I . -linkpkg -dontlink str,unix,dynlink,threads,zarith  -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.CertiCoqCheck.compile.certicoqchk.c CertiCoq.CertiCoqCheck.compile.certicoqchk.c
CFILES = certicoqchk_wrapper.c ${GENCFILES}
COQOPTS = -Q ../../theories/Codegen CertiCoq.Codegen -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/LambdaANF CertiCoq.LambdaANF -Q ../../theories/LambdaBoxLocal CertiCoq.LambdaBoxLocal \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/Glue CertiCoq.Glue \
	-Q ../../theories/LambdaBoxMut CertiCoq.LambdaBoxMut \
	-Q ../../plugin CertiCoq.Plugin \
	-I ../../plugin \
	-Q ../../cplugin CertiCoq.VanillaPlugin \
	-I ../../cplugin \
	-Q . CertiCoq.CertiCoqCheck

RUNTIME_DIR = ../../plugin/runtime
RUNTIME_FILES = ${RUNTIME_DIR}/gc_stack.o ${RUNTIME_DIR}/prim_floats.o ${RUNTIME_DIR}/prim_int63.o ${RUNTIME_DIR}/coq_c_ffi.o

CCOMPILEROPTS = -fPIC -g -c -I . -I ${RUNTIME_DIR} -I ${OCAMLLIB} -w -Wno-everything -O2
# ccomp: CCOMPILEROPTS = -g -c -I . -I ${OCAMLLIB} -O2

plugin: compile.vo Loader.vo

test: test.vo

test.vo: test.v
	ulimit -Ss 65500 && ulimit -a && coqc -I . ${COQOPTS} test.v

clean: 
	rm *.cm* *.o *.vo

Loader.vo: Loader.v certicoqchk_plugin.cmxs
	coqc ${COQOPTS} Loader.v

compile.vo ${GENCFILES} &: compile.v
	coqc ${COQOPTS} $<

%.o: %.c
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certicoqchk_plugin.cmxs: certicoqchk_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} -shared -linkall -o $@ $+

certicoqchk_plugin.cmx: certicoqchk_plugin_wrapper.cmx certicoqchk.cmx g_certicoqchk.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoqchk_plugin.cmxa: certicoqchk_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_certicoqchk.ml: g_certicoqchk.mlg certicoqchk.cmi certicoqchk_plugin_wrapper.cmx
	coqpp $<

certicoqchk_wrapper.c: compile.vo

certicoqchk_plugin_wrapper.cmx: certicoqchk_wrapper.o

certicoqchk.cmx: certicoqchk_plugin_wrapper.cmx certicoqchk_plugin_wrapper.cmi

%.mli: %.ml
	[ -f "$@" ] || ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoqchk_plugin -o $@ $<

install: Loader.vo certicoqchk_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 Loader.v Loader.vo certicoqchk_plugin.cmx* "$(COQLIBINSTALL)"

.PHONY: plugin test