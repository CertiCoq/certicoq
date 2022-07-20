CCOMPILER = clang # gcc takes ages

PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
COQLIB = $(shell coqc -where)
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -I ${COQLIB}/user-contrib/MetaCoq/Template -open Metacoq_template_plugin -I ${COQLIB}/user-contrib/CertiCoq/VanillaPlugin -open Certicoq_vanilla_plugin \
	-I . -linkpkg -dontlink str,unix,dynlink,threads,zarith  -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.CertiCoqCheck.compile.certicoqchk.c CertiCoq.CertiCoqCheck.compile.certicoqchk.c
CFILES = certicoqchk_wrapper.c ${GENCFILES} gc_stack.c print.c
COQOPTS = -Q ../../theories/L7 CertiCoq.L7 -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/L6_PCPS CertiCoq.L6 -Q ../../theories/L4_deBruijn CertiCoq.L4 \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/L2k_noCnstrParams CertiCoq.L2k -Q . CertiCoq.CertiCoqCheck

plugin: compile.vo Loader.vo

test: test.vo

test.vo: plugin test.v
	ulimit -Ss 65500 && ulimit -a && coqc -I . -Q . CertiCoq.CertiCoqCheck test.v

clean: 
	rm *.cm* *.o *.vo

Loader.vo: Loader.v certicoqchk_plugin.cmxs
	coqc -Q . CertiCoq.CertiCoqCheck Loader.v

compile.vo ${GENCFILES} &: compile.v
	coqc ${COQOPTS} $<

%.o: %.c
	$(CCOMPILER) -fPIC -g -c -I . -I ${OCAMLLIB} -w -Wno-everything -O2 -o $@ $<

certicoqchk_plugin.cmxs: certicoqchk_plugin.cmxa ${CFILES:.c=.o}
	ocamlfind opt ${OCAMLOPTS} -shared -linkall -o $@ $+

certicoqchk_plugin.cmx: certicoqchk_plugin_wrapper.cmx certicoqchk.cmx g_certicoqchk.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoqchk_plugin.cmxa: certicoqchk_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_certicoqchk.ml: g_certicoqchk.mlg certicoqchk.cmx certicoqchk_plugin_wrapper.cmx
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

.PHONY: plugin test