PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
OCAMLOPTS = -I ../../_opam/lib/coq/user-contrib/MetaCoq/Template -open Metacoq_template_plugin -I ../../_opam/lib/coq/user-contrib/CertiCoq/Plugin -open Certicoq_plugin -I . -linkpkg -dontlink str,unix,dynlink,threads,zarith  -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.Benchmarks.certicoq_pipeline.certicoq_pipeline.certicoq_pipeline.c \
		CertiCoq.Benchmarks.certicoq_pipeline.certicoq_pipeline.certicoq_pipeline.c
CFILES = certicoqc_pipeline_wrapper.c ${GENCFILES} gc_stack.c print.c
# ffi.CertiCoq.Benchmarks.certicoq_pipeline.certicoq_pipeline.QuoteFFI.c
COQOPTS = -Q ../../theories/L7 CertiCoq.L7 -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/L6_PCPS CertiCoq.L6 -Q ../../theories/L4_deBruijn CertiCoq.L4 \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/L2k_noCnstrParams CertiCoq.L2k -Q .. CertiCoq.Benchmarks

plugin: certicoq_pipeline.vo Loader.vo

test: test.vo

test.vo: plugin test.v
	coqc -I . -Q . CertiCoq.Benchmarks.certicoq_pipeline test.v

clean: 
	rm *.cm*

Loader.vo: Loader.v certicoqc_plugin.cmxs
	coqc -Q . CertiCoq.Benchmarks.certicoq_pipeline Loader.v

certicoq_pipeline.vo ${GENCFILES} &: certicoq_pipeline.v
	coqc ${COQOPTS} $<

%.o: %.c
	gcc -c -I . -I ../../_opam/lib/ocaml -Wno-everything -O2 -fomit-frame-pointer -o $@ $<

certicoqc_plugin.cmxs: certicoqc_plugin.cmxa ${CFILES:.c=.o}
	ocamlfind opt ${OCAMLOPTS} -shared -linkall -o $@ $+

certicoqc_plugin.cmx: certicoq_pipeline.cmx certicoqc.cmx g_certicoqc.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoqc_plugin.cmxa: certicoqc_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_certicoqc.ml: g_certicoqc.mlg certicoqc.cmx certicoq_pipeline.cmx
	coqpp $<

certicoqc.cmx: certicoq_pipeline.cmx

# g_certicoqc.mli: g_certicoqc.ml
# ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoqc_plugin -o $@ $<

.PHONY: plugin test