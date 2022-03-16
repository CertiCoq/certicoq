PKGS = -package coq-core,coq-core.clib,coq-core.config,coq-core.engine,coq-core.gramlib,coq-core.interp,coq-core.kernel,coq-core.lib,coq-core.library,coq-core.toplevel,coq-core.vernac,coq-core.plugins.ltac
OCAMLOPTS = -I ../../_opam/lib/coq/user-contrib/MetaCoq/Template -open Metacoq_template_plugin -I . -linkpkg -dontlink str,unix,dynlink,threads,zarith  -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.metacoq_erasure.c \
		CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.metacoq_erasure.c
CFILES = certicoq_erasure.c ${GENCFILES} gc_stack.c print.c
# ffi.CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.QuoteFFI.c
COQOPTS = -Q ../../theories/L7 CertiCoq.L7 -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/L6_PCPS CertiCoq.L6 -Q ../../theories/L4_deBruijn CertiCoq.L4 \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/L2k_noCnstrParams CertiCoq.L2k -Q .. CertiCoq.Benchmarks

plugin: metacoq_erasure.vo Loader.vo

test: test.vo

test.vo: plugin test.v
	coqc -I . -Q . CertiCoq.Benchmarks.metacoq_erasure test.v

clean: 
	rm *.cm*

Loader.vo: Loader.v certicoq_erasure_plugin.cmxs
	coqc -Q . CertiCoq.Benchmarks.metacoq_erasure Loader.v

metacoq_erasure.vo ${GENCFILES} &: metacoq_erasure.v
	coqc ${COQOPTS} $<

%.o: %.c
	gcc -c -I . -I ../../_opam/lib/ocaml -Wno-everything -O2 -fomit-frame-pointer -o $@ $<

certicoq_erasure_plugin.cmxs: certicoq_erasure_plugin.cmxa ${CFILES:.c=.o}
	ocamlfind opt ${OCAMLOPTS} -shared -linkall -o $@ $+

certicoq_erasure_plugin.cmx: certiCoqErase.cmx g_safe_erasure.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certicoq_erasure_plugin.cmxa: certicoq_erasure_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_safe_erasure.ml: g_safe_erasure.mlg certiCoqErase.cmx
	coqpp $<

# g_safe_erasure.mli: g_safe_erasure.ml
# ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin -o $@ $<

.PHONY: plugin test