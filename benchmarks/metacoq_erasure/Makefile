PKGS = -package coq-core,coq-core.plugins.ltac,coq-metacoq-template-ocaml,coq-certicoqc
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith
OCAMLOPTS = -open Metacoq_template_plugin -I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.metacoq_erasure.c \
		CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.metacoq_erasure.c
CFILES = certicoq_erasure.c ${GENCFILES} gc_stack.c print.c
COPTS = -g -I ../../_opam/lib/ocaml -I . -I ../../theories/Runtime
# ffi.CertiCoq.Benchmarks.metacoq_erasure.metacoq_erasure.QuoteFFI.c
COQOPTS = -Q ../../theories/Codegen CertiCoq.Codegen -Q ../../libraries CertiCoq.Libraries \
	-Q ../../theories/LambdaANF CertiCoq.LambdaANF -Q ../../theories/LambdaBoxLocal CertiCoq.LambdaBoxLocal \
	-Q ../../theories/Compiler CertiCoq.Compiler -Q ../../theories/common CertiCoq.Common \
	-Q ../../theories/LambdaBoxMut CertiCoq.LambdaBoxMut -Q .. CertiCoq.Benchmarks

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = ${RUNTIME_DIR}/prim_floats.o ${RUNTIME_DIR}/prim_int63.o

plugin: metacoq_erasure.vo Loader.vo

test: test.vo

test.vo: plugin test.v
	coqc -I . -Q . CertiCoq.Benchmarks.metacoq_erasure test.v

clean: 
	rm *.cm*

Loader.vo: Loader.v install
	coqc -I . -Q . CertiCoq.Benchmarks.metacoq_erasure Loader.v

metacoq_erasure.vo: metacoq_erasure.v
	coqc ${COQOPTS} $<

%.o: %.c
	gcc ${COPTS} -c -Wno-everything -O2 -fomit-frame-pointer -o $@ $<

certicoq_erasure_plugin.cmxs: certicoq_erasure_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} ${LINKOPTS} -shared -linkall -o $@ $+

certicoq_erasure_plugin.cmx: certiCoqErase.cmx g_safe_erasure.cmx
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -pack -o $@ $+

certicoq_erasure_plugin.cmxa: certicoq_erasure_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_safe_erasure.ml: g_safe_erasure.mlg certiCoqErase.cmx
	coqpp $<

# g_safe_erasure.mli: g_safe_erasure.ml
# ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin $<

%.cmx: %.ml %.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certicoq_erasure_plugin $<

install: certicoq_erasure_plugin.cmxa certicoq_erasure_plugin.cmxs certicoq_erasure_plugin.cmx
	ocamlfind remove coq-certicoq-bootstrapped-erasure
	ocamlfind install coq-certicoq-bootstrapped-erasure META $+

.PHONY: plugin test
