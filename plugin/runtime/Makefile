SRC = gc_stack.c certicoq_run_main.c certicoq_run.c coq_c_ffi.c coq_ffi.c prim_int63.c prim_floats.c
HEADERS = m.h config.h values.h gc_stack.h certicoq_run_main.h certicoq_run.h coq_c_ffi.h coq_ffi.h prim_int63.h prim_floats.h
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith

MLIFILES = certicoq_run_wrapper.mli 
MLFILES = certicoq_run_wrapper.ml

TARGETS = ${SRC:.c=.o} ${MLFILES:.ml=.cmx}
COQLIB = `coqc -where`
DST = ${COQLIB}/user-contrib/CertiCoq/Plugin/runtime

all: ${TARGETS}

%.o: %.c
	gcc -I . -I `ocamlc -where` -O2 -g -fomit-frame-pointer -c -o $@ $+

%.cmx: %.ml %.mli
	ocamlfind ocamlopt -thread -rectypes -package coq-core,coq-core.plugins.ltac,coq-metacoq-template-ocaml,coq-certicoq.plugin -open Metacoq_template_plugin ${<:.ml=.mli}
	ocamlfind ocamlopt -thread -rectypes ${LINKOPTS} -package coq-core,coq-core.plugins.ltac,coq-metacoq-template-ocaml,coq-certicoq.plugin -open Metacoq_template_plugin -I .. -c $<

install: all
	install -d ${DST}
	install -m 0644 ${HEADERS} ${DST}
	install -m 0644 ${SRC} ${DST}
	install -m 0644 ${MLFILES} ${MLIFILES} ${MLFILES:.ml=.o} ${DST}
	install -m 0644 ${TARGETS} ${DST}
	
clean:
	rm -f *.o *.cmx *.cmi

.PHONY: certicoq_run_wrapper.cmi