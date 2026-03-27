SRC = gc_stack.c certicoq_run_main.c coq_c_ffi.c coq_ffi.c prim_int63.c prim_floats.c get_ordinal.c
HEADERS = m.h config.h values.h gc_stack.h certicoq_run_main.h coq_c_ffi.h coq_ffi.h prim_int63.h prim_floats.h get_ordinal.h
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith

TARGETS = ${SRC:.c=.o}
COQLIB = `coqc -where`
DST = ${COQLIB}/user-contrib/CertiCoq/Plugin/runtime

all: ${TARGETS}

%.o: %.c
	gcc -I . -I `ocamlc -where` -fPIC -O2 -g -fomit-frame-pointer -c -o $@ $+

install: all
	install -d ${DST}
	install -m 0644 ${HEADERS} ${DST}
	install -m 0644 ${SRC} ${DST}
	install -m 0644 ${TARGETS} ${DST}
	
clean:
	rm -f *.o
