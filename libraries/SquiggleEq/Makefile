all: Makefile.coq
	make -f Makefile.coq

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install :
	make -f Makefile.coq install

clean:
	make -f Makefile.coq clean
	rm Makefile.coq

_CoqProject:
	echo "-R . Libraries.SquiggleEq" > _CoqProject
	find . -name "*.v" >> _CoqProject
