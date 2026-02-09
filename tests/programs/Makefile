COQOPTS = -R ../../plugin CertiCoq.Plugin -I ../../plugin -R ./ CertiCoq.Tests -R ../lib CertiCoq.Tests.lib
CCOMPILER=gcc
INCLUDE=../../runtime
WARN_OPTS=-Wno-format -Wno-format-security -Wno-int-conversion

# Names of the tests
TESTS=$(shell cat TESTS)
TEST_PREQS=%_main.c glue_%.c $(INCLUDE)/gc_stack.c
TEST_RECIPE=$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) $^

# Names of the generated glue code files
GLUE=$(TESTS:%=glue_%.c) $(TESTS:%=glue_%.h)

# Names of the generated C files
OPTS=opt opt1 opt2 opt3 opt4 opt5
TESTS_OPTS=$(foreach TEST,$(TESTS),$(OPTS:%=$(TEST)_%))
CFILES=$(TESTS_OPTS:%=CertiCoq.Tests.tests.%.c)

default: exec
all: lib exec run

.PHONY: all default clean cleanexec lib cleanlib run $(TESTS)

exec: $(TESTS)

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.vo
	rm -f ./*.glob
	rm -f ./glue_*.*
	rm -f ./CertiCoq.Tests.tests.*.c

cleanexec:
	rm -f ./*_opt
	rm -f ./*_opt[1-5]

lib/Makefile:
	cd ../lib; coq_makefile -f _CoqProject -o Makefile

lib: ../lib/Makefile
	$(MAKE) -C ../lib

cleanlib:
	$(MAKE) clean -C ../lib

$(GLUE) $(CFILES): tests.v
	coqc $(COQOPTS) $<

%_opt:  $(TEST_PREQS) CertiCoq.Tests.tests.%_opt.c  ; $(TEST_RECIPE)
%_opt1: $(TEST_PREQS) CertiCoq.Tests.tests.%_opt1.c ; $(TEST_RECIPE)
%_opt2: $(TEST_PREQS) CertiCoq.Tests.tests.%_opt2.c ; $(TEST_RECIPE)
%_opt3: $(TEST_PREQS) CertiCoq.Tests.tests.%_opt3.c ; $(TEST_RECIPE)
%_opt4: $(TEST_PREQS) CertiCoq.Tests.tests.%_opt4.c ; $(TEST_RECIPE)
%_opt5: $(TEST_PREQS) CertiCoq.Tests.tests.%_opt5.c ; $(TEST_RECIPE)

$(TESTS):%: %_opt %_opt1 %_opt2 %_opt3 %_opt4 %_opt5

run: run.sh exec
	sh $<
