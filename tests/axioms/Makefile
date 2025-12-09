COQOPTS = -R ./ CertiCoq.Tests -R ../lib CertiCoq.Tests.lib
CCOMPILER=gcc
INCLUDE=../../runtime
WARN_OPTS=-Wno-format -Wno-format-security -Wno-int-conversion

# Names of the tests
TESTS=print_lst fibn list_sum_int63 list_sum_int63_tinfo
# Names of the generated C files
CFILES=$(patsubst %, CertiCoq.Tests.tests.%.c, $(TESTS)) glue.c

default: exec

.PHONY: compile exec clean

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob
	rm -f $(TESTS)
	rm -f glue.*

compile: tests.v
	coqc $(COQOPTS) tests.v

$(CFILES): compile

fibn: CertiCoq.Tests.tests.fibn.c glue.c int63.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

print_lst: CertiCoq.Tests.tests.print_lst.c glue.c print.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

list_sum_int63: CertiCoq.Tests.tests.list_sum_int63.c glue.c int63.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

list_sum_int63_tinfo: CertiCoq.Tests.tests.list_sum_int63_tinfo.c glue.c int63_tinfo.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

exec: $(TESTS)
