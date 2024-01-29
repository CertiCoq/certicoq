#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include <time.h>
#include <coq_ffi.h>

extern value body(struct thread_info *);

extern value args[];

value certicoq_run() {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  start = clock();
  tinfo = make_tinfo();
  val = body(tinfo);
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return val;
}
