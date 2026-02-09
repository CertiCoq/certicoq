#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <caml/memory.h>
#include <time.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>

extern value body(struct thread_info *);

extern value args[];

extern value *call(struct thread_info *, value, value);

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

CAMLprim value certicoq_erase(value prog) {
  CAMLparam1 (prog);
  CAMLlocal1 (v);
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  struct Coq_Init_Datatypes_pair_args*  progargs;
  start = clock();
  // Run Coq program
  tinfo = make_tinfo();
  
  v = call(tinfo, body(tinfo), prog);
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  CAMLreturn(Val_unit);
}
