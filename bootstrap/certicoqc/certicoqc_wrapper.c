#include <stdio.h>
#include <stdlib.h>
#include "values.h"
#include "gc.h"
#include <caml/memory.h>
#include <time.h>
#include <caml/callback.h>

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

// external certicoq_pipeline : (coq_Options × ExtractedASTBaseQuoter.quoted_program) -> coq_Cprogram error * Bytestring.String.t = "certicoq_pipeline"
CAMLprim value certicoq_pipeline_wrapper(value opts, value prog) {
  CAMLparam2 (opts, prog);
  CAMLlocal1 (res);
  value closure;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  start = clock();
  
  // Run Coq program
  tinfo = make_tinfo();
  printf("about to call compiler\n");
  closure = body(tinfo);
  closure = call(tinfo, closure, opts);
  res = call(tinfo, closure, prog);
  printf("compiler returned a value\n");
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  CAMLreturn(res);
}
