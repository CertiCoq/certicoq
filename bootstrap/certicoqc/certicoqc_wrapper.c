#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <time.h>
#include <caml/callback.h>

extern value body(struct thread_info *);

extern value *call(struct thread_info *, value, value);

// Follow gc_stack.c/forward function to preserve sharing.
static value copy_value(value v) {
  CAMLparam0();
  CAMLlocal1 (newv);

  if (Is_long(v)) {
    //printf ("Copying immediate int of value %i\n", Long_val(v));
    newv = v;
  } else {
    mlsize_t size = Wosize_val(v);
    header_t hd = Hd_val(v);
    tag_t tag = Tag_hd(hd);

    if (hd == 0) { /* already copied */
      //printf ("Value is already copied\n", Long_val(v));
      newv = Field(v,0);
    } else { 
      //printf ("Copying object of tag %i and size %i \n", tag, size);
      
      newv = caml_alloc(size, tag);
      int i;
      for (i = 0; i < size; i++) {
        // printf ("Copying field %i of block of tag %i\n", i, tag);
        Field (newv, i) = Field(v, i);
      }
      Hd_val(v) = 0;
	    Field(v, 0) = newv;
      if (!No_scan(tag)) {
        for (i = 0; i < size; i++) {
          // printf ("Copying field %i of block of tag %i\n", i, tag);
          Store_field(newv, i, copy_value (Field(newv, i)));
        }
      }
    }
  }
  CAMLreturn (newv);
}

// external certicoq_pipeline : (coq_Options × ExtractedASTBaseQuoter.quoted_program) -> coq_Cprogram error * Bytestring.String.t = "certicoq_pipeline"
CAMLprim value certicoq_pipeline_wrapper(value opts, value prog) {
  CAMLparam2 (opts, prog);
  CAMLlocal1 (res);
  value closure;
  value restemp;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  start = clock();
  
  // Run Coq program
  tinfo = make_tinfo();
  printf("about to call compiler\n");
  closure = body(tinfo);
  closure = call(tinfo, closure, opts);
  restemp = call(tinfo, closure, prog);
  printf("compiler returned a value\n");
  end = clock();

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  printf("Copying value to OCaml heap\n");
  res = copy_value(restemp);
  free_heap(tinfo->heap);
  printf("Value copied to OCaml heap\n");
  
  CAMLreturn(res);
}
