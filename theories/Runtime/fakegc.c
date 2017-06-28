#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc.h"

int GC = 0;
/* This is an alternate implementation of the gc.h interface,
   that does no garbage collection.  Useful for debugging 
   both programs and proofs. */

#define SIZE (1<<8)  /* 16 million words */




struct heap {
  value *start, *limit;
  value *space;
};

struct heap *create_heap()
{
  struct heap *h = (struct heap *) malloc (sizeof *h);
  h->space =  (value *)malloc(sizeof (value)*64);
  h->start = h->space;
  h->limit = h->space;
  return h;
}

struct thread_info *make_tinfo(void) {
  struct thread_info *tinfo;
  struct heap *h = create_heap();
  
  tinfo = (struct thread_info *)malloc(sizeof(struct thread_info));
  if (!tinfo) {
    fprintf(stderr, "Could not allocate thread_info struct\n");
    exit(1);
  }
  
  tinfo->heap=h;
  tinfo->alloc=h->start;
  tinfo->limit=h->limit;
  return tinfo;
}


void resume(fun_info fi, struct thread_info *ti)
/* When the garbage collector is all done, it does not "return"
   to the mutator; instead, it uses this function (which does not return)
   to resume the mutator by invoking the continuation, fi->fun.  
   But first, "resume" informs the mutator
   of the new values for the alloc and limit pointers.
*/
 {
   fprintf(stderr, "In resume");
   struct heap *h = ti->heap;
  value *lo, *hi;
  assert (h);
  fprintf(stderr, " h ok \n");
  
  uintnat num_allocs = fi[0];
  lo = h->start;
  hi = h->start+num_allocs;
  fprintf(stderr, "Space in heap = %d, num allocs = %d \n", (hi-lo), num_allocs);

  if (hi-lo < num_allocs) {
    fprintf(stderr, "Heap is too small for function's num_allocs\n");
    exit(1);
  }
  ti->alloc = lo;
  ti->limit = lo;
}  

void garbage_collect(fun_info fi, struct thread_info *ti) {
  GC = GC+ 1;
  uintnat num_allocs = fi[0];
  fprintf(stderr, "GC = %d for %d values \n", GC, num_allocs);
  struct heap *h = (struct heap *) malloc (sizeof (struct heap));
  fprintf(stderr, "gc1\n ");
  h->space =  (value *)malloc(sizeof (value)*num_allocs);
  fprintf(stderr, "gc2\n ");
  h->start = h->space;
  h->limit = h->space + num_allocs;
  ti->heap = h;
  resume(fi,ti);
  return;
}
  

void free_heap(struct heap *h) {
  free(h);
}

void reset_heap(struct heap *h) {
}
