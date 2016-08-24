#include <string.h>
#include <stdlib.h>
#include "config.h"
#include "values.h"

/* things I need to know */
value *alloc = NULL;
value *limit = NULL;
value *args = NULL;

value *from_start = NULL;
value *from_limit = NULL;
value *to_start = NULL;
value *to_limit = NULL;
value *next = NULL;
uintnat heap_size = 0;

#define Is_from(v) (from_start <= v && v <= from_limit)
#define Is_to(v) (to_start <= v && v <= to_limit)

struct fun_info {
  void (*fun)(void);
  uintnat num_allocs;
  uintnat num_args;
  uintnat *indices;
};

void incr_heap (void) { /* use malloc, copy over, free up old space, maybe smart with gc */
  heap_size = heap_size + Heap_chunk_def;
  
  from_start = realloc(from_start, heap_size * sizeof(value));
  from_limit = from_start + heap_size;
  to_start = realloc(to_start, heap_size * sizeof(value)); /* will the init malloc make contiguous, so this will fail? */
  to_limit = to_limit + heap_size;
  
  limit = from_limit;
  return;
}

value forward (value v)
{
  if(Is_block(v)) {
    if(Is_from((value *) v)) {
      header_t hd = Hd_val(v); 
      if(hd == 0) {
	return Field(v,0);
      } else {
	for(int i = -1; i < Wosize_val(v); i++) {
	  Field(next, i + 1) = Field(v, i);
	}
	Hd_val(v) = 0;
	Field(v, 0) = (value) (next + 1);
	next = next + Whsize_val(v); 
	return Field(v, 0);
      }
    } else {
      return v;
    }
  } else {
    return v;
  }
}

void gc_control (struct fun_info *info)
{
  uintnat num_args, num_allocs, *roots;
  value *scan;

  roots = info -> indices;
  num_args = info -> num_args;
  num_allocs = info -> num_allocs;
  
  next = to_start;
  scan = next;
  for(uintnat i = 0; i < num_args; i++) {
    Field(args, Field(roots, i)) = forward(Field(args, Field(roots, i)));
  }
  while(scan < next) {
    if(Is_block(*scan)){
      mlsize_t sz = Wosize_hd(Hd_val(scan));
      for(intnat j = 1; j <= sz; j++) { /* here first field is 1 because hd is at scan + 0 */
	Field(scan, j) = forward (Field(scan, j));
      }
      scan = scan + Whsize_hd(Hd_val(scan));
    } else {
      scan = scan + 1;
    }
  }
  /* swap gc start pointers */
  value *t = to_start;
  to_start = from_start;
  from_start = t;
  /* swap gc limit pointers */
  t = to_limit;
  to_limit = from_limit;
  from_limit = t;
  /* update heap alloc pointers */
  alloc = next;
  limit = from_limit;

  while(alloc + num_allocs > limit){
    incr_heap();
  }

  /* tail call function after gc */
  (*(*info).fun)();
  
  return; 
}

void init (void) {
  heap_size = Heap_def;
  
  from_start = malloc(heap_size * sizeof(value));
  from_limit = from_start + heap_size;
  to_start = malloc(heap_size * sizeof(value));
  to_limit = to_start + heap_size;
  
  alloc = from_start;
  limit = from_limit;
}
