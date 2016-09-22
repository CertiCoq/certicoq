#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc.h"

struct space {
  value *start, *next, *limit;
};

#define MAX_SPACES 10  /* how many generations */
#define RATIO 8   /* size of generation i+1 / size of generation i */
#define NURSERY_SIZE ((1<<19)/sizeof(value))  /* half a megabyte */

struct heap {
  struct space spaces[MAX_SPACES];
};


#define Is_from(from_start, from_limit, v)			\
   (from_start <= (value*)(v) && (value*)(v) < from_limit)

void forward (value *from_start, value *from_limit, value **next,
	       value *p) {
  mlsize_t sz;
  value new;
  value v = *p;
  if(Is_block(v)) {
    if(Is_from(from_start, from_limit, v)) {
      header_t hd = Hd_val(v); 
      if(hd == 0) { /* already forwarded */
	new = Field(v,0);
	*p = new;
      } else {
        sz = Wosize_hd(hd);
	new = (value)(*next+1);
	*next += new+sz; 
	for(int i = -1; i < sz; i++) {
	  Field(new, i + 1) = Field(v, i);
	}
	Hd_val(v) = 0;
	Field(v, 0) = new;
	*p = new;
      }
    }
  }
}

void forward_roots (value *from_start, value *from_limit,
		    value **next,
		    struct fun_info *fi, struct thread_info *ti) {
  value *args; int n; uintnat *roots;
  roots = fi -> indices;
  n = fi -> num_args;
  args = ti->args;
  
  for(uintnat i = 0; i < n; i++)
    forward(from_start, from_limit, next, args+roots[i]);
}  

#define No_scan_tag 251
#define No_scan(t) ((t) >= No_scan_tag)

void do_scan(value *from_start, value *from_limit,
	     value *scan,
 	     value **next) {
  value *s;
  s = scan;
  while(s < *next) {
    header_t hd = *s;
    mlsize_t sz = Wosize_hd(hd);
    int tag = Tag_hd(hd);
    if (!No_scan(tag)) {
      intnat j;
      for(j = 1; j <= sz; j++) {
	forward (from_start, from_limit, next, &Field(s, j));
      }
    }
    s += 1+sz;
  }
}
	     
void do_generation (struct space *from,
		    struct space *to, 
		    struct fun_info *fi,
		    struct thread_info *ti) {
  assert(from->next-from->start <= to->limit-to->next);
  forward_roots(from->start, from->limit, &to->next, fi, ti);
  do_scan(from->start, from->limit, to->start, &to->next);
  from->next=from->start;
}  

void resume(struct fun_info *fi, struct thread_info *ti) {
  void (*f)(void);
  struct heap *h = ti->heap;
  assert (h);
  f = fi->fun;
  *ti->alloc = h->spaces[0].start;
  *ti->limit = h->spaces[0].limit;
  (*f)();
}  

void create_space(struct space *s, uintnat words) {
  value *p; uintnat n;
  unintnat maxint = 0u-1u;
  if (words > maxint/(2*sizeof(value))) {
    fprintf(stderr,"Next generation would be too big for address space\n");
    exit(1);
  }
  d = maxint/RATIO;
  if (words<d) d=words;
  n = d*RATIO;
  p = (value *)malloc(n * sizeof(value););
  if (p==NULL) {
    fprintf(stderr,"Could not create the next generation\n");
    exit(1);
  }
  s->start=p;
  s->next=p;
  s->limit = p+n;
}

struct heap *create_heap() {
  int i;
  struct heap *h = (struct heap *)malloc(sizeof (struct heap));
  if (h==NULL) {
    fprintf(stderr,"Could not create the heap\n");
    exit(1);
  }
  create_space(h->spaces+0, NURSERY_SIZE);
  for(i=1; i<MAX_SPACES; i++) {
    h->spaces[i].start = NULL;
    h->spaces[i].next = NULL;
    h->spaces[i].limit = NULL;
  }
  return h;
}

void garbage_collect(struct fun_info *fi, struct thread_info *ti) {
  struct heap *h = ti->heap;
  if (h==NULL) {
    h = create_heap();
    ti->heap = h;
    resume(fi,ti);
  } else {
    assert (h->spaces[0].limit == *ti->limit);
    h->spaces[0].next = *ti->alloc;
    int i;
    for (i=0; i<MAX_SPACES-1; i++) {
      if (h->spaces[i+1].start==NULL)
	create_space(h->spaces+(i+1), h->spaces[i].limit-h->spaces[i].start);
      do_generation(h->spaces+i, h->spaces+(i+1), fi, ti);
      if (h->spaces[i].limit - h->spaces[i].start
	  <= h->spaces[i+1].limit - h->spaces[i].next)
	resume(fi,ti);
    }
    fprintf(stderr, "Ran out of generations\n");
    exit(1);
  }
  assert(0);
} 
