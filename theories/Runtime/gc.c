#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc.h"

/* A "space" describes one generation of the generational collector. */
struct space {
  value *start, *next, *limit;
};
/* Either start==NULL (meaning that this generation has not yet been created),
   or start <= next <= limit.  The words in start..next  are allocated
   and initialized, and the words from next..limit are available to allocate. */

#define MAX_SPACES 10  /* how many generations */
#define RATIO 4   /* size of generation i+1 / size of generation i */

#ifdef TINY_NURSERY
#define NURSERY_SIZE (12)
#else
#define NURSERY_SIZE ((1<<18)/sizeof(value))  /* 256 kilobytes */
#endif
/* The size of generation 0 (the "nursery") should approximately match the 
   size of the level-2 cache of the machine, according to:
      Cache Performance of Fast-Allocating Programs, 
      by Marcelo J. R. Goncalves and Andrew W. Appel. 
      7th Int'l Conf. on Functional Programming and Computer Architecture,
      pp. 293-305, ACM Press, June 1995.
   We estimate this as 256 kilobytes 
     (which is the size of the Intel Core i7 per-core L2 cache).
    http://www.tomshardware.com/reviews/Intel-i7-nehalem-cpu,2041-10.html
    https://en.wikipedia.org/wiki/Nehalem_(microarchitecture)
*/

#define DEPTH 0  /* how much depth-first search to do */

struct heap {
  /* A heap is an array of generations; generation 0 must be already-created */
  struct space spaces[MAX_SPACES];
};

#ifdef DEBUG

int in_heap(struct heap *h, value v) {
  int i;
  for (i=0; i<MAX_SPACES; i++)
    if (h->spaces[i].start != NULL)
      if (h->spaces[i].start <= (value*)v &&
	  (value *)v <= h->spaces[i].limit)
	return 1;
  return 0;
}

void printtree(FILE *f, struct heap *h, value v) {
  if(Is_block(v))
    if (in_heap(h,v)) {
      header_t hd = Field(v,-1);
      int sz = Wosize_hd(hd);
      int i;
      fprintf(f,"%d(", Tag_hd(hd));
      for(i=0; i<sz-1; i++) {
	printtree(f,h,Field(v,i));
	fprintf(f,",");
      }
      if (i<sz)
	printtree(f,h,Field(v,i));
      fprintf(f,")");
    }
    else {
      fprintf(f,"%8x",v);
    }
  else fprintf(f,"%d",v>>1);
}

void printroots (FILE *f, struct heap *h,
		  const struct fun_info *fi,/* which args contain live roots? */
		  struct thread_info *ti) /* where's the args array? */
 {
   value *args; int n; uintnat i, *roots;
  roots = fi -> indices;
  n = fi -> num_args;
  args = ti->args;
  
  for(i = 0; i < n; i++) {
    fprintf(f,"%d[%8x]:",roots[i],args[roots[i]]);
    printtree(f, h, args[roots[i]]);
    fprintf(f,"\n");
  }
  fprintf(f,"\n");
}  

#endif

#define Is_from(from_start, from_limit, v)			\
   (from_start <= (value*)(v) && (value*)(v) < from_limit)
/* Assuming v is a pointer (Is_block(v)), tests whether v points
   somewhere into the "from-space" defined by from_start and from_limit */

void forward (value *from_start,  /* beginning of from-space */
	      value *from_limit,  /* end of from-space */
	      value **next,       /* next available spot in to-space */
	      value *p,           /* location of word to forward */
	      int depth)          /* how much depth-first search to do */
/* What it does:  If *p is a pointer, AND it points into from-space,
   then make *p point at the corresponding object in to-space.
   If such an object did not already exist, create it at address *next
    (and increment *next by the size of the object).
   If *p is not a pointer into from-space, then leave it alone. 

   The depth parameter may be set to 0 for ordinary breadth-first
   collection.  Setting depth to a small integer (perhaps 10)
   may improve the cache locality of the copied graph.
*/
 {
  value v = *p;
  if(Is_block(v)) {
    if(Is_from(from_start, from_limit, v)) {
      header_t hd = Hd_val(v); 
      if(hd == 0) { /* already forwarded */
	*p = Field(v,0);
      } else {
	int i;
	int sz;
	value *new;
        sz = Wosize_hd(hd);
	new = *next+1;
	*next = new+sz; 
	for(i = -1; i < sz; i++) {
	  Field(new, i) = Field(v, i);
	}
	Hd_val(v) = 0;
	Field(v, 0) = (value)new;
	*p = (value)new;
	if (depth>0)
	  for (i=0; i<sz; i++)
	    forward(from_start, from_limit, next, &Field(new,i), depth-1);
      }
    }
  }
}

void forward_roots (value *from_start,  /* beginning of from-space */
		    value *from_limit,  /* end of from-space */
		    value **next,       /* next available spot in to-space */
		    const struct fun_info *fi,/* which args contain live roots? */
		    struct thread_info *ti) /* where's the args array? */
/* Forward each live root in the args array */
 {
   value *args; int n; uintnat i, *roots;
  roots = fi -> indices;
  n = fi -> num_args;
  args = ti->args;
  
  for(i = 0; i < n; i++)
    forward(from_start, from_limit, next, args+roots[i], DEPTH);
}  

#define No_scan_tag 251
#define No_scan(t) ((t) >= No_scan_tag)

void do_scan(value *from_start,  /* beginning of from-space */
	     value *from_limit,  /* end of from-space */
	     value *scan,        /* start of unforwarded part of to-space */
 	     value **next)       /* next available spot in to-space */
/* Forward each word in the to-space between scan and *next.
  In the process, next may increase, so keep doing it until scan catches up.
  Leave alone:  header words, and "no_scan" (nonpointer) data. 
*/
{
  value *s;
  s = scan;
  while(s < *next) {
    header_t hd = *s;
    mlsize_t sz = Wosize_hd(hd);
    int tag = Tag_hd(hd);
    if (!No_scan(tag)) {
      intnat j;
      for(j = 1; j <= sz; j++) {
	forward (from_start, from_limit, next, &Field(s, j), DEPTH);
      }
    }
    s += 1+sz;
  }
}
	     
void do_generation (struct space *from,  /* descriptor of from-space */
		    struct space *to,    /* descriptor of to-space */
		    const struct fun_info *fi, /* which args contain live roots? */
		    struct thread_info *ti)  /* where's the args array? */
/* Copy the live objects out of the "from" space, into the "to" space,
   using fi and ti to determine the roots of liveness. */
{
  assert(from->next-from->start <= to->limit-to->next);
  forward_roots(from->start, from->limit, &to->next, fi, ti);
  do_scan(from->start, from->limit, to->start, &to->next);
  from->next=from->start;
}  

uintnat gensize(uintnat words)
/* words is size of one generation; calculate size of the next generation */
{
  uintnat maxint = 0u-1u;
  uintnat n,d;
  /* The next few lines calculate a value "n" that's at least words*2,
     preferably words*RATIO, and without overflowing the size of an
     unsigned integer. */
  /* minor bug:  this assumes sizeof(uintnat)==sizeof(void*)==sizeof(value) */
  if (words > maxint/(2*sizeof(value))) {
    fprintf(stderr,"Next generation would be too big for address space\n");
    exit(1);
  }
  d = maxint/RATIO;
  if (words<d) d=words;
  n = d*RATIO;
  assert (n >= 2*words);
  return n;
}  

void create_space(struct space *s,  /* which generation to create */
		  uintnat n,  /* desired size of the generation */
		  uintnat min_n) /* min size of the generation */
  /* malloc an array of words for generation "s", and
     set s->start and s->next to the beginning, and s->limit to the end.
  */

 {
  value *p;

  /* Now, try to malloc an array of n values.  If that's not possible,
   * then set n=2*words, and try again. */
  p = (value *)malloc(n * sizeof(value));
  if (p==NULL) {
    n=min_n;
    p = (value *)malloc(min_n * sizeof(value));
  }
  if (p==NULL) {
    fprintf(stderr,"Could not create the next generation\n");
    exit(1);
  }
  fprintf(stderr, "Created a generation of %d words\n", n);
  s->start=p;
  s->next=p;
  s->limit = p+n;
}

struct heap *create_heap()
/* To create a heap, first malloc the array of space-descriptors,
   then create only generation 0.  */
{
  int i;
  struct heap *h = (struct heap *)malloc(sizeof (struct heap));
  if (h==NULL) {
    fprintf(stderr,"Could not create the heap\n");
    exit(1);
  }
  create_space(h->spaces+0, NURSERY_SIZE, NURSERY_SIZE);
  for(i=1; i<MAX_SPACES; i++) {
    h->spaces[i].start = NULL;
    h->spaces[i].next = NULL;
    h->spaces[i].limit = NULL;
  }
  return h;
}

void resume(const struct fun_info *fi, struct thread_info *ti)
/* When the garbage collector is all done, it does not "return"
   to the mutator; instead, it uses this function (which does not return)
   to resume the mutator by invoking the continuation, fi->fun.  
   But first, "resume" informs the mutator
   of the new values for the alloc and limit pointers.
*/
 {
  void (*f)(void);
  struct heap *h = ti->heap;
  value *lo, *hi;
  assert (h);
  lo = h->spaces[0].start;
  hi = h->spaces[0].limit;
  if (hi-lo < fi->num_allocs) {
    fprintf(stderr, "Nursery is too small for function's num_allocs\n");
    exit(1);
  }
  f = fi->fun;
  *ti->alloc = lo;
  *ti->limit = hi;
  /*  (*f)(); */
}  

void garbage_collect(const struct fun_info *fi, struct thread_info *ti)
/* See the header file for the interface-spec of this function. */
{
  struct heap *h = ti->heap;
  if (h==NULL) {
    /* If the heap has not yet been initialized, create it and resume */
    h = create_heap();
    ti->heap = h;
    resume(fi,ti);
    return;
  } else {
    int i;
    assert (h->spaces[0].limit == *ti->limit);
    h->spaces[0].next = *ti->alloc; /* this line is probably unnecessary */
    for (i=0; i<MAX_SPACES-1; i++) {
      /* Starting with the youngest generation, collect each generation
         into the next-older generation.  Usually, when doing that,
         there will be enough space left in the next-older generation
         so that we can break the loop by resuming the mutator. */

      /* If the next generation does not yet exist, create it */
      if (h->spaces[i+1].start==NULL) {
	int w = h->spaces[i].limit-h->spaces[i].start;
	create_space(h->spaces+(i+1), gensize(w), 2*w);
      }
      /*      fprintf(stderr, "At %8x collecting gen. %d; %8x\n", fi->fun, i,h->spaces[i+1].next); */
      /*      fprintf(stderr,"BEFORE\n"); printroots(stderr,h,fi,ti); */
      /* Copy all the objects in generation i, into generation i+1 */
      do_generation(h->spaces+i, h->spaces+(i+1), fi, ti);
      /*      printroots(stderr,h,fi,ti); */
      /*      fprintf(stderr, " %8x %8x %8x %8x %8x\n",
	      h->spaces[i].start,
	      h->spaces[i].limit,
	      h->spaces[i+1].start,
	      h->spaces[i+1].next,
	      h->spaces[i+1].limit);
      */
      /* If there's enough space in gen i+1 to guarantee that the
         NEXT collection into i+1 will succeed, we can stop here */
      if (h->spaces[i].limit - h->spaces[i].start
	  <= h->spaces[i+1].limit - h->spaces[i+1].next) {
	 resume(fi,ti);
	 return;
      }
    }
    /* If we get to i==MAX_SPACES, that's bad news */
    fprintf(stderr, "Ran out of generations\n");
    exit(1);
  }
  /* Can't reach this point */
  assert(0);
} 

/* REMARK.  The generation-management policy in the garbage_collect function
   has a potential flaw.  Whenever a record is copied, it is promoted to
   a higher generation.  This is generally a good idea.  But there is
   a bounded number of generations.  A useful improvement would be:
   when it's time to collect the oldest generation (and we can tell
   it's the oldest, at least because create_space() fails), do some
   reorganization instead of failing.
 */

void reset_heap (struct heap *h) {
  int i;
  for (i=0; i<MAX_SPACES; i++)
    h->spaces[i].next = h->spaces[i].start;
}
  

void free_heap (struct heap *h) {
  int i;
  for (i=0; i<MAX_SPACES; i++) {
    value *p = h->spaces[i].start;
    if (p!=NULL)
      free(p);
  }
  free (h);
}
