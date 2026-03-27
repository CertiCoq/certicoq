#include "m.h"  /* use printm.c to create m.h */
#include "config.h"
#include "values.h"
#include "gc_stack.h"


/* The following 5 functions should (in practice) compile correctly in CompCert,
   but the CompCert correctness specification does not _require_ that
   they compile correctly:  their semantics is "undefined behavior" in
   CompCert C (and in C11), but in practice they will work in any compiler. */

int test_int_or_ptr (value x) /* returns 1 if int, 0 if aligned ptr */ {
    return (int)(((intnat)x)&1);
}

intnat int_or_ptr_to_int (value x) /* precondition: is int */ {
    return (intnat)x;
}

void * int_or_ptr_to_ptr (value x) /* precond: is aligned ptr */ {
    return (void *)x;
}

value int_to_int_or_ptr(intnat x) /* precondition: is odd */ {
    return (value)x;
}

value ptr_to_int_or_ptr(void *x) /* precondition: is aligned */ {
    return (value)x;
}

int is_ptr(value x) {
    return test_int_or_ptr(x) == 0;
}

/* A "space" describes one generation of the generational collector. 
struct space {
  value *start, *next, *limit, *rem_limit;
  };*/
/* Either start==NULL (meaning that this generation has not yet been created),
   or start <= next <= limit.  The words in start..next  are allocated
   and initialized, and the words from next..limit are available to allocate. */


// Global variable declarations
struct thread_info t_info;
struct heap h;
struct space spaces[MAX_SPACES];
struct space sp;
value values[SPACE_SIZE];

struct thread_info *make_tinfo(void) {
    // Initialize space
    sp.start = values;
    sp.next = values;
    sp.limit = values + SPACE_SIZE;
    sp.rem_limit = sp.limit;
    
    // Initialize spaces array
    h.spaces[0] = sp;  // Assign initialized space to first index

    // Initialize global thread_info struct
    t_info.heap = &h;
    t_info.alloc= h.spaces[0].start;
    t_info.limit = h.spaces[0].limit;
    t_info.fp= NULL;
    t_info.nalloc = 0;
    t_info.odata = NULL;

    return &t_info;  // Return a pointer to the global t_info
}

void abort_with(char *s) {
  /* fprintf(stderr, "%s", s); */
  /* exit(1); */
}

void garbage_collect(struct thread_info *ti)
/* See the header file for the interface-spec of this function. */
{
  abort_with("Ran out of space\n");
}
    
