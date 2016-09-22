#include "values.h"

struct fun_info {
  void (*fun)(void);
  uintnat num_allocs;
  uintnat num_args;
  uintnat *indices;
};

struct heap_info; /* abstract */

struct thread_info {
  value *args;
  int argc;
  value **alloc; /* pointer to the pointer to the beginning of alloc-space */
  value **limit; /* ... ditto ... just-past-end of alloc-space */
  struct heap *heap;
};

/* The client must create the thread_info and fill in all fields.
  In a newly created thread_info, it should be that (*start == *limit)
  and heap=NULL;
  Example:
value my_args[987];
value bogus[1];
value *my_start=bogus;
value *my_limit=bogus;
struct thread_info my_thread_info = {my_args, 987, &my_start, &my_limit, NULL};
*/

void garbage_collect(struct fun_info *fi, struct thread_info *ti);
/* Performs one garbage collection; or if (*start == *limit),
   initializes the heap. */


void destroy_thread(struct thread_info *ti);
/* Deallocates all heap data associated with ti, but does not free
   the struct thread_info itself. */

