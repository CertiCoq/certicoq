#ifndef CERTICOQ_GC_STACK_H
#define CERTICOQ_GC_STACK_H

#include "values.h"

#define NULL 0

typedef const uintnat *fun_info;
/* fi[0]: How many words the function might allocate
   fi[1]: How many slots of the args array contain live roots
   fi[2..(fi[1]-2)]: Indices of the live roots in the args array
*/

/* ideally struct heap should be more abstract (opaque)
      struct heap;
  and ideally, the following definitions should live in gc_stack.c rather than gc_stack.h:
*/
#if  SIZEOF_PTR == 8
#define LOG_WORDSIZE 3
#endif
#if SIZEOF_PTR == 4
#define LOG_WORDSIZE 2
#endif
#define LOG_NURSERY_SIZE 16
#define NURSERY_SIZE (1<<LOG_NURSERY_SIZE)
#define MAX_SPACES 1 /* how many generations */
#define SPACE_SIZE 1000

/* END of the stuff that would ideally be more opaque */

#define MAX_ARGS 1024


/* A frame of the shadow stack used to keep track of the live roots */
struct stack_frame {
  value *next;
  value *root; /* the array of roots of the function. Allocated in the stack of the function */
  struct stack_frame *prev; /* pointer to the previous stack frame */
};

struct space { value *start, *next, *limit, *rem_limit; };
struct heap {  struct space spaces[MAX_SPACES]; };

struct thread_info {
  value *alloc; /* alloc pointer  */
  value *limit; /* limit pointer */
  struct heap *heap;  /* Description of the generations in the heap */
  value args[MAX_ARGS];   /* the args array */
  struct stack_frame *fp; /* stack pointer */
  uintnat nalloc; /* Remaining allocation until next GC call*/
  void *odata;
};

struct thread_info *make_tinfo(void);

void garbage_collect(struct thread_info *ti);

/* which slot of the args array has the answer of a certicoq program */
#define answer_index 1


#endif /* CERTICOQ_GC_STACK_H */
