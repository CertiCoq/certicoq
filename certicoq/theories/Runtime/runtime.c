#include "nogc.c"

extern value *alloc;
extern value *limit;
extern value args [];

extern struct heap;
extern struct thread_info;

extern void garbage_college (fun_info fi, struct thread_info *ti);

void gc(fun_info fi, struct thread_info *ti) {
  garbage_collect(fi, ti);
}
