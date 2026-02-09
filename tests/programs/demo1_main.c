#include <stdio.h>
#include "gc_stack.h"
#include "glue_demo1.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);

  print_Coq_Init_Datatypes_list(val, print_Coq_Init_Datatypes_bool);
  printf("\n");

  return 0;
}
