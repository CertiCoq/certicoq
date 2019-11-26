#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>
#include "demo.demo1.h"
#include "glue.demo.demo1.h"

extern void body(struct thread_info *);

extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;

  struct thread_info* tinfo;
  tinfo = make_tinfo();
  body(tinfo);

  val = tinfo -> args[1];
  print_list(val, print_bool);
  printf("\n");

  return 0;
}
