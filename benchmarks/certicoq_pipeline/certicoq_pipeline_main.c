#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>

extern void body(struct thread_info *);

extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  
  // Specify number of runs
  int n = 1;
  if (argc > 1) n = atoi(argv[1]);

  start = clock();
  // Run Coq program
  for (int i = 0; i < n; i ++) {
    tinfo = make_tinfo();
    body(tinfo);
  }
  end = clock();

  val = tinfo -> args[1];
  // TODO : fold over nat to print the C string
  // print_string(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
