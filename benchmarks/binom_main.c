#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>


extern void body(struct thread_info *);

extern void print_Coq_Init_Datatypes_nat(unsigned long long);

extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  tinfo = make_tinfo();
  start = clock();
  // Run Coq program
  body(tinfo);
  end = clock();

  val = tinfo -> args[1];
  // TODO : fold over nat to print the C int
  print_Coq_Init_Datatypes_nat(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
