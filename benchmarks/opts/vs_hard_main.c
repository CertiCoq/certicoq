#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>

extern value body(struct thread_info *);

extern void print_Coq_Init_Datatypes_bool(value);

extern void print_Coq_Init_Datatypes_list(value, void (*)(value));

void print_elem(value v) {
  printf(".");
}

void print_list(value l) {
  print_Coq_Init_Datatypes_list(l, print_elem);
  printf("\n");
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
    val = body(tinfo);
  }
  end = clock();

  // TODO : fold over nat to print the C int
  print_Coq_Init_Datatypes_bool(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
