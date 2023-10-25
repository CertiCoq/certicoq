#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include <time.h>

extern value body(struct thread_info *);

extern void print_Coq_Init_Datatypes_bool(value);

extern void print_CertiCoq_Benchmarks_lib_vs_space_atom(value);

extern unsigned int get_Coq_Init_Datatypes_list_tag(value);

extern void print_Coq_Init_Datatypes_list(value, void (*)(value));

extern void print_CertiCoq_Benchmarks_lib_vs_clause(value);

void print_elem(value v) {
  printf(".");
}

void print_list(value l) {
  print_Coq_Init_Datatypes_list(l, print_elem);
  printf("\n");
}

void print_list_space_atom(value l) {
  print_Coq_Init_Datatypes_list(l, print_CertiCoq_Benchmarks_lib_vs_space_atom);
  printf("\n");
}

void print_list_clause(value l) {
  print_Coq_Init_Datatypes_list(l, print_CertiCoq_Benchmarks_lib_vs_clause);
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
