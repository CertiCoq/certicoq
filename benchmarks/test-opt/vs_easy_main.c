#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>


extern void body(struct thread_info *);

extern void print_Coq_Init_Datatypes_bool(unsigned long long);

extern void print_CertiCoq_Benchmarks_lib_vs_space_atom(unsigned long long);

extern unsigned int get_Coq_Init_Datatypes_list_tag(unsigned long long);

extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));

extern void print_CertiCoq_Benchmarks_lib_vs_clause(unsigned long long);

void print_elem(unsigned long long v)
{
  printf(".");
}

void print_list(unsigned long long l)
{
  print_Coq_Init_Datatypes_list(l, print_elem);
  printf("\n");
}

void print_list_space_atom(unsigned long long l)
{
  print_Coq_Init_Datatypes_list(l, print_CertiCoq_Benchmarks_lib_vs_space_atom);
  printf("\n");
}

void print_list_clause(unsigned long long l)
{
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
    body(tinfo);
  }
  end = clock();

  val = tinfo -> args[1];
  // TODO : fold over nat to print the C int
  print_Coq_Init_Datatypes_bool(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
