#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>


extern void body(struct thread_info *);

extern void print_Coq_Init_Datatypes_nat(unsigned long long);

extern unsigned int get_Coq_Init_Datatypes_nat_tag(unsigned long long);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(unsigned long long);
extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));

void print_Coq_nat_as_int(unsigned long long v)
{
  unsigned int tag;
  void *args;
  int cnt = 0;
  unsigned long long val = v;

  tag = (get_Coq_Init_Datatypes_nat_tag)(val);

  while (tag != 0) {
    cnt ++ ;
    val = *((unsigned long long *)((get_Coq_Init_Datatypes_S_args)(val)) + 0);
    tag = (get_Coq_Init_Datatypes_nat_tag)(val);
  }
  printf("%d\n", cnt);
}

void print_list_nat(unsigned long long l)
{
  print_Coq_Init_Datatypes_list(l, print_Coq_nat_as_int);
  printf("\n");
}

extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  // Specify number of runs to be executed
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
  print_Coq_Init_Datatypes_nat(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
