#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include "gc.h"
#include <time.h>

/* TODO: This should be imported with include. */
extern value body(struct thread_info *);
extern value args[];

extern struct thread_info;
extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));
extern void print_Coq_Init_Datatypes_bool(unsigned long long);
extern value get_Coq_Init_Datatypes_pair_args (unsigned long long);
extern value make_Coq_Init_Datatypes_bool_true (void);
extern value make_Coq_Init_Datatypes_bool_false (void);
extern void* call(struct thread_info *tinfo, unsigned long long clos, unsigned long long arg0);

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

value calls(struct thread_info* tinfo, value clos, unsigned int n, ...)
{
  value v = clos;
  va_list args;
  va_start(args, n);

  for(; n != 0; n--) {
    v = va_arg(args, unsigned long long);
    clos = call(tinfo, clos, v);
  }
  va_end(args);
  return clos;
}


/* Main */
int main(int argc, char *argv[]) {
  value andb, clos;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  tinfo = make_tinfo();
  start = clock();

  // Run Coq program to get the andb function
  andb = body(tinfo);
  end = clock();

  /* Generate booleans*/
  value b = make_Coq_Init_Datatypes_bool_true ();
  value c = make_Coq_Init_Datatypes_bool_false ();


  printf("The original booleans.\n");
  print_Coq_Init_Datatypes_bool(b);
  printf(" and ");
  print_Coq_Init_Datatypes_bool(c);
  printf("\n");

  /* Call the variadic function val with two arguments, b and c */
  value v = calls(tinfo,andb,2,b,c);

  printf("The new boolean.\n");
  print_Coq_Init_Datatypes_bool(v);

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("\nTime taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
