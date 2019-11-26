#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>
#include "demo.demo2.h"
#include "glue.demo.demo2.h"

extern void body(struct thread_info *);

extern value args[];

/*
OS: Checks if an long long represents a pointer, implemented as an extern in Clight
 */
_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;

  struct thread_info* tinfo;
  tinfo = make_tinfo();
  body(tinfo);
  val = tinfo -> args[1];


  struct pair_args *p = get_pair_args(val);

  value ret;
  void *v_clo;

  printf(">>>>> Call to negb\n");
  value v_fal = make_bool_false();
  printf("Input: \n" );
  print_bool(v_fal);

  v_clo = p->pair_args_0;

  ret = call_1(v_clo, v_fal);
  printf("Return: %s\n");
  print_bool(ret);


  printf(">>>>> Call to List.hd_error\n");
  v_clo = p->pair_args_1;

  value v_l = make_list_nil();
  value v_next[3];
  value v_cons = make_list_cons(v_fal, v_l, v_next);


  printf("Input: ");
  print_list(v_cons, print_bool);

  ret = (unsigned int*) call_2(v_clo, 0, v_cons);

  printf("\nReturn: ");
  print_option(ret, print_bool);

  return 0;

}
