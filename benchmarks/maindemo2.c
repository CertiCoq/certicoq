#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>
#include "demo.demo2.h"

extern void body(struct thread_info *);

extern value args[];




/*
OS: Checks if an int represents a pointer, implemented as an extern in Clight
 */
_Bool is_ptr(unsigned int s) {
  return (_Bool) Is_block(s);
} 

/* OS: not generated */
void option_bool_print(value o_bool){
  unsigned int prod_arr[1]; 
  unsigned int ordinal;
  void *v_bool;

  elim_option(o_bool, &ordinal, prod_arr);
  printf("%s ", names_of_option[ordinal]);
  if(ordinal == 1){
    v_bool = prod_arr[0];
    elim_bool(v_bool, &ordinal, NULL);
    printf("%s", names_of_bool[ordinal]);
  }
  
  printf("\n"); 
} 

/* OS: not generated */
void list_bool_print(value list){
  unsigned int prod_arr[2]; 
  unsigned int ordinal;
  void *v_bool;
 
  unsigned int curr = list;
  printf("(");
  while(1){
    
    elim_list(curr, &ordinal, prod_arr);
    if(ordinal == 0){
      v_bool = prod_arr[0];
      curr = prod_arr[1];
      elim_bool(v_bool, &ordinal, NULL);
      printf(" %s ", names_of_bool[ordinal]);
      printf("::");           
    }else {
      printf(" %s", names_of_list[ordinal]);
      break;
    }
  }
  printf(")\n");
} 


int main(int argc, char *argv[]) {
  unsigned int val; 

  struct thread_info* tinfo;
  tinfo = make_tinfo();
  body(tinfo);
 
  val = tinfo -> args[1];
  
  unsigned int ordinal;
  unsigned int prod_arr[2]; 

  elim_prod(val, &ordinal, prod_arr);
  


  unsigned int ret;
  void *v_clo;

  printf(">>>>> Call to negb\n");
  unsigned int v_fal = make_bool_false();
  elim_bool(v_fal, &ordinal, NULL);
  printf("Input: %s\n", names_of_bool[ordinal]);
  v_clo = prod_arr[0];   
  ret = (unsigned int*) call_1(v_clo, v_fal);
  elim_bool(ret, &ordinal, NULL);
  printf("Return: %s\n", names_of_bool[ordinal]);

  
  printf(">>>>> Call to List.hd_error\n");
  v_clo = prod_arr[1];
  
  unsigned int v_l = make_list_nil();
  unsigned int v_next[3];
  unsigned int v_cons = make_list_cons(v_fal, v_l, v_next);
  

  printf("Input: ");
  list_bool_print(v_cons);

  ret = (unsigned int*) call_2(v_clo, 0, v_cons);

  printf("Return: ");
  option_bool_print(ret);
  
  return 0;
    
}
