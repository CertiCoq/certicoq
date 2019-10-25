#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>
#include "CertiCoq.Benchmarks.demo.is_valid.h"

extern void body(struct thread_info *);

extern value args[];



_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
} 

unsigned long long make_bool_false(void)
{
  return 3;
}

unsigned long long make_bool_true(void)
{
  return 1;
}

signed char const names_of_bool[2][6] = { 102, 97, 108, 115, 101, 0, 116,
  114, 117, 101, 0, 0, };

int const arities_of_bool[2] = { 0LL, 0LL, };

void elim_bool(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      
    }
  } else {
    switch (val >> 1) {
      case 1:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        break;
      case 0:
        *((unsigned long long *) ordinal + 0LLU) = 1LLU;
        break;
      
    }
  }
}
/* OS: not generated */
void bool_elim(value bool){
    value ordinal;
 

    elim_bool(bool, &ordinal, NULL);
    if(ordinal == 0){
      printf(" %s ", names_of_bool[ordinal]);
    } else{
      printf(" %s ", names_of_bool[ordinal]);     
    }
}

int main(int argc, char *argv[]) {
  value val; 

  struct thread_info* tinfo;
  tinfo = make_tinfo();
  body(tinfo);

  val = tinfo -> args[1];
  bool_elim(val);

  return 0;
    
}
