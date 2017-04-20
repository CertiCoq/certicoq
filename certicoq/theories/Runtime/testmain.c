#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

extern void build(struct thread_info *)   __attribute__ ((returns_twice)) ;
extern void done(struct thread_info *)   __attribute__ ((returns_twice)) ;

int measure (value t) {
  if (Is_long(t))
    return 0;
  else {
    int i;
    i= 1 + measure(Field(t,1)) + measure (Field(t,2));
    return i;
  }
}

int *stack;

void done(struct thread_info *ti) {
  int x;
  printf ("Stack growth: %d words\n", stack - &x);
}

extern void build(struct thread_info *);

int main(int argc, char *argv[]) {
  struct thread_info *tinfo;
  value n, t;
  int x; stack = &x;
  assert (argc==2);
  n = Val_long (atoi(argv[1]));
  t = Val_long(0);
  tinfo = make_tinfo();
  tinfo->args[4]=n;
  tinfo->args[1]=t;
  build(tinfo);
  t = tinfo->args[1];
  n = measure(t);
  printf("Tree has %d nodes\n", n);
  return 0;
}


