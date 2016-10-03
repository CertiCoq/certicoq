#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

extern void build(void)   __attribute__ ((returns_twice)) ;
extern void done(void)   __attribute__ ((returns_twice)) ;

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

extern value args[];

void done(void) {
  int x;
  printf ("Stack growth: %d words\n", stack - &x);
}

extern void build(void);

int main(int argc, char *argv[]) {
  value n, t;
  int x; stack = &x;
  assert (argc==2);
  n = Val_long (atoi(argv[1]));
  t = Val_long(0);
  args[4]=n;
  args[1]=t;
  build();
  t = args[1];
  n = measure(t);
  printf("Tree has %d nodes\n", n);
  return 0;
}


