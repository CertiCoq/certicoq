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
  struct thread_info *ti;
  value n, t, count; value *y;
  int x; stack = &x;
  assert (argc==2);
  n = Val_long (atoi(argv[1]));
  t = Val_long(0);
  ti = make_tinfo();
  ti->args[4]=n;
  ti->args[1]=t;
  build(ti);
  count = measure(ti->args[1]);
  printf("Tree has %d nodes\n", count);
  y = extract_answer(ti);
  count = measure(y[1]);
  printf("Extracted tree has %d nodes\n", count);
  printf("Doing it again\n");
  ti->args[4]=n;
  ti->args[1]=t;
  build(ti);
  printf("First tree has %d nodes\n", measure(y[1]));  
  free(y);
  count = measure(ti->args[1]);
  printf("Heap tree has %d nodes\n", count);
  y = extract_answer(ti);
  printf("Second tree has %d nodes\n", measure(y[1]));  
  free(y);
  return 0;
}


