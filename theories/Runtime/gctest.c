#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

value *alloc, *limit;

#define Null ((value)1)

#define NARGS 100
value args[NARGS];

value cons1(unsigned char c, value a1) {
  value *p;
  p=alloc;
  alloc+=2;
  p[0] = ((1<<10)|c);
  p[1] = a1;
  return (value) (p+1);
}

value cons2(unsigned char c, value a1, value a2) {
  value *p;
  p=alloc;
  alloc+=3;
  p[0] = ((2<<10)|c);
  p[1] = a1;
  p[2] = a2;
  return (value) (p+1);
}

value cons3(unsigned char c, value a1, value a2, value a3) {
  value *p;
  p=alloc;
  alloc+=4;
  p[0] = ((3<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  return (value) (p+1);
}

value cons4(unsigned char c, value a1, value a2, value a3, value a4) {
  value *p;
  p=alloc;
  alloc+=5;
  p[0] = ((4<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  p[4] = a4;
  return (value) (p+1);
}

value cons5(unsigned char c, value a1, value a2, value a3, value a4, value a5) {
  value *p;
  p=alloc;
  alloc+=6;
  p[0] = ((5<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  p[4] = a4;
  p[5] = a5;
  return (value) (p+1);
}

#define jump(f) (((void (*)(void))f)())

struct thread_info tinfo = {args,NARGS,&alloc, &limit, NULL};

#define check(fi) \
  {if (limit-alloc < fi.num_allocs) garbage_collect(&fi,&tinfo);} 

void insert(void);
void insert_left(void);
void insert_right(void);
void build(void);
void done(void);

uintnat roots_insert[] = {1,2,3,4};
const struct fun_info fi_insert = {insert, 5, 4, roots_insert};

void insert() {
  value t, key, contf, conte;
  check(fi_insert);
  t=args[1];
  key=args[2];
  contf=args[3];
  conte=args[4];
  if (t==Null) {
    value u = cons3(0,key,Null,Null);
    args[4]=conte;
    args[5]=u;
    jump(contf);
  } else {
    value k = Field(t,0);
    value left = Field(t,1);
    value right = Field(t,2);
    if (key<k) {
      value e = cons4(1,k,right,contf,conte);
      args[1]=left;
      args[2]=key;
      args[3]= (value)insert_left;
      args[4]=e;
      jump(insert);
    } else if (key>k) {
      value e = cons4(2,k,left,contf,conte);
      args[1]=right;
      args[2]=key;
      args[3]= (value)insert_right;
      args[4]=e;
      jump(insert);
    } else {
      value u = cons3(0,k,left,right);
      args[4]=conte;
      args[5]=u;
      jump(contf);
    }
  }
}

uintnat roots_insert_left[] = {4,5};
const struct fun_info fi_insert_left = {insert, 4, 2, roots_insert_left};

void insert_left(void) {
  value k, e, t, u, right, contf, conte;
  check (fi_insert_left);
  e=args[4];
  u=args[5];
  k=Field(e,0);
  right=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(0,k,u,right);
  args[4]=conte;
  args[5]=t;
  jump(contf);
}

uintnat roots_insert_right[] = {4,5};
const struct fun_info fi_insert_right = {insert, 4, 2, roots_insert_right};

void insert_right(void) {
  value k, e, u, t, left, contf, conte;
  check (fi_insert_right);
  e=args[4];
  u=args[5];
  k=Field(e,0);
  left=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(0,k,left,u);
  args[4]=conte;
  args[5]=t;
  jump(contf);
}

void show_stackptr(void) {
  int x;
  fprintf (stderr, "stack: %8x\n", &x);
}  

uintnat roots_build[] = {4,5};
const struct fun_info fi_build = {build, 0, 2, roots_build};

void build() {
  value n,t;
  /*  show_stackptr(); */
  check(fi_build);  
  n=args[4];
  t=args[5];
  {value n1 = Long_val(n);
  if (n1>0) {
    value k = Val_long (random() % 1000);
    n1 = Val_long (n1-1);
    args[1]=t;
    args[2]=k;
    args[3]= (value)build;
    args[4]=n1;
    jump(insert);
  } else {
    args[5]=t;
    jump(done);
  }
}}

int measure (value t) {
  if (t==Null) 
    return 0;
  else {
    int i;
    i= 1 + measure(Field(t,1)) + measure (Field(t,2));
    return i;
  }
}

int *stack;

void done(void) {
  value t = args[5];
  int n = measure(t);
  int x; printf ("Stack growth: %d words\n", stack - &x);
  printf("Tree has %d nodes\n", n);
  exit(0);
}

int main(int argc, char *argv[]) {
  value n, t;
  int x; stack = &x;
  assert (argc==2);
  n = Val_long (atoi(argv[1]));
  t = Null;
  args[4]=n;
  args[5]=t;
  jump(build);
}

