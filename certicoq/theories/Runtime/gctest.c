#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

#define Null ((value)1)

value *alloc, *limit;
#define NARGS 100
value args[NARGS];
struct thread_info tinfo = {args,NARGS,&alloc, &limit, NULL};


inline static value cons1(unsigned char c, value a1) {
  value *p;
  p=alloc;
  alloc+=2;
  p[0] = ((1<<10)|c);
  p[1] = a1;
  return (value) (p+1);
}

inline static value cons2(unsigned char c, value a1, value a2) {
  value *p;
  p=alloc;
  alloc+=3;
  p[0] = ((2<<10)|c);
  p[1] = a1;
  p[2] = a2;
  return (value) (p+1);
}

inline static value cons3(unsigned char c, value a1, value a2, value a3) {
  value *p;
  p=alloc;
  alloc+=4;
  p[0] = ((3<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  return (value) (p+1);
}

inline static value cons4(unsigned char c, value a1, value a2, value a3, value a4) {
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

inline static value cons5(unsigned char c, value a1, value a2, value a3, value a4, value a5) {
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

#define check(fi) \
  {if (limit-alloc < fi[0]) garbage_collect(fi,&tinfo);} 

void insert(void);
void insert_left(void);
void insert_right(void);
void build(void);
extern void done(void);

const uintnat fi_insert [] = {5, 4, 1,2,3,4};

void insert (void) {
  value t, key, contf, conte;
  check(fi_insert);
  t=args[1];
  key=args[2];
  contf=args[3];
  conte=args[4];
  if (t==Null) {
    value u = cons3(0,key,Null,Null);
    args[4]=conte;
    args[1]=u;
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
      args[4]=conte;
      args[1]=t;
      jump(contf);
    }
  }
}

const uintnat fi_insert_left [] = {4,2, 4,1};

void insert_left(void)
{
  value k, e, t, u, right, contf, conte;
  check (fi_insert_left);
  e=args[4];
  u=args[1];
  k=Field(e,0);
  right=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(0,k,u,right);
  args[4]=conte;
  args[1]=t;
  jump(contf);
}

const uintnat fi_insert_right [] = {4,2, 4,1};

void insert_right(void)
{
  value k, e, u, t, left, contf, conte;
  check (fi_insert_right);
  e=args[4];
  u=args[1];
  k=Field(e,0);
  left=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(0,k,left,u);
  args[4]=conte;
  args[1]=t;
  jump(contf);
}


const uintnat fi_build [] = {0,2, 4,1};

void build(void) {
  value n,t;
  /*  show_stackptr(); */
  check(fi_build);  
  n=args[4];
  t=args[1];
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
    args[1]=t;
    jump(done);
  }
}}
