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

#define cons1(p,c,a0)\
  ( allocx[0] = ((1<<10)|c),  \
    allocx[1] = a0, \
    p=(value)(allocx+1), \
    allocx+=(1+1))

#define cons2(p,c,a0,a1)\
  ( allocx[0] = ((2<<10)|c),  \
    allocx[1] = a0, \
    allocx[2] = a1, \
    p=(value)(allocx+1), \
    allocx+=(2+1))


#define cons3(p,c,a0,a1,a2)\
  ( allocx[0] = ((3<<10)|c),  \
    allocx[1] = a0, \
    allocx[2] = a1, \
    allocx[3] = a2, \
    p=(value)(allocx+1), \
    allocx+=(3+1))

#define cons4(p,c,a0,a1,a2,a3)\
  ( allocx[0] = ((4<<10)|c),  \
    allocx[1] = a0, \
    allocx[2] = a1, \
    allocx[3] = a2, \
    allocx[4] = a3, \
    p=(value)(allocx+1), \
    allocx+=(4+1))

#define cons5(p,c,a0,a1,a2,a3,a4)			\
  ( allocx[0] = ((5<<10)|c),  \
    allocx[1] = a0, \
    allocx[2] = a1, \
    allocx[3] = a2, \
    allocx[4] = a3, \
    allocx[5] = a4, \
    p=(value)(allocx+1), \
    allocx+=(5+1))

typedef void (*function)(value*,value*,value,value,value,value);
typedef void (*function0)();

#define jump(f) (((function)f)(allocx,limitx,a1,a2,a3,a4))

struct thread_info tinfo = {args,NARGS,&alloc, &limit, NULL};

#define HEADROOM 100

#define check(fi) \
  {if ( __builtin_expect( \
     (fi[0]<HEADROOM ? (limitx <= allocx) : (limitx-allocx < fi[0]-HEADROOM)), \
     0)) \
    { \
      alloc=allocx; \
      args[1]=a1; args[2]=a2; args[3]=a3; args[4]=a4; \
      garbage_collect(fi,&tinfo); \
      limitx=limit-HEADROOM; \
      allocx=alloc; \
      a1=args[1]; a2=args[2]; a3=args[3]; a4=args[4]; \
    }} 

void build(void);

void insert      (value *allocx, value *limitx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void insert_left (value *allocx, value *limitx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void insert_right(value *allocx, value *limitx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void buildx      (value *allocx, value *limitx, value a1, value a2, value a3, value a4) __attribute__ ((noinline));
void done        (void) __attribute__ ((noinline));

const uintnat fi_insert [] = {5, 4, 1,2,3,4};

void insert(value *allocx, value *limitx, value a1, value a2, value a3, value a4) {
  value t, key, contf, conte;
  check(fi_insert);
  t=a1;
  key=a2;
  contf=a3;
  conte=a4;
  if (t==Null) {
    value u;
    cons3(u,0,key,Null,Null);
    a4=conte;
    a1=u;
    jump(contf);
  } else {
    value k = Field(t,0);
    value left = Field(t,1);
    value right = Field(t,2);
    if (key<k) {
      value e;
      cons4(e,1,k,right,contf,conte);
      a1=left;
      a2=key;
      a3= (value)insert_left;
      a4=e;
      jump(insert);
    } else if (key>k) {
      value e;
      cons4(e,2,k,left,contf,conte);
      a1=right;
      a2=key;
      a3= (value)insert_right;
      a4=e;
      jump(insert);
    } else {
      a4=conte;
      a1=t;
      jump(contf);
    }
  }
}

const uintnat fi_insert_left [] = {4,2, 4,1};

void insert_left(value *allocx, value *limitx, value a1, value a2, value a3, value a4) {
  value k, e, t, u, right, contf, conte;
  check (fi_insert_left);
  e=a4;
  u=a1;
  k=Field(e,0);
  right=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  cons3(t,0,k,u,right);
  a4=conte;
  a1=t;
  jump(contf);
}

const uintnat fi_insert_right [] = {4,2, 4,1};

void insert_right(value *allocx, value *limitx, value a1, value a2, value a3, value a4) {
  value k, e, u, t, left, contf, conte;
  check (fi_insert_right);
  e=a4;
  u=a1;
  k=Field(e,0);
  left=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  cons3(t,0,k,left,u);
  a4=conte;
  a1=t;
  jump(contf);
}

const uintnat fi_buildx [] = {0,2, 4,1};

void buildx(value *allocx, value *limitx, value a1, value a2, value a3, value a4) {
  value n,t;
  check(fi_buildx);  
  n=a4;
  t=a1;
  {value n1 = Long_val(n);
  if (n1>0) {
    value k = Val_long (random() % 1000);
    n1 = Val_long (n1-1);
    a1=t;
    a2=k;
    a3= (value)buildx;
    a4=n1;
    jump(insert);
  } else {
    a1=t;
    alloc=allocx;
    args[1]=a1;
    done();
  }
}}

void build(void) {
  limit=alloc;
  buildx(alloc, limit, args[1], args[2], args[3], args[4]);
}
