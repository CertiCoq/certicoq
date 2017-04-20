#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "values.h"
#include "gc.h"

#define Null ((value)1)

inline static value cons1(struct thread_info *ti, unsigned char c, value a1) {
  value *p;
  p=ti->alloc;
  ti->alloc=p+2;
  p[0] = ((1<<10)|c);
  p[1] = a1;
  return (value) (p+1);
}

inline static value cons2(struct thread_info *ti, unsigned char c, value a1, value a2) {
  value *p;
  p=ti->alloc;
  ti->alloc=p+3;
  p[0] = ((2<<10)|c);
  p[1] = a1;
  p[2] = a2;
  return (value) (p+1);
}

inline static value cons3(struct thread_info *ti, unsigned char c, value a1, value a2, value a3) {
  value *p;
  p=ti->alloc;
  ti->alloc=p+4;
  p[0] = ((3<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  return (value) (p+1);
}

inline static value cons4(struct thread_info *ti, unsigned char c, value a1, value a2, value a3, value a4) {
  value *p;
  p=ti->alloc;
  ti->alloc=p+5;
  p[0] = ((4<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  p[4] = a4;
  return (value) (p+1);
}

inline static value cons5(struct thread_info *ti, unsigned char c, value a1, value a2, value a3, value a4, value a5) {
  value *p;
  p=ti->alloc;
  ti->alloc=p+6;
  p[0] = ((5<<10)|c);
  p[1] = a1;
  p[2] = a2;
  p[3] = a3;
  p[4] = a4;
  p[5] = a5;
  return (value) (p+1);
}

#define jump(f) (((void (*)(struct thread_info *))f)(ti))

#define check(fi) \
  {if (ti->limit-ti->alloc < fi[0]) garbage_collect(fi,ti);} 

void insert(struct thread_info *);
void insert_left(struct thread_info *);
void insert_right(struct thread_info *);
void build(struct thread_info *);
extern void done(struct thread_info *);

const uintnat fi_insert [] = {5, 4, 1,2,3,4};

void insert (struct thread_info *ti) {
  value t, key, contf, conte;
  check(fi_insert);
  t=ti->args[1];
  key=ti->args[2];
  contf=ti->args[3];
  conte=ti->args[4];
  if (t==Null) {
    value u = cons3(ti,0,key,Null,Null);
    ti->args[4]=conte;
    ti->args[1]=u;
    jump(contf);
  } else {
    value k = Field(t,0);
    value left = Field(t,1);
    value right = Field(t,2);
    if (key<k) {
      value e = cons4(ti,1,k,right,contf,conte);
      ti->args[1]=left;
      ti->args[2]=key;
      ti->args[3]= (value)insert_left;
      ti->args[4]=e;
      jump(insert);
    } else if (key>k) {
      value e = cons4(ti,2,k,left,contf,conte);
      ti->args[1]=right;
      ti->args[2]=key;
      ti->args[3]= (value)insert_right;
      ti->args[4]=e;
      jump(insert);
    } else {
      ti->args[4]=conte;
      ti->args[1]=t;
      jump(contf);
    }
  }
}

const uintnat fi_insert_left [] = {4,2, 4,1};

void insert_left(struct thread_info *ti)
{
  value k, e, t, u, right, contf, conte;
  check (fi_insert_left);
  e=ti->args[4];
  u=ti->args[1];
  k=Field(e,0);
  right=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(ti,0,k,u,right);
  ti->args[4]=conte;
  ti->args[1]=t;
  jump(contf);
}

const uintnat fi_insert_right [] = {4,2, 4,1};

void insert_right(struct thread_info *ti)
{
  value k, e, u, t, left, contf, conte;
  check (fi_insert_right);
  e=ti->args[4];
  u=ti->args[1];
  k=Field(e,0);
  left=Field(e,1);
  contf=Field(e,2);
  conte=Field(e,3);
  t = cons3(ti,0,k,left,u);
  ti->args[4]=conte;
  ti->args[1]=t;
  jump(contf);
}


const uintnat fi_build [] = {0,2, 4,1};

void build(struct thread_info *ti) {
  value n,t;
  /*  show_stackptr(); */
  check(fi_build);  
  n=ti->args[4];
  t=ti->args[1];
  {value n1 = Long_val(n);
  if (n1>0) {
    value k = Val_long (random() % 1000);
    n1 = Val_long (n1-1);
    ti->args[1]=t;
    ti->args[2]=k;
    ti->args[3]= (value)build;
    ti->args[4]=n1;
    jump(insert);
  } else {
    ti->args[1]=t;
    jump(done);
  }
}}
