#ifndef GLUE_C
#define GLUE_C
#include <gc_stack.h>
#include <stdio.h>
#include "glue.h"
struct closure;
struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

extern int is_ptr(value);
unsigned long long get_unboxed_ordinal(value);
unsigned long long get_boxed_ordinal(value);
value *get_args(value);
value call(struct thread_info *, value, value);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned long long get_unboxed_ordinal(value $v)
{
  return (unsigned long long) $v >> 1LL;
}

unsigned long long get_boxed_ordinal(value $v)
{
  return (unsigned long long) *((unsigned long long *) $v + -1LL) & 255LL;
}

value *get_args(value $v)
{
  return (value *) $v;
}

value call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register value $f;
  register value $envi;
  register value $tmp;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  $tmp =
    ((value (*)(struct thread_info *, value, value)) $f)
    ($tinfo, $envi, $arg);
  return $tmp;
}


#endif /* GLUE_C */
