#ifndef GLUE_VS_EASY_C
#define GLUE_VS_EASY_C
#include <gc_stack.h>
#include <stdio.h>
#include "glue_vs_easy.h"
struct closure;
struct closure {
  value (*func)(struct thread_info *, value, value);
  value env;
};

extern int is_ptr(value);
unsigned long long get_unboxed_ordinal(value);
unsigned long long get_boxed_ordinal(value);
value *get_args(value);
value make_Coq_Init_Datatypes_bool_true(void);
value make_Coq_Init_Datatypes_bool_false(void);
value make_Coq_Init_Datatypes_list_nil(void);
value make_Coq_Init_Datatypes_list_cons(value, value, value *);
value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);
value make_Coq_Numbers_BinNums_positive_xI(value, value *);
value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, value);
value make_Coq_Numbers_BinNums_positive_xO(value, value *);
value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, value);
value make_Coq_Numbers_BinNums_positive_xH(void);
value make_CertiCoq_Tests_lib_vs_expr_Nil(void);
value make_CertiCoq_Tests_lib_vs_expr_Var(value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_expr_Var(struct thread_info *, value);
value make_CertiCoq_Tests_lib_vs_space_atom_Next(value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Next(struct thread_info *, value, value);
value make_CertiCoq_Tests_lib_vs_space_atom_Lseg(value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Lseg(struct thread_info *, value, value);
value make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(struct thread_info *, value, value);
value make_Coq_Numbers_BinNums_Z_Z0(void);
value make_Coq_Numbers_BinNums_Z_Zpos(value, value *);
value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, value);
value make_Coq_Numbers_BinNums_Z_Zneg(value, value *);
value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, value);
value make_CertiCoq_Tests_lib_vs_clause_PureClause(value, value, value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_clause_PureClause(struct thread_info *, value, value, value, value);
value make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(value, value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(struct thread_info *, value, value, value);
value make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(value, value, value, value *);
value alloc_make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(struct thread_info *, value, value, value);
unsigned long long get_Coq_Init_Datatypes_bool_tag(value);
unsigned long long get_Coq_Init_Datatypes_list_tag(value);
unsigned long long get_Coq_Numbers_BinNums_positive_tag(value);
unsigned long long get_CertiCoq_Tests_lib_vs_expr_tag(value);
unsigned long long get_CertiCoq_Tests_lib_vs_space_atom_tag(value);
unsigned long long get_CertiCoq_Tests_lib_vs_pure_atom_tag(value);
unsigned long long get_Coq_Numbers_BinNums_Z_tag(value);
unsigned long long get_CertiCoq_Tests_lib_vs_clause_tag(value);
void print_Coq_Init_Datatypes_bool(value);
void print_Coq_Init_Datatypes_list(value, void (*)(value));
void print_Coq_Numbers_BinNums_positive(value);
void print_CertiCoq_Tests_lib_vs_expr(value);
void print_CertiCoq_Tests_lib_vs_space_atom(value);
void print_CertiCoq_Tests_lib_vs_pure_atom(value);
void print_Coq_Numbers_BinNums_Z(value);
void print_CertiCoq_Tests_lib_vs_clause(value);
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

signed char const names_of_Coq_Init_Datatypes_bool[2][6] = { 116, 114, 117,
  101, 0, 0, 102, 97, 108, 115, 101, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_list[2][5] = { 110, 105, 108,
  0, 0, 99, 111, 110, 115, 0, /* skip 0 */ };

signed char const names_of_Coq_Numbers_BinNums_positive[3][3] = { 120, 73, 0,
  120, 79, 0, 120, 72, 0, /* skip 0 */ };

signed char const names_of_CertiCoq_Tests_lib_vs_expr[2][4] = { 78, 105, 108,
  0, 86, 97, 114, 0, /* skip 0 */ };

signed char const names_of_CertiCoq_Tests_lib_vs_space_atom[2][5] = { 78,
  101, 120, 116, 0, 76, 115, 101, 103, 0, /* skip 0 */ };

signed char const names_of_CertiCoq_Tests_lib_vs_pure_atom[1][4] = { 69, 113,
  118, 0, /* skip 0 */ };

signed char const names_of_Coq_Numbers_BinNums_Z[3][5] = { 90, 48, 0, 0, 0,
  90, 112, 111, 115, 0, 90, 110, 101, 103, 0, /* skip 0 */ };

signed char const names_of_CertiCoq_Tests_lib_vs_clause[3][15] = { 80, 117,
  114, 101, 67, 108, 97, 117, 115, 101, 0, 0, 0, 0, 0, 80, 111, 115, 83, 112,
  97, 99, 101, 67, 108, 97, 117, 115, 101, 0, 78, 101, 103, 83, 112, 97, 99,
  101, 67, 108, 97, 117, 115, 101, 0, /* skip 0 */ };

value make_Coq_Init_Datatypes_bool_true(void)
{
  return (value) 1;
}

value make_Coq_Init_Datatypes_bool_false(void)
{
  return (value) 3;
}

value make_Coq_Init_Datatypes_list_nil(void)
{
  return (value) 1;
}

value make_Coq_Init_Datatypes_list_cons(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_positive_xI(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_positive_xO(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1025LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1025LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_positive_xH(void)
{
  return (value) 1;
}

value make_CertiCoq_Tests_lib_vs_expr_Nil(void)
{
  return (value) 1;
}

value make_CertiCoq_Tests_lib_vs_expr_Var(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_expr_Var(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_space_atom_Next(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Next(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_space_atom_Lseg(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2049LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Lseg(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2049LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(value $arg0, value $arg1, value *$argv)
{
  *($argv + 0LL) = (value) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(struct thread_info *$tinfo, value $arg0, value $arg1)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_Z_Z0(void)
{
  return (value) 1;
}

value make_Coq_Numbers_BinNums_Z_Zpos(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_Z_Zneg(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1025LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1025LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_clause_PureClause(value $arg0, value $arg1, value $arg2, value $arg3, value *$argv)
{
  *($argv + 0LL) = (value) 4096LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  *($argv + 4LL) = $arg3;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_clause_PureClause(struct thread_info *$tinfo, value $arg0, value $arg1, value $arg2, value $arg3)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 4096LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  *($argv + 4LL) = $arg3;
  (*$tinfo).alloc = (*$tinfo).alloc + 5LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(value $arg0, value $arg1, value $arg2, value *$argv)
{
  *($argv + 0LL) = (value) 3073LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(struct thread_info *$tinfo, value $arg0, value $arg1, value $arg2)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 3073LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  (*$tinfo).alloc = (*$tinfo).alloc + 4LL;
  return $argv + 1LL;
}

value make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(value $arg0, value $arg1, value $arg2, value *$argv)
{
  *($argv + 0LL) = (value) 3074LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  return $argv + 1LL;
}

value alloc_make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(struct thread_info *$tinfo, value $arg0, value $arg1, value $arg2)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 3074LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  (*$tinfo).alloc = (*$tinfo).alloc + 4LL;
  return $argv + 1LL;
}

unsigned long long get_Coq_Init_Datatypes_bool_tag(value $v)
{
  register unsigned long long $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

unsigned long long get_Coq_Init_Datatypes_list_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  }
}

unsigned long long get_Coq_Numbers_BinNums_positive_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      case 1:
        return 1;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 2;
      
    }
  }
}

unsigned long long get_CertiCoq_Tests_lib_vs_expr_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  }
}

unsigned long long get_CertiCoq_Tests_lib_vs_space_atom_tag(value $v)
{
  register unsigned long long $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

unsigned long long get_CertiCoq_Tests_lib_vs_pure_atom_tag(value $v)
{
  register unsigned long long $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

unsigned long long get_Coq_Numbers_BinNums_Z_tag(value $v)
{
  register _Bool $b;
  register unsigned long long $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1;
      case 1:
        return 2;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0;
      
    }
  }
}

unsigned long long get_CertiCoq_Tests_lib_vs_clause_tag(value $v)
{
  register unsigned long long $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

void print_Coq_Init_Datatypes_bool(value $v)
{
  register unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_bool_tag($v);
  printf(*(names_of_Coq_Init_Datatypes_bool + $tag));
}

void print_Coq_Init_Datatypes_list(value $v, void $print_param_A(value))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_list_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      printf(space_lit);
      $print_param_A(*((value *) $args + 0));
      printf(space_lit);
      print_Coq_Init_Datatypes_list(*((value *) $args + 1), $print_param_A);
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Numbers_BinNums_positive(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Numbers_BinNums_positive_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 2:
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      break;
    
  }
}

void print_CertiCoq_Tests_lib_vs_expr(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_CertiCoq_Tests_lib_vs_expr_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_CertiCoq_Tests_lib_vs_expr + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_expr + $tag));
      printf(space_lit);
      printf(unk_lit);
      printf(rparen_lit);
      break;
    
  }
}

void print_CertiCoq_Tests_lib_vs_space_atom(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_CertiCoq_Tests_lib_vs_space_atom_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_space_atom + $tag));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 0));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 1));
      printf(rparen_lit);
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_space_atom + $tag));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 0));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 1));
      printf(rparen_lit);
      break;
    
  }
}

void print_CertiCoq_Tests_lib_vs_pure_atom(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_CertiCoq_Tests_lib_vs_pure_atom_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_pure_atom + $tag));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 0));
      printf(space_lit);
      print_CertiCoq_Tests_lib_vs_expr(*((value *) $args + 1));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Numbers_BinNums_Z(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Numbers_BinNums_Z_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 2:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void print_CertiCoq_Tests_lib_vs_clause(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_CertiCoq_Tests_lib_vs_clause_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_clause + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 0), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 1), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(space_lit);
      printf(unk_lit);
      printf(space_lit);
      printf(prop_lit);
      printf(rparen_lit);
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_clause + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 0), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 1), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 2), print_CertiCoq_Tests_lib_vs_space_atom);
      printf(rparen_lit);
      break;
    case 2:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_CertiCoq_Tests_lib_vs_clause + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 0), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 1), print_CertiCoq_Tests_lib_vs_space_atom);
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((value *) $args + 2), print_CertiCoq_Tests_lib_vs_pure_atom);
      printf(rparen_lit);
      break;
    
  }
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


#endif /* GLUE_VS_EASY_C */
