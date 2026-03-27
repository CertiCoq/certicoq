#ifndef CERTICOQ_BENCHMARKS_TESTS_DEMO3_C
#define CERTICOQ_BENCHMARKS_TESTS_DEMO3_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Benchmarks.tests.demo3.h"
extern struct thread_info *make_tinfo(void);
extern value CoqdInitdDatatypesdandb_uncurried_103(struct thread_info *, value, value);
extern value y_102(struct thread_info *, value, value);
extern value CoqdInitdDatatypesdandb_101(struct thread_info *, value, value);
extern value body(struct thread_info *);
value CoqdInitdDatatypesdandb_uncurried_103(struct thread_info *, value, value);
value y_102(struct thread_info *, value, value);
value CoqdInitdDatatypesdandb_101(struct thread_info *, value, value);
value body(struct thread_info *);
unsigned long long const body_info_121[2] = { 3LL, 0LL, };

unsigned long long const CoqdInitdDatatypesdandb_info_120[4] = { 5LL, 2LL,
  0LL, 1LL, };

unsigned long long const y_info_119[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const CoqdInitdDatatypesdandb_uncurried_info_118[4] = {
  0LL, 2LL, 0LL, 1LL, };

value CoqdInitdDatatypesdandb_uncurried_103(struct thread_info *$tinfo, value $b2_113, value $b1_114)
{
  struct stack_frame frame;
  value root[2];
  register value $y_115;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (($b1_114 & 1) == 0) {
    switch (*((value *) $b1_114 + -1LL) & 255LL) {
      
    }
  } else {
    switch ($b1_114 >> 1LL) {
      case 0:
        $y_115 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_115;
        break;
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $b2_113;
        break;
      
    }
  }
}

value y_102(struct thread_info *$tinfo, value $env_108, value $b2_109)
{
  struct stack_frame frame;
  value root[2];
  register value $b1_proj_111;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  $b1_proj_111 = *((value *) $env_108 + 0LL);
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value, value)) CoqdInitdDatatypesdandb_uncurried_103)
    ($tinfo, $b2_109, $b1_proj_111);
  return $result;
}

value CoqdInitdDatatypesdandb_101(struct thread_info *$tinfo, value $env_104, value $b1_105)
{
  struct stack_frame frame;
  value root[1];
  register value $env_106;
  register value $y_clo_107;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  register _Bool $arg;
  register value $result;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(5LL <= $limit - $alloc)) {
    *(root + 0LL) = $b1_105;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 5LL;
    garbage_collect($tinfo);
    $b1_105 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $env_106 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $env_106 + -1LL) = 1024LL;
  *((value *) $env_106 + 0LL) = $b1_105;
  $y_clo_107 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_clo_107 + -1LL) = 2048LL;
  *((value *) $y_clo_107 + 0LL) = y_102;
  *((value *) $y_clo_107 + 1LL) = $env_106;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $y_clo_107;
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $env_116;
  register value $CoqdInitdDatatypesdandb_clo_117;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(3LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 3LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $env_116 = 1LL;
  $CoqdInitdDatatypesdandb_clo_117 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $CoqdInitdDatatypesdandb_clo_117 + -1LL) = 2048LL;
  *((value *) $CoqdInitdDatatypesdandb_clo_117 + 0LL) =
    CoqdInitdDatatypesdandb_101;
  *((value *) $CoqdInitdDatatypesdandb_clo_117 + 1LL) = $env_116;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CoqdInitdDatatypesdandb_clo_117;
}


#endif /* CERTICOQ_BENCHMARKS_TESTS_DEMO3_C */
