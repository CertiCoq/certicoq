#ifndef CERTICOQ_BENCHMARKS_TESTS_DEMO3_OPT_LL_C
#define CERTICOQ_BENCHMARKS_TESTS_DEMO3_OPT_LL_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Benchmarks.tests.demo3_opt_ll.h"
extern struct thread_info *make_tinfo(void);
extern value CoqdInitdDatatypesdandb_wrapper_103(struct thread_info *, value, value);
extern value CoqdInitdDatatypesdandb_uncurried_known_102(struct thread_info *, value, value);
extern value y_wrapper_101(struct thread_info *, value, value);
extern value body(struct thread_info *);
value CoqdInitdDatatypesdandb_wrapper_103(struct thread_info *, value, value);
value CoqdInitdDatatypesdandb_uncurried_known_102(struct thread_info *, value, value);
value y_wrapper_101(struct thread_info *, value, value);
value body(struct thread_info *);
unsigned long long const body_info_121[2] = { 3LL, 0LL, };

unsigned long long const y_wrapper_info_120[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const CoqdInitdDatatypesdandb_uncurried_known_info_119[4] = {
  0LL, 2LL, 0LL, 1LL, };

unsigned long long const CoqdInitdDatatypesdandb_wrapper_info_118[4] = { 5LL,
  2LL, 0LL, 1LL, };

value CoqdInitdDatatypesdandb_wrapper_103(struct thread_info *$tinfo, value $env_112, value $b1_113)
{
  struct stack_frame frame;
  value root[1];
  register value $env_114;
  register value $y_wrapper_clo_115;
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
    *(root + 0LL) = $b1_113;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 5LL;
    garbage_collect($tinfo);
    $b1_113 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $env_114 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $env_114 + -1LL) = 1024LL;
  *((value *) $env_114 + 0LL) = $b1_113;
  $y_wrapper_clo_115 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_wrapper_clo_115 + -1LL) = 2048LL;
  *((value *) $y_wrapper_clo_115 + 0LL) = y_wrapper_101;
  *((value *) $y_wrapper_clo_115 + 1LL) = $env_114;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $y_wrapper_clo_115;
}

value CoqdInitdDatatypesdandb_uncurried_known_102(struct thread_info *$tinfo, value $b2_109, value $b1_110)
{
  struct stack_frame frame;
  value root[2];
  register value $y_111;
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
  if (($b1_110 & 1) == 0) {
    switch (*((value *) $b1_110 + -1LL) & 255LL) {
      
    }
  } else {
    switch ($b1_110 >> 1LL) {
      case 0:
        $y_111 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_111;
        break;
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $b2_109;
        break;
      
    }
  }
}

value y_wrapper_101(struct thread_info *$tinfo, value $env_104, value $b2_105)
{
  struct stack_frame frame;
  value root[2];
  register value $b1_proj_106;
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
  $b1_proj_106 = *((value *) $env_104 + 0LL);
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value, value)) CoqdInitdDatatypesdandb_uncurried_known_102)
    ($tinfo, $b2_105, $b1_proj_106);
  return $result;
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $env_116;
  register value $CoqdInitdDatatypesdandb_wrapper_clo_117;
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
  $CoqdInitdDatatypesdandb_wrapper_clo_117 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $CoqdInitdDatatypesdandb_wrapper_clo_117 + -1LL) = 2048LL;
  *((value *) $CoqdInitdDatatypesdandb_wrapper_clo_117 + 0LL) =
    CoqdInitdDatatypesdandb_wrapper_103;
  *((value *) $CoqdInitdDatatypesdandb_wrapper_clo_117 + 1LL) = $env_116;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CoqdInitdDatatypesdandb_wrapper_clo_117;
}


#endif /* CERTICOQ_BENCHMARKS_TESTS_DEMO3_OPT_LL_C */
