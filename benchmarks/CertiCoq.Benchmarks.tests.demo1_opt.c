#ifndef CERTICOQ_BENCHMARKS_TESTS_DEMO1_OPT_C
#define CERTICOQ_BENCHMARKS_TESTS_DEMO1_OPT_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Benchmarks.tests.demo1_opt.h"
extern struct thread_info *make_tinfo(void);
extern value app_uncurried_known_102(struct thread_info *, value, value);
extern value repeat_uncurried_known_101(struct thread_info *, value, value);
extern value body(struct thread_info *);
value app_uncurried_known_102(struct thread_info *, value, value);
value repeat_uncurried_known_101(struct thread_info *, value, value);
value body(struct thread_info *);
unsigned long long const body_info_137[2] = { 10LL, 0LL, };

unsigned long long const repeat_uncurried_known_info_136[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const app_uncurried_known_info_135[4] = { 0LL, 2LL, 0LL,
  1LL, };

value app_uncurried_known_102(struct thread_info *$tinfo, value $m_111, value $l_112)
{
  struct stack_frame frame;
  value root[2];
  register value $a_113;
  register value $l1_114;
  register value $y_115;
  register value $y_116;
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
  if (($l_112 & 1) == 0) {
    switch (*((value *) $l_112 + -1LL) & 255LL) {
      default:
        $a_113 = *((value *) $l_112 + 0LL);
        $l1_114 = *((value *) $l_112 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $a_113;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_115 =
          ((value (*)(struct thread_info *, value, value)) app_uncurried_known_102)
          ($tinfo, $m_111, $l1_114);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_115;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_115 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $a_113 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_116 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_116 + -1LL) = 2048LL;
        *((value *) $y_116 + 0LL) = $a_113;
        *((value *) $y_116 + 1LL) = $y_115;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_116;
        break;
      
    }
  } else {
    switch ($l_112 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $m_111;
        break;
      
    }
  }
}

value repeat_uncurried_known_101(struct thread_info *$tinfo, value $n_104, value $x_105)
{
  struct stack_frame frame;
  value root[2];
  register value $y_106;
  register value $k_107;
  register value $y_108;
  register value $y_109;
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
  if (($n_104 & 1) == 0) {
    switch (*((value *) $n_104 + -1LL) & 255LL) {
      default:
        $k_107 = *((value *) $n_104 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $x_105;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_108 =
          ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_101)
          ($tinfo, $k_107, $x_105);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_108;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_108 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_105 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_109 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_109 + -1LL) = 2048LL;
        *((value *) $y_109 + 0LL) = $x_105;
        *((value *) $y_109 + 1LL) = $y_108;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_109;
        break;
      
    }
  } else {
    switch ($n_104 >> 1LL) {
      default:
        $y_106 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_106;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[1];
  register value $y_117;
  register value $y_118;
  register value $y_119;
  register value $y_120;
  register value $y_121;
  register value $y_122;
  register value $y_123;
  register value $y_125;
  register value $y_127;
  register value $y_128;
  register value $y_129;
  register value $y_130;
  register value $y_131;
  register value $y_133;
  register value $CertiCoqdBenchmarksdtestsddemo1_134;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(10LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 10LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_117 = 3LL;
  $y_118 = 1LL;
  $y_119 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_119 + -1LL) = 1024LL;
  *((value *) $y_119 + 0LL) = $y_118;
  $y_120 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_120 + -1LL) = 1024LL;
  *((value *) $y_120 + 0LL) = $y_119;
  $y_121 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_121 + -1LL) = 1024LL;
  *((value *) $y_121 + 0LL) = $y_120;
  $y_122 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_122 + -1LL) = 1024LL;
  *((value *) $y_122 + 0LL) = $y_121;
  $y_123 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_123 + -1LL) = 1024LL;
  *((value *) $y_123 + 0LL) = $y_122;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $y_125 =
    ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_101)
    ($tinfo, $y_123, $y_117);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(6LL <= $limit - $alloc)) {
    *(root + 0LL) = $y_125;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 6LL;
    garbage_collect($tinfo);
    $y_125 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  /*skip*/;
  $y_127 = 1LL;
  $y_128 = 1LL;
  $y_129 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_129 + -1LL) = 1024LL;
  *((value *) $y_129 + 0LL) = $y_128;
  $y_130 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_130 + -1LL) = 1024LL;
  *((value *) $y_130 + 0LL) = $y_129;
  $y_131 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_131 + -1LL) = 1024LL;
  *((value *) $y_131 + 0LL) = $y_130;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $y_125;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_133 =
    ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_101)
    ($tinfo, $y_131, $y_127);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $y_125 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdBenchmarksdtestsddemo1_134 =
    ((value (*)(struct thread_info *, value, value)) app_uncurried_known_102)
    ($tinfo, $y_133, $y_125);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdBenchmarksdtestsddemo1_134;
}


#endif /* CERTICOQ_BENCHMARKS_TESTS_DEMO1_OPT_C */
