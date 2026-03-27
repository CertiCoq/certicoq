#ifndef CERTICOQ_TESTS_TESTS_FIBN_C
#define CERTICOQ_TESTS_TESTS_FIBN_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "int63.h"
#include "CertiCoq.Tests.tests.fibn.h"
extern struct thread_info *make_tinfo(void);
extern value fib_aux_uncurried_uncurried_known_106(struct thread_info *, value, value, value);
extern value body(struct thread_info *);
value fib_aux_uncurried_uncurried_known_106(struct thread_info *, value, value, value);
value body(struct thread_info *);
unsigned long long const body_info_133[2] = { 22LL, 0LL, };

unsigned long long const fib_aux_uncurried_uncurried_known_info_132[5] = {
  0LL, 3LL, 0LL, 1LL, 2LL, };

value fib_aux_uncurried_uncurried_known_106(struct thread_info *$tinfo, value $prev1_108, value $prev0_109, value $n_110)
{
  struct stack_frame frame;
  value root[3];
  register value $n_111;
  register value $prim_112;
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
  if (($n_110 & 1) == 0) {
    switch (*((value *) $n_110 + -1LL) & 255LL) {
      default:
        $n_111 = *((value *) $n_110 + 0LL);
        if (($n_111 & 1) == 0) {
          switch (*((value *) $n_111 + -1LL) & 255LL) {
            default:
              $prim_112 =
                ((value (*)(value, value)) add_int63)
                ($prev0_109, $prev1_108);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              $result =
                ((value (*)(struct thread_info *, value, value, value)) 
                  fib_aux_uncurried_uncurried_known_106)
                ($tinfo, $prim_112, $prev1_108, $n_111);
              return $result;
              break;
            
          }
        } else {
          switch ($n_111 >> 1LL) {
            default:
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $prev1_108;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($n_110 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $prev0_109;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $y_113;
  register value $y_114;
  register value $y_115;
  register value $y_116;
  register value $y_117;
  register value $y_118;
  register value $y_119;
  register value $y_120;
  register value $y_121;
  register value $y_122;
  register value $y_123;
  register value $y_124;
  register value $prim_126;
  register value $prim_127;
  register value $y_128;
  register value $prim_129;
  register value $y_130;
  register value $prim_131;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(22LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 22LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_113 = 1LL;
  $y_114 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_114 + -1LL) = 1024LL;
  *((value *) $y_114 + 0LL) = $y_113;
  $y_115 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_115 + -1LL) = 1024LL;
  *((value *) $y_115 + 0LL) = $y_114;
  $y_116 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_116 + -1LL) = 1024LL;
  *((value *) $y_116 + 0LL) = $y_115;
  $y_117 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_117 + -1LL) = 1024LL;
  *((value *) $y_117 + 0LL) = $y_116;
  $y_118 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_118 + -1LL) = 1024LL;
  *((value *) $y_118 + 0LL) = $y_117;
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
  $y_124 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_124 + -1LL) = 1024LL;
  *((value *) $y_124 + 0LL) = $y_123;
  $prim_126 = ((value (*)(void)) zero_int63)();
  $prim_127 = ((value (*)(void)) one_int63)();
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $y_128 =
    ((value (*)(struct thread_info *, value, value, value)) fib_aux_uncurried_uncurried_known_106)
    ($tinfo, $prim_127, $prim_126, $y_124);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  $prim_129 = ((value (*)(value)) print_int63)($y_128);
  $y_130 = 1LL;
  $prim_131 = ((value (*)(value)) print_new_line)($y_130);
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $prim_131;
}


#endif /* CERTICOQ_TESTS_TESTS_FIBN_C */
