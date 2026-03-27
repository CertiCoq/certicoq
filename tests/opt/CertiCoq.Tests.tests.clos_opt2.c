#ifndef CERTICOQ_TESTS_TESTS_CLOS_OPT2_C
#define CERTICOQ_TESTS_TESTS_CLOS_OPT2_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Tests.tests.clos_opt2.h"
extern struct thread_info *make_tinfo(void);
extern value loop_add_uncurried_known_106(struct thread_info *, value, value);
extern value CertiCoqdTestsdtestsdclos_loop_wrapper_105(struct thread_info *, value, value);
extern value repeat_uncurried_known_104(struct thread_info *, value, value);
extern value list_add_uncurried_uncurried_uncurried_known_103(struct thread_info *, value, value, value, value);
extern value CertiCoqdTestsdtestsdclos_loop_known_102(struct thread_info *);
extern value add_uncurried_known_101(struct thread_info *, value, value);
extern value body(struct thread_info *);
value loop_add_uncurried_known_106(struct thread_info *, value, value);
value CertiCoqdTestsdtestsdclos_loop_wrapper_105(struct thread_info *, value, value);
value repeat_uncurried_known_104(struct thread_info *, value, value);
value list_add_uncurried_uncurried_uncurried_known_103(struct thread_info *, value, value, value, value);
value CertiCoqdTestsdtestsdclos_loop_known_102(struct thread_info *);
value add_uncurried_known_101(struct thread_info *, value, value);
value body(struct thread_info *);
unsigned long long const body_info_167[2] = { 5LL, 0LL, };

unsigned long long const add_uncurried_known_info_166[4] = { 0LL, 2LL, 0LL,
  1LL, };

unsigned long long const CertiCoqdTestsdtestsdclos_loop_known_info_165[2] = {
  2LL, 0LL, };

unsigned long long const list_add_uncurried_uncurried_uncurried_known_info_164[6] = {
  0LL, 4LL, 0LL, 1LL, 2LL, 3LL, };

unsigned long long const repeat_uncurried_known_info_163[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const CertiCoqdTestsdtestsdclos_loop_wrapper_info_162[4] = {
  2LL, 2LL, 0LL, 1LL, };

unsigned long long const loop_add_uncurried_known_info_161[4] = { 0LL, 2LL,
  0LL, 1LL, };

value loop_add_uncurried_known_106(struct thread_info *$tinfo, value $f_145, value $n_146)
{
  struct stack_frame frame;
  value root[2];
  register value $y_147;
  register value $f_code_148;
  register value $f_env_149;
  register value $n_150;
  register value $y_151;
  register value $f_code_152;
  register value $f_env_153;
  register value $y_154;
  register value $y_155;
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
  if (($n_146 & 1) == 0) {
    switch (*((value *) $n_146 + -1LL) & 255LL) {
      default:
        $n_150 = *((value *) $n_146 + 0LL);
        $y_151 = 1LL;
        $f_code_152 = *((value *) $f_145 + 0LL);
        $f_env_153 = *((value *) $f_145 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $n_150;
        *(root + 0LL) = $f_145;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_154 =
          ((value (*)(struct thread_info *, value, value)) $f_code_152)
          ($tinfo, $f_env_153, $y_151);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n_150 = *(root + 1LL);
        $f_145 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_154;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_155 =
          ((value (*)(struct thread_info *, value, value)) loop_add_uncurried_known_106)
          ($tinfo, $f_145, $n_150);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_154 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $y_155, $y_154);
        return $result;
        break;
      
    }
  } else {
    switch ($n_146 >> 1LL) {
      default:
        $y_147 = 1LL;
        $f_code_148 = *((value *) $f_145 + 0LL);
        $f_env_149 = *((value *) $f_145 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) $f_code_148)
          ($tinfo, $f_env_149, $y_147);
        return $result;
        break;
      
    }
  }
}

value CertiCoqdTestsdtestsdclos_loop_wrapper_105(struct thread_info *$tinfo, value $env_136, value $u_137)
{
  struct stack_frame frame;
  value root[3];
  register value $y_138;
  register value $y_139;
  register value $y_140;
  register value $y_141;
  register value $y_142;
  register value $y_143;
  register value $y_144;
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
  if (!(2LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_138 = 1LL;
  $y_139 = 1LL;
  $y_140 = 1LL;
  $y_141 = 1LL;
  $y_142 = 1LL;
  $y_143 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_143 + -1LL) = 1024LL;
  *((value *) $y_143 + 0LL) = $y_142;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 2LL) = $y_140;
  *(root + 1LL) = $y_139;
  *(root + 0LL) = $y_138;
  frame.next = root + 3LL;
  (*$tinfo).fp = &frame;
  $y_144 =
    ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_104)
    ($tinfo, $y_143, $y_141);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $y_140 = *(root + 2LL);
  $y_139 = *(root + 1LL);
  $y_138 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value, value, value, value)) list_add_uncurried_uncurried_uncurried_known_103)
    ($tinfo, $y_144, $y_140, $y_139, $y_138);
  return $result;
}

value repeat_uncurried_known_104(struct thread_info *$tinfo, value $n_130, value $x_131)
{
  struct stack_frame frame;
  value root[2];
  register value $y_132;
  register value $k_133;
  register value $y_134;
  register value $y_135;
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
  if (($n_130 & 1) == 0) {
    switch (*((value *) $n_130 + -1LL) & 255LL) {
      default:
        $k_133 = *((value *) $n_130 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $x_131;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_134 =
          ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_104)
          ($tinfo, $k_133, $x_131);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_134;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_134 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_131 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_135 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_135 + -1LL) = 2048LL;
        *((value *) $y_135 + 0LL) = $x_131;
        *((value *) $y_135 + 1LL) = $y_134;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_135;
        break;
      
    }
  } else {
    switch ($n_130 >> 1LL) {
      default:
        $y_132 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_132;
        break;
      
    }
  }
}

value list_add_uncurried_uncurried_uncurried_known_103(struct thread_info *$tinfo, value $l_119, value $k3_120, value $k2_121, value $k1_122)
{
  struct stack_frame frame;
  value root[5];
  register value $y_123;
  register value $x_124;
  register value $xs_125;
  register value $y_126;
  register value $y_127;
  register value $y_128;
  register value $y_129;
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
  if (($l_119 & 1) == 0) {
    switch (*((value *) $l_119 + -1LL) & 255LL) {
      default:
        $x_124 = *((value *) $l_119 + 0LL);
        $xs_125 = *((value *) $l_119 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 4LL) = $xs_125;
        *(root + 3LL) = $x_124;
        *(root + 2LL) = $k1_122;
        *(root + 1LL) = $k2_121;
        *(root + 0LL) = $k3_120;
        frame.next = root + 5LL;
        (*$tinfo).fp = &frame;
        $y_126 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $k2_121, $k1_122);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_125 = *(root + 4LL);
        $x_124 = *(root + 3LL);
        $k1_122 = *(root + 2LL);
        $k2_121 = *(root + 1LL);
        $k3_120 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 4LL) = $xs_125;
        *(root + 3LL) = $x_124;
        *(root + 2LL) = $k1_122;
        *(root + 1LL) = $k2_121;
        *(root + 0LL) = $k3_120;
        frame.next = root + 5LL;
        (*$tinfo).fp = &frame;
        $y_127 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $k3_120, $y_126);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_125 = *(root + 4LL);
        $x_124 = *(root + 3LL);
        $k1_122 = *(root + 2LL);
        $k2_121 = *(root + 1LL);
        $k3_120 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 3LL) = $xs_125;
        *(root + 2LL) = $k1_122;
        *(root + 1LL) = $k2_121;
        *(root + 0LL) = $k3_120;
        frame.next = root + 4LL;
        (*$tinfo).fp = &frame;
        $y_128 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $x_124, $y_127);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_125 = *(root + 3LL);
        $k1_122 = *(root + 2LL);
        $k2_121 = *(root + 1LL);
        $k3_120 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_128;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_129 =
          ((value (*)(struct thread_info *, value, value, value, value)) 
            list_add_uncurried_uncurried_uncurried_known_103)
          ($tinfo, $xs_125, $k3_120, $k2_121, $k1_122);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_128 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $y_129, $y_128);
        return $result;
        break;
      
    }
  } else {
    switch ($l_119 >> 1LL) {
      default:
        $y_123 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_123;
        break;
      
    }
  }
}

value CertiCoqdTestsdtestsdclos_loop_known_102(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[3];
  register value $y_112;
  register value $y_113;
  register value $y_114;
  register value $y_115;
  register value $y_116;
  register value $y_117;
  register value $y_118;
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
  if (!(2LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_112 = 1LL;
  $y_113 = 1LL;
  $y_114 = 1LL;
  $y_115 = 1LL;
  $y_116 = 1LL;
  $y_117 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_117 + -1LL) = 1024LL;
  *((value *) $y_117 + 0LL) = $y_116;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 2LL) = $y_114;
  *(root + 1LL) = $y_113;
  *(root + 0LL) = $y_112;
  frame.next = root + 3LL;
  (*$tinfo).fp = &frame;
  $y_118 =
    ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_104)
    ($tinfo, $y_117, $y_115);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $y_114 = *(root + 2LL);
  $y_113 = *(root + 1LL);
  $y_112 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value, value, value, value)) list_add_uncurried_uncurried_uncurried_known_103)
    ($tinfo, $y_118, $y_114, $y_113, $y_112);
  return $result;
}

value add_uncurried_known_101(struct thread_info *$tinfo, value $m_107, value $n_108)
{
  struct stack_frame frame;
  value root[2];
  register value $p_109;
  register value $y_110;
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
  if (($n_108 & 1) == 0) {
    switch (*((value *) $n_108 + -1LL) & 255LL) {
      default:
        $p_109 = *((value *) $n_108 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_110 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $m_107, $p_109);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_110;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_110 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_111 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_111 + -1LL) = 1024LL;
        *((value *) $y_111 + 0LL) = $y_110;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_111;
        break;
      
    }
  } else {
    switch ($n_108 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $m_107;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $env_156;
  register value $y_157;
  register value $y_158;
  register value $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159;
  register value $CertiCoqdTestsdtestsdclos_160;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(5LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 5LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $env_156 = 1LL;
  $y_157 = 1LL;
  $y_158 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_158 + -1LL) = 1024LL;
  *((value *) $y_158 + 0LL) = $y_157;
  $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159 + -1LL) =
    2048LL;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159 + 0LL) =
    CertiCoqdTestsdtestsdclos_loop_wrapper_105;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159 + 1LL) =
    $env_156;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdTestsdtestsdclos_160 =
    ((value (*)(struct thread_info *, value, value)) loop_add_uncurried_known_106)
    ($tinfo, $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_159, $y_158);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdTestsdtestsdclos_160;
}


#endif /* CERTICOQ_TESTS_TESTS_CLOS_OPT2_C */
