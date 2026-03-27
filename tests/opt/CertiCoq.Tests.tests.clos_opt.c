#ifndef CERTICOQ_TESTS_TESTS_CLOS_OPT_C
#define CERTICOQ_TESTS_TESTS_CLOS_OPT_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Tests.tests.clos_opt.h"
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
unsigned long long const body_info_175[2] = { 5LL, 0LL, };

unsigned long long const add_uncurried_known_info_174[4] = { 0LL, 2LL, 0LL,
  1LL, };

unsigned long long const CertiCoqdTestsdtestsdclos_loop_known_info_173[2] = {
  2LL, 0LL, };

unsigned long long const list_add_uncurried_uncurried_uncurried_known_info_172[6] = {
  0LL, 4LL, 0LL, 1LL, 2LL, 3LL, };

unsigned long long const repeat_uncurried_known_info_171[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const CertiCoqdTestsdtestsdclos_loop_wrapper_info_170[4] = {
  0LL, 2LL, 0LL, 1LL, };

unsigned long long const loop_add_uncurried_known_info_169[4] = { 0LL, 2LL,
  0LL, 1LL, };

value loop_add_uncurried_known_106(struct thread_info *$tinfo, value $f_151, value $n_152)
{
  struct stack_frame frame;
  value root[2];
  register value $y_153;
  register value $f_code_154;
  register value $f_env_155;
  register value $n_156;
  register value $y_157;
  register value $f_code_158;
  register value $f_env_159;
  register value $y_160;
  register value $y_161;
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
  if (($n_152 & 1) == 0) {
    switch (*((value *) $n_152 + -1LL) & 255LL) {
      default:
        $n_156 = *((value *) $n_152 + 0LL);
        $y_157 = 1LL;
        $f_code_158 = *((value *) $f_151 + 0LL);
        $f_env_159 = *((value *) $f_151 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $n_156;
        *(root + 0LL) = $f_151;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_160 =
          ((value (*)(struct thread_info *, value, value)) $f_code_158)
          ($tinfo, $f_env_159, $y_157);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n_156 = *(root + 1LL);
        $f_151 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_160;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_161 =
          ((value (*)(struct thread_info *, value, value)) loop_add_uncurried_known_106)
          ($tinfo, $f_151, $n_156);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_160 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $y_161, $y_160);
        return $result;
        break;
      
    }
  } else {
    switch ($n_152 >> 1LL) {
      default:
        $y_153 = 1LL;
        $f_code_154 = *((value *) $f_151 + 0LL);
        $f_env_155 = *((value *) $f_151 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) $f_code_154)
          ($tinfo, $f_env_155, $y_153);
        return $result;
        break;
      
    }
  }
}

value CertiCoqdTestsdtestsdclos_loop_wrapper_105(struct thread_info *$tinfo, value $env_147, value $u_148)
{
  struct stack_frame frame;
  value root[0];
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
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *)) CertiCoqdTestsdtestsdclos_loop_known_102)
    ($tinfo);
  return $result;
}

value repeat_uncurried_known_104(struct thread_info *$tinfo, value $n_141, value $x_142)
{
  struct stack_frame frame;
  value root[2];
  register value $y_143;
  register value $k_144;
  register value $y_145;
  register value $y_146;
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
  if (($n_141 & 1) == 0) {
    switch (*((value *) $n_141 + -1LL) & 255LL) {
      default:
        $k_144 = *((value *) $n_141 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $x_142;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_145 =
          ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_104)
          ($tinfo, $k_144, $x_142);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_145;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_145 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_142 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_146 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_146 + -1LL) = 2048LL;
        *((value *) $y_146 + 0LL) = $x_142;
        *((value *) $y_146 + 1LL) = $y_145;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_146;
        break;
      
    }
  } else {
    switch ($n_141 >> 1LL) {
      default:
        $y_143 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_143;
        break;
      
    }
  }
}

value list_add_uncurried_uncurried_uncurried_known_103(struct thread_info *$tinfo, value $l_125, value $k3_126, value $k2_127, value $k1_128)
{
  struct stack_frame frame;
  value root[5];
  register value $y_129;
  register value $x_130;
  register value $xs_131;
  register value $y_133;
  register value $y_135;
  register value $y_137;
  register value $y_138;
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
  if (($l_125 & 1) == 0) {
    switch (*((value *) $l_125 + -1LL) & 255LL) {
      default:
        $x_130 = *((value *) $l_125 + 0LL);
        $xs_131 = *((value *) $l_125 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 4LL) = $xs_131;
        *(root + 3LL) = $x_130;
        *(root + 2LL) = $k1_128;
        *(root + 1LL) = $k2_127;
        *(root + 0LL) = $k3_126;
        frame.next = root + 5LL;
        (*$tinfo).fp = &frame;
        $y_133 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $k2_127, $k1_128);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_131 = *(root + 4LL);
        $x_130 = *(root + 3LL);
        $k1_128 = *(root + 2LL);
        $k2_127 = *(root + 1LL);
        $k3_126 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 4LL) = $xs_131;
        *(root + 3LL) = $x_130;
        *(root + 2LL) = $k1_128;
        *(root + 1LL) = $k2_127;
        *(root + 0LL) = $k3_126;
        frame.next = root + 5LL;
        (*$tinfo).fp = &frame;
        $y_135 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $k3_126, $y_133);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_131 = *(root + 4LL);
        $x_130 = *(root + 3LL);
        $k1_128 = *(root + 2LL);
        $k2_127 = *(root + 1LL);
        $k3_126 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 3LL) = $xs_131;
        *(root + 2LL) = $k1_128;
        *(root + 1LL) = $k2_127;
        *(root + 0LL) = $k3_126;
        frame.next = root + 4LL;
        (*$tinfo).fp = &frame;
        $y_137 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $x_130, $y_135);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $xs_131 = *(root + 3LL);
        $k1_128 = *(root + 2LL);
        $k2_127 = *(root + 1LL);
        $k3_126 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_137;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_138 =
          ((value (*)(struct thread_info *, value, value, value, value)) 
            list_add_uncurried_uncurried_uncurried_known_103)
          ($tinfo, $xs_131, $k3_126, $k2_127, $k1_128);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_137 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $y_138, $y_137);
        return $result;
        break;
      
    }
  } else {
    switch ($l_125 >> 1LL) {
      default:
        $y_129 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_129;
        break;
      
    }
  }
}

value CertiCoqdTestsdtestsdclos_loop_known_102(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[3];
  register value $y_116;
  register value $y_117;
  register value $y_118;
  register value $y_119;
  register value $y_120;
  register value $y_121;
  register value $y_123;
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
  $y_116 = 1LL;
  $y_117 = 1LL;
  $y_118 = 1LL;
  $y_119 = 1LL;
  $y_120 = 1LL;
  $y_121 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_121 + -1LL) = 1024LL;
  *((value *) $y_121 + 0LL) = $y_120;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 2LL) = $y_118;
  *(root + 1LL) = $y_117;
  *(root + 0LL) = $y_116;
  frame.next = root + 3LL;
  (*$tinfo).fp = &frame;
  $y_123 =
    ((value (*)(struct thread_info *, value, value)) repeat_uncurried_known_104)
    ($tinfo, $y_121, $y_119);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $y_118 = *(root + 2LL);
  $y_117 = *(root + 1LL);
  $y_116 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  $result =
    ((value (*)(struct thread_info *, value, value, value, value)) list_add_uncurried_uncurried_uncurried_known_103)
    ($tinfo, $y_123, $y_118, $y_117, $y_116);
  return $result;
}

value add_uncurried_known_101(struct thread_info *$tinfo, value $m_108, value $n_109)
{
  struct stack_frame frame;
  value root[2];
  register value $p_110;
  register value $y_111;
  register value $y_112;
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
  if (($n_109 & 1) == 0) {
    switch (*((value *) $n_109 + -1LL) & 255LL) {
      default:
        $p_110 = *((value *) $n_109 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_111 =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_101)
          ($tinfo, $m_108, $p_110);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_111;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_111 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_112 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_112 + -1LL) = 1024LL;
        *((value *) $y_112 + 0LL) = $y_111;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_112;
        break;
      
    }
  } else {
    switch ($n_109 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $m_108;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $env_163;
  register value $y_164;
  register value $y_165;
  register value $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167;
  register value $CertiCoqdTestsdtestsdclos_168;
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
  $env_163 = 1LL;
  $y_164 = 1LL;
  $y_165 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_165 + -1LL) = 1024LL;
  *((value *) $y_165 + 0LL) = $y_164;
  $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167 + -1LL) =
    2048LL;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167 + 0LL) =
    CertiCoqdTestsdtestsdclos_loop_wrapper_105;
  *((value *) $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167 + 1LL) =
    $env_163;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdTestsdtestsdclos_168 =
    ((value (*)(struct thread_info *, value, value)) loop_add_uncurried_known_106)
    ($tinfo, $CertiCoqdTestsdtestsdclos_loop_wrapper_clo_167, $y_165);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdTestsdtestsdclos_168;
}


#endif /* CERTICOQ_TESTS_TESTS_CLOS_OPT_C */
