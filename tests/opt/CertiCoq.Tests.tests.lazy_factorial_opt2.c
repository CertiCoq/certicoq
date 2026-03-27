#ifndef CERTICOQ_TESTS_TESTS_LAZY_FACTORIAL_OPT2_C
#define CERTICOQ_TESTS_TESTS_LAZY_FACTORIAL_OPT2_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Tests.tests.lazy_factorial_opt2.h"
extern struct thread_info *make_tinfo(void);
extern value append_uncurried_known_127(struct thread_info *, value, value);
extern value f_case_known_126(struct thread_info *, value);
extern value is_eq_uncurried_known_125(struct thread_info *, value, value);
extern value y_wrapper_124(struct thread_info *, value, value);
extern value y_wrapper_123(struct thread_info *, value, value);
extern value f_case_known_122(struct thread_info *, value, value);
extern value f_case_known_121(struct thread_info *, value, value);
extern value f_case_known_120(struct thread_info *, value);
extern value memo_get_uncurried_known_119(struct thread_info *, value, value);
extern value y_wrapper_118(struct thread_info *, value, value);
extern value y_wrapper_117(struct thread_info *, value, value);
extern value f_case_known_116(struct thread_info *, value);
extern value tfact_known_115(struct thread_info *, value);
extern value of_succ_nat_known_114(struct thread_info *, value);
extern value CoqdZArithdBinIntDefdZdof_nat_known_113(struct thread_info *, value);
extern value CoqdZArithdBinIntDefdZdmul_uncurried_known_112(struct thread_info *, value, value);
extern value add_carry_uncurried_known_111(struct thread_info *, value, value);
extern value add_uncurried_known_110(struct thread_info *, value, value);
extern value mul_uncurried_known_109(struct thread_info *, value, value);
extern value succ_known_108(struct thread_info *, value);
extern value string_of_uint_known_107(struct thread_info *, value);
extern value revapp_uncurried_known_106(struct thread_info *, value, value);
extern value succ_double_known_105(struct thread_info *, value);
extern value double_known_104(struct thread_info *, value);
extern value succ_double_known_103(struct thread_info *, value);
extern value double_known_102(struct thread_info *, value);
extern value to_little_uint_known_101(struct thread_info *, value);
extern value body(struct thread_info *);
value append_uncurried_known_127(struct thread_info *, value, value);
value f_case_known_126(struct thread_info *, value);
value is_eq_uncurried_known_125(struct thread_info *, value, value);
value y_wrapper_124(struct thread_info *, value, value);
value y_wrapper_123(struct thread_info *, value, value);
value f_case_known_122(struct thread_info *, value, value);
value f_case_known_121(struct thread_info *, value, value);
value f_case_known_120(struct thread_info *, value);
value memo_get_uncurried_known_119(struct thread_info *, value, value);
value y_wrapper_118(struct thread_info *, value, value);
value y_wrapper_117(struct thread_info *, value, value);
value f_case_known_116(struct thread_info *, value);
value tfact_known_115(struct thread_info *, value);
value of_succ_nat_known_114(struct thread_info *, value);
value CoqdZArithdBinIntDefdZdof_nat_known_113(struct thread_info *, value);
value CoqdZArithdBinIntDefdZdmul_uncurried_known_112(struct thread_info *, value, value);
value add_carry_uncurried_known_111(struct thread_info *, value, value);
value add_uncurried_known_110(struct thread_info *, value, value);
value mul_uncurried_known_109(struct thread_info *, value, value);
value succ_known_108(struct thread_info *, value);
value string_of_uint_known_107(struct thread_info *, value);
value revapp_uncurried_known_106(struct thread_info *, value, value);
value succ_double_known_105(struct thread_info *, value);
value double_known_104(struct thread_info *, value);
value succ_double_known_103(struct thread_info *, value);
value double_known_102(struct thread_info *, value);
value to_little_uint_known_101(struct thread_info *, value);
value body(struct thread_info *);
unsigned long long const body_info_717[2] = { 0LL, 0LL, };

unsigned long long const to_little_uint_known_info_716[3] = { 2LL, 1LL, 0LL,
  };

unsigned long long const double_known_info_715[3] = { 0LL, 1LL, 0LL, };

unsigned long long const succ_double_known_info_714[3] = { 2LL, 1LL, 0LL, };

unsigned long long const double_known_info_713[3] = { 0LL, 1LL, 0LL, };

unsigned long long const succ_double_known_info_712[3] = { 2LL, 1LL, 0LL, };

unsigned long long const revapp_uncurried_known_info_711[4] = { 2LL, 2LL,
  0LL, 1LL, };

unsigned long long const string_of_uint_known_info_710[3] = { 0LL, 1LL, 0LL,
  };

unsigned long long const succ_known_info_709[3] = { 2LL, 1LL, 0LL, };

unsigned long long const mul_uncurried_known_info_708[4] = { 0LL, 2LL, 0LL,
  1LL, };

unsigned long long const add_uncurried_known_info_707[4] = { 2LL, 2LL, 0LL,
  1LL, };

unsigned long long const add_carry_uncurried_known_info_706[4] = { 2LL, 2LL,
  0LL, 1LL, };

unsigned long long const CoqdZArithdBinIntDefdZdmul_uncurried_known_info_705[4] = {
  0LL, 2LL, 0LL, 1LL, };

unsigned long long const CoqdZArithdBinIntDefdZdof_nat_known_info_704[3] = {
  0LL, 1LL, 0LL, };

unsigned long long const of_succ_nat_known_info_703[3] = { 0LL, 1LL, 0LL, };

unsigned long long const tfact_known_info_702[3] = { 2LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_701[3] = { 4LL, 1LL, 0LL, };

unsigned long long const y_wrapper_info_700[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const y_wrapper_info_699[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const memo_get_uncurried_known_info_698[4] = { 0LL, 2LL,
  0LL, 1LL, };

unsigned long long const f_case_known_info_697[3] = { 0LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_696[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const f_case_known_info_695[4] = { 5LL, 2LL, 0LL, 1LL, };

unsigned long long const y_wrapper_info_694[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const y_wrapper_info_693[4] = { 2LL, 2LL, 0LL, 1LL, };

unsigned long long const is_eq_uncurried_known_info_692[4] = { 2LL, 2LL, 0LL,
  1LL, };

unsigned long long const f_case_known_info_691[3] = { 3LL, 1LL, 0LL, };

unsigned long long const append_uncurried_known_info_690[4] = { 0LL, 2LL,
  0LL, 1LL, };

value append_uncurried_known_127(struct thread_info *$tinfo, value $y_525, value $x_526)
{
  struct stack_frame frame;
  value root[2];
  register value $x_527;
  register value $xs_528;
  register value $y_529;
  register value $y_530;
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
  if (($x_526 & 1) == 0) {
    switch (*((value *) $x_526 + -1LL) & 255LL) {
      default:
        $x_527 = *((value *) $x_526 + 0LL);
        $xs_528 = *((value *) $x_526 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $x_527;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_529 =
          ((value (*)(struct thread_info *, value, value)) append_uncurried_known_127)
          ($tinfo, $y_525, $xs_528);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_529;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_529 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_527 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_530 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_530 + -1LL) = 2048LL;
        *((value *) $y_530 + 0LL) = $x_527;
        *((value *) $y_530 + 1LL) = $y_529;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_530;
        break;
      
    }
  } else {
    switch ($x_526 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_525;
        break;
      
    }
  }
}

value f_case_known_126(struct thread_info *$tinfo, value $s_509)
{
  struct stack_frame frame;
  value root[1];
  register value $y_510;
  register value $y_511;
  register value $y_512;
  register value $p_513;
  register value $y_514;
  register value $y_515;
  register value $y_516;
  register value $p_517;
  register value $y_518;
  register value $y_519;
  register value $y_520;
  register value $y_521;
  register value $y_522;
  register value $y_523;
  register value $y_524;
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
  if (!(3LL <= $limit - $alloc)) {
    *(root + 0LL) = $s_509;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 3LL;
    garbage_collect($tinfo);
    $s_509 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($s_509 & 1) == 0) {
    switch (*((value *) $s_509 + -1LL) & 255LL) {
      case 0:
        $p_513 = *((value *) $s_509 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_514 =
          ((value (*)(struct thread_info *, value)) to_little_uint_known_101)
          ($tinfo, $p_513);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $y_515 = 1LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_516 =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_515, $y_514);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $y_516);
        return $result;
        break;
      default:
        $p_517 = *((value *) $s_509 + 0LL);
        $y_518 = 91LL;
        $y_519 = 1LL;
        $y_520 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_520 + -1LL) = 2048LL;
        *((value *) $y_520 + 0LL) = $y_518;
        *((value *) $y_520 + 1LL) = $y_519;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_520;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_521 =
          ((value (*)(struct thread_info *, value)) to_little_uint_known_101)
          ($tinfo, $p_517);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_520 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_522 = 1LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_520;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_523 =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_522, $y_521);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_520 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_520;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_524 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $y_523);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_520 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) append_uncurried_known_127)
          ($tinfo, $y_524, $y_520);
        return $result;
        break;
      
    }
  } else {
    switch ($s_509 >> 1LL) {
      default:
        $y_510 = 97LL;
        $y_511 = 1LL;
        $y_512 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_512 + -1LL) = 2048LL;
        *((value *) $y_512 + 0LL) = $y_510;
        *((value *) $y_512 + 1LL) = $y_511;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_512;
        break;
      
    }
  }
}

value is_eq_uncurried_known_125(struct thread_info *$tinfo, value $m_494, value $n_495)
{
  struct stack_frame frame;
  value root[2];
  register value $y_496;
  register value $y_497;
  register value $y_498;
  register value $y_499;
  register value $n1_500;
  register value $y_501;
  register value $y_502;
  register value $m1_503;
  register value $y_504;
  register value $y_505;
  register value $y_506;
  register value $y_507;
  register value $y_508;
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
    *(root + 1LL) = $n_495;
    *(root + 0LL) = $m_494;
    frame.next = root + 2LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $n_495 = *(root + 1LL);
    $m_494 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($n_495 & 1) == 0) {
    switch (*((value *) $n_495 + -1LL) & 255LL) {
      default:
        $n1_500 = *((value *) $n_495 + 0LL);
        if (($m_494 & 1) == 0) {
          switch (*((value *) $m_494 + -1LL) & 255LL) {
            default:
              $m1_503 = *((value *) $m_494 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_504 =
                ((value (*)(struct thread_info *, value, value)) is_eq_uncurried_known_125)
                ($tinfo, $m1_503, $n1_500);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_504;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_504 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              if (($y_504 & 1) == 0) {
                switch (*((value *) $y_504 + -1LL) & 255LL) {
                  case 0:
                    $y_505 = 1LL;
                    $y_506 = (value) ($alloc + 1LL);
                    $alloc = $alloc + 2LL;
                    *((value *) $y_506 + -1LL) = 1024LL;
                    *((value *) $y_506 + 0LL) = $y_505;
                    (*$tinfo).alloc = $alloc;
                    (*$tinfo).limit = $limit;
                    return $y_506;
                    break;
                  default:
                    $y_507 = 1LL;
                    $y_508 = (value) ($alloc + 1LL);
                    $alloc = $alloc + 2LL;
                    *((value *) $y_508 + -1LL) = 1025LL;
                    *((value *) $y_508 + 0LL) = $y_507;
                    (*$tinfo).alloc = $alloc;
                    (*$tinfo).limit = $limit;
                    return $y_508;
                    break;
                  
                }
              } else {
                switch ($y_504 >> 1LL) {
                  
                }
              }
              break;
            
          }
        } else {
          switch ($m_494 >> 1LL) {
            default:
              $y_501 = 1LL;
              $y_502 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_502 + -1LL) = 1025LL;
              *((value *) $y_502 + 0LL) = $y_501;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_502;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($n_495 >> 1LL) {
      default:
        if (($m_494 & 1) == 0) {
          switch (*((value *) $m_494 + -1LL) & 255LL) {
            default:
              $y_498 = 1LL;
              $y_499 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_499 + -1LL) = 1025LL;
              *((value *) $y_499 + 0LL) = $y_498;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_499;
              break;
            
          }
        } else {
          switch ($m_494 >> 1LL) {
            default:
              $y_496 = 1LL;
              $y_497 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_497 + -1LL) = 1024LL;
              *((value *) $y_497 + 0LL) = $y_496;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_497;
              break;
            
          }
        }
        break;
      
    }
  }
}

value y_wrapper_124(struct thread_info *$tinfo, value $env_486, value $anon_487)
{
  struct stack_frame frame;
  value root[1];
  register value $y_proj_488;
  register value $y_489;
  register value $y_490;
  register value $n1_491;
  register value $y_492;
  register value $y_493;
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
    *(root + 0LL) = $env_486;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $env_486 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_proj_488 = *((value *) $env_486 + 0LL);
  if (($y_proj_488 & 1) == 0) {
    switch (*((value *) $y_proj_488 + -1LL) & 255LL) {
      default:
        $n1_491 = *((value *) $y_proj_488 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $n1_491;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_492 =
          ((value (*)(struct thread_info *, value)) CoqdZArithdBinIntDefdZdof_nat_known_113)
          ($tinfo, $y_proj_488);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n1_491 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_492;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_493 =
          ((value (*)(struct thread_info *, value)) tfact_known_115)
          ($tinfo, $n1_491);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_492 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) CoqdZArithdBinIntDefdZdmul_uncurried_known_112)
          ($tinfo, $y_493, $y_492);
        return $result;
        break;
      
    }
  } else {
    switch ($y_proj_488 >> 1LL) {
      default:
        $y_489 = 1LL;
        $y_490 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_490 + -1LL) = 1024LL;
        *((value *) $y_490 + 0LL) = $y_489;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_490;
        break;
      
    }
  }
}

value y_wrapper_123(struct thread_info *$tinfo, value $env_484, value $v1_485)
{
  struct stack_frame frame;
  value root[1];
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
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $v1_485;
}

value f_case_known_122(struct thread_info *$tinfo, value $s_478, value $y_479)
{
  struct stack_frame frame;
  value root[2];
  register value $env_480;
  register value $y_wrapper_clo_481;
  register value $env_482;
  register value $y_wrapper_clo_483;
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
    *(root + 1LL) = $y_479;
    *(root + 0LL) = $s_478;
    frame.next = root + 2LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 5LL;
    garbage_collect($tinfo);
    $y_479 = *(root + 1LL);
    $s_478 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($s_478 & 1) == 0) {
    switch (*((value *) $s_478 + -1LL) & 255LL) {
      case 0:
        $env_480 = 1LL;
        $y_wrapper_clo_481 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_wrapper_clo_481 + -1LL) = 2048LL;
        *((value *) $y_wrapper_clo_481 + 0LL) = y_wrapper_123;
        *((value *) $y_wrapper_clo_481 + 1LL) = $env_480;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_wrapper_clo_481;
        break;
      default:
        $env_482 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $env_482 + -1LL) = 1024LL;
        *((value *) $env_482 + 0LL) = $y_479;
        $y_wrapper_clo_483 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_wrapper_clo_483 + -1LL) = 2048LL;
        *((value *) $y_wrapper_clo_483 + 0LL) = y_wrapper_124;
        *((value *) $y_wrapper_clo_483 + 1LL) = $env_482;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_wrapper_clo_483;
        break;
      
    }
  } else {
    switch ($s_478 >> 1LL) {
      
    }
  }
}

value f_case_known_121(struct thread_info *$tinfo, value $s_470, value $y_471)
{
  struct stack_frame frame;
  value root[2];
  register value $m_472;
  register value $x_473;
  register value $y_474;
  register value $y_475;
  register value $y_code_476;
  register value $y_env_477;
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
  if (($s_470 & 1) == 0) {
    switch (*((value *) $s_470 + -1LL) & 255LL) {
      default:
        $m_472 = *((value *) $s_470 + 0LL);
        $x_473 = *((value *) $s_470 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $x_473;
        *(root + 0LL) = $y_471;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_474 =
          ((value (*)(struct thread_info *, value, value)) is_eq_uncurried_known_125)
          ($tinfo, $m_472, $y_471);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $x_473 = *(root + 1LL);
        $y_471 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $x_473;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_475 =
          ((value (*)(struct thread_info *, value, value)) f_case_known_122)
          ($tinfo, $y_474, $y_471);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $x_473 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_code_476 = *((value *) $y_475 + 0LL);
        $y_env_477 = *((value *) $y_475 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) $y_code_476)
          ($tinfo, $y_env_477, $x_473);
        return $result;
        break;
      
    }
  } else {
    switch ($s_470 >> 1LL) {
      
    }
  }
}

value f_case_known_120(struct thread_info *$tinfo, value $s_468)
{
  struct stack_frame frame;
  value root[1];
  register value $s_469;
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
  if (($s_468 & 1) == 0) {
    switch (*((value *) $s_468 + -1LL) & 255LL) {
      default:
        $s_469 = *((value *) $s_468 + 1LL);
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $s_469;
        break;
      
    }
  } else {
    switch ($s_468 >> 1LL) {
      
    }
  }
}

value memo_get_uncurried_known_119(struct thread_info *$tinfo, value $l_455, value $n_456)
{
  struct stack_frame frame;
  value root[2];
  register value $y_457;
  register value $l_code_458;
  register value $l_env_459;
  register value $y_460;
  register value $a_461;
  register value $n1_462;
  register value $y_463;
  register value $l_code_464;
  register value $l_env_465;
  register value $y_466;
  register value $y_467;
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
  if (($n_456 & 1) == 0) {
    switch (*((value *) $n_456 + -1LL) & 255LL) {
      default:
        $n1_462 = *((value *) $n_456 + 0LL);
        $y_463 = 1LL;
        $l_code_464 = *((value *) $l_455 + 0LL);
        $l_env_465 = *((value *) $l_455 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $n1_462;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_466 =
          ((value (*)(struct thread_info *, value, value)) $l_code_464)
          ($tinfo, $l_env_465, $y_463);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n1_462 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $n1_462;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_467 =
          ((value (*)(struct thread_info *, value)) f_case_known_120)
          ($tinfo, $y_466);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n1_462 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) memo_get_uncurried_known_119)
          ($tinfo, $y_467, $n1_462);
        return $result;
        break;
      
    }
  } else {
    switch ($n_456 >> 1LL) {
      default:
        $y_457 = 1LL;
        $l_code_458 = *((value *) $l_455 + 0LL);
        $l_env_459 = *((value *) $l_455 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_460 =
          ((value (*)(struct thread_info *, value, value)) $l_code_458)
          ($tinfo, $l_env_459, $y_457);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        if (($y_460 & 1) == 0) {
          switch (*((value *) $y_460 + -1LL) & 255LL) {
            default:
              $a_461 = *((value *) $y_460 + 0LL);
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $a_461;
              break;
            
          }
        } else {
          switch ($y_460 >> 1LL) {
            
          }
        }
        break;
      
    }
  }
}

value y_wrapper_118(struct thread_info *$tinfo, value $env_448, value $anon_449)
{
  struct stack_frame frame;
  value root[2];
  register value $y_proj_450;
  register value $fn1_451;
  register value $env_452;
  register value $y_wrapper_clo_453;
  register value $y_454;
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
  $y_proj_450 = *((value *) $env_448 + 0LL);
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $y_proj_450;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $fn1_451 =
    ((value (*)(struct thread_info *, value)) f_case_known_116)
    ($tinfo, $y_proj_450);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(8LL <= $limit - $alloc)) {
    *(root + 1LL) = $fn1_451;
    frame.next = root + 2LL;
    (*$tinfo).nalloc = 8LL;
    garbage_collect($tinfo);
    $fn1_451 = *(root + 1LL);
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_proj_450 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $env_452 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $env_452 + -1LL) = 1024LL;
  *((value *) $env_452 + 0LL) = $fn1_451;
  $y_wrapper_clo_453 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_wrapper_clo_453 + -1LL) = 2048LL;
  *((value *) $y_wrapper_clo_453 + 0LL) = y_wrapper_117;
  *((value *) $y_wrapper_clo_453 + 1LL) = $env_452;
  $y_454 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_454 + -1LL) = 2048LL;
  *((value *) $y_454 + 0LL) = $y_proj_450;
  *((value *) $y_454 + 1LL) = $y_wrapper_clo_453;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $y_454;
}

value y_wrapper_117(struct thread_info *$tinfo, value $env_441, value $anon_442)
{
  struct stack_frame frame;
  value root[2];
  register value $fn1_proj_443;
  register value $fn1_444;
  register value $env_445;
  register value $y_wrapper_clo_446;
  register value $y_447;
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
  $fn1_proj_443 = *((value *) $env_441 + 0LL);
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $fn1_proj_443;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $fn1_444 =
    ((value (*)(struct thread_info *, value)) f_case_known_116)
    ($tinfo, $fn1_proj_443);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(8LL <= $limit - $alloc)) {
    *(root + 1LL) = $fn1_444;
    frame.next = root + 2LL;
    (*$tinfo).nalloc = 8LL;
    garbage_collect($tinfo);
    $fn1_444 = *(root + 1LL);
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $fn1_proj_443 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $env_445 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $env_445 + -1LL) = 1024LL;
  *((value *) $env_445 + 0LL) = $fn1_444;
  $y_wrapper_clo_446 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_wrapper_clo_446 + -1LL) = 2048LL;
  *((value *) $y_wrapper_clo_446 + 0LL) = y_wrapper_117;
  *((value *) $y_wrapper_clo_446 + 1LL) = $env_445;
  $y_447 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_447 + -1LL) = 2048LL;
  *((value *) $y_447 + 0LL) = $fn1_proj_443;
  *((value *) $y_447 + 1LL) = $y_wrapper_clo_446;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $y_447;
}

value f_case_known_116(struct thread_info *$tinfo, value $s_433)
{
  struct stack_frame frame;
  value root[2];
  register value $n1_434;
  register value $v1_435;
  register value $y_436;
  register value $y_437;
  register value $y_438;
  register value $y_439;
  register value $y_440;
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
  if (!(4LL <= $limit - $alloc)) {
    *(root + 0LL) = $s_433;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 4LL;
    garbage_collect($tinfo);
    $s_433 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($s_433 & 1) == 0) {
    switch (*((value *) $s_433 + -1LL) & 255LL) {
      default:
        $n1_434 = *((value *) $s_433 + 0LL);
        $v1_435 = *((value *) $s_433 + 1LL);
        $y_436 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_436 + -1LL) = 1024LL;
        *((value *) $y_436 + 0LL) = $n1_434;
        $y_437 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_437 + -1LL) = 1024LL;
        *((value *) $y_437 + 0LL) = $n1_434;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $y_436;
        *(root + 0LL) = $v1_435;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_438 =
          ((value (*)(struct thread_info *, value)) CoqdZArithdBinIntDefdZdof_nat_known_113)
          ($tinfo, $y_437);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_436 = *(root + 1LL);
        $v1_435 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_436;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_439 =
          ((value (*)(struct thread_info *, value, value)) CoqdZArithdBinIntDefdZdmul_uncurried_known_112)
          ($tinfo, $v1_435, $y_438);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_439;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_439 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_436 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_440 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_440 + -1LL) = 2048LL;
        *((value *) $y_440 + 0LL) = $y_436;
        *((value *) $y_440 + 1LL) = $y_439;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_440;
        break;
      
    }
  } else {
    switch ($s_433 >> 1LL) {
      
    }
  }
}

value tfact_known_115(struct thread_info *$tinfo, value $n_427)
{
  struct stack_frame frame;
  value root[1];
  register value $y_428;
  register value $y_429;
  register value $n1_430;
  register value $y_431;
  register value $y_432;
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
    *(root + 0LL) = $n_427;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $n_427 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($n_427 & 1) == 0) {
    switch (*((value *) $n_427 + -1LL) & 255LL) {
      default:
        $n1_430 = *((value *) $n_427 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $n1_430;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_431 =
          ((value (*)(struct thread_info *, value)) CoqdZArithdBinIntDefdZdof_nat_known_113)
          ($tinfo, $n_427);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $n1_430 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_431;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_432 =
          ((value (*)(struct thread_info *, value)) tfact_known_115)
          ($tinfo, $n1_430);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $y_431 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) CoqdZArithdBinIntDefdZdmul_uncurried_known_112)
          ($tinfo, $y_432, $y_431);
        return $result;
        break;
      
    }
  } else {
    switch ($n_427 >> 1LL) {
      default:
        $y_428 = 1LL;
        $y_429 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_429 + -1LL) = 1024LL;
        *((value *) $y_429 + 0LL) = $y_428;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_429;
        break;
      
    }
  }
}

value of_succ_nat_known_114(struct thread_info *$tinfo, value $n_423)
{
  struct stack_frame frame;
  value root[1];
  register value $y_424;
  register value $x_425;
  register value $y_426;
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
  if (($n_423 & 1) == 0) {
    switch (*((value *) $n_423 + -1LL) & 255LL) {
      default:
        $x_425 = *((value *) $n_423 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_426 =
          ((value (*)(struct thread_info *, value)) of_succ_nat_known_114)
          ($tinfo, $x_425);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value)) succ_known_108)
          ($tinfo, $y_426);
        return $result;
        break;
      
    }
  } else {
    switch ($n_423 >> 1LL) {
      default:
        $y_424 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_424;
        break;
      
    }
  }
}

value CoqdZArithdBinIntDefdZdof_nat_known_113(struct thread_info *$tinfo, value $n_418)
{
  struct stack_frame frame;
  value root[1];
  register value $y_419;
  register value $n_420;
  register value $y_421;
  register value $y_422;
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
  if (($n_418 & 1) == 0) {
    switch (*((value *) $n_418 + -1LL) & 255LL) {
      default:
        $n_420 = *((value *) $n_418 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_421 =
          ((value (*)(struct thread_info *, value)) of_succ_nat_known_114)
          ($tinfo, $n_420);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_421;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_421 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_422 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_422 + -1LL) = 1024LL;
        *((value *) $y_422 + 0LL) = $y_421;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_422;
        break;
      
    }
  } else {
    switch ($n_418 >> 1LL) {
      default:
        $y_419 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_419;
        break;
      
    }
  }
}

value CoqdZArithdBinIntDefdZdmul_uncurried_known_112(struct thread_info *$tinfo, value $y_399, value $x_400)
{
  struct stack_frame frame;
  value root[2];
  register value $y_401;
  register value $xp_402;
  register value $y_403;
  register value $yp_404;
  register value $y_405;
  register value $y_406;
  register value $yp_407;
  register value $y_408;
  register value $y_409;
  register value $xp_410;
  register value $y_411;
  register value $yp_412;
  register value $y_413;
  register value $y_414;
  register value $yp_415;
  register value $y_416;
  register value $y_417;
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
  if (($x_400 & 1) == 0) {
    switch (*((value *) $x_400 + -1LL) & 255LL) {
      case 0:
        $xp_402 = *((value *) $x_400 + 0LL);
        if (($y_399 & 1) == 0) {
          switch (*((value *) $y_399 + -1LL) & 255LL) {
            case 0:
              $yp_404 = *((value *) $y_399 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_405 =
                ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
                ($tinfo, $yp_404, $xp_402);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_405;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_405 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_406 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_406 + -1LL) = 1024LL;
              *((value *) $y_406 + 0LL) = $y_405;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_406;
              break;
            default:
              $yp_407 = *((value *) $y_399 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_408 =
                ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
                ($tinfo, $yp_407, $xp_402);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_408;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_408 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_409 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_409 + -1LL) = 1025LL;
              *((value *) $y_409 + 0LL) = $y_408;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_409;
              break;
            
          }
        } else {
          switch ($y_399 >> 1LL) {
            default:
              $y_403 = 1LL;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_403;
              break;
            
          }
        }
        break;
      default:
        $xp_410 = *((value *) $x_400 + 0LL);
        if (($y_399 & 1) == 0) {
          switch (*((value *) $y_399 + -1LL) & 255LL) {
            case 0:
              $yp_412 = *((value *) $y_399 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_413 =
                ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
                ($tinfo, $yp_412, $xp_410);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_413;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_413 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_414 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_414 + -1LL) = 1025LL;
              *((value *) $y_414 + 0LL) = $y_413;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_414;
              break;
            default:
              $yp_415 = *((value *) $y_399 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_416 =
                ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
                ($tinfo, $yp_415, $xp_410);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_416;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_416 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_417 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_417 + -1LL) = 1024LL;
              *((value *) $y_417 + 0LL) = $y_416;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_417;
              break;
            
          }
        } else {
          switch ($y_399 >> 1LL) {
            default:
              $y_411 = 1LL;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_411;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($x_400 >> 1LL) {
      default:
        $y_401 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_401;
        break;
      
    }
  }
}

value add_carry_uncurried_known_111(struct thread_info *$tinfo, value $y_371, value $x_372)
{
  struct stack_frame frame;
  value root[2];
  register value $p_373;
  register value $q_374;
  register value $y_375;
  register value $y_376;
  register value $q_377;
  register value $y_378;
  register value $y_379;
  register value $y_380;
  register value $y_381;
  register value $p_382;
  register value $q_383;
  register value $y_384;
  register value $y_385;
  register value $q_386;
  register value $y_387;
  register value $y_388;
  register value $y_389;
  register value $y_390;
  register value $q_391;
  register value $y_392;
  register value $y_393;
  register value $q_394;
  register value $y_395;
  register value $y_396;
  register value $y_397;
  register value $y_398;
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
    *(root + 1LL) = $x_372;
    *(root + 0LL) = $y_371;
    frame.next = root + 2LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $x_372 = *(root + 1LL);
    $y_371 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_372 & 1) == 0) {
    switch (*((value *) $x_372 + -1LL) & 255LL) {
      case 0:
        $p_373 = *((value *) $x_372 + 0LL);
        if (($y_371 & 1) == 0) {
          switch (*((value *) $y_371 + -1LL) & 255LL) {
            case 0:
              $q_374 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_375 =
                ((value (*)(struct thread_info *, value, value)) add_carry_uncurried_known_111)
                ($tinfo, $q_374, $p_373);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_375;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_375 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_376 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_376 + -1LL) = 1024LL;
              *((value *) $y_376 + 0LL) = $y_375;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_376;
              break;
            default:
              $q_377 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_378 =
                ((value (*)(struct thread_info *, value, value)) add_carry_uncurried_known_111)
                ($tinfo, $q_377, $p_373);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_378;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_378 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_379 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_379 + -1LL) = 1025LL;
              *((value *) $y_379 + 0LL) = $y_378;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_379;
              break;
            
          }
        } else {
          switch ($y_371 >> 1LL) {
            default:
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_380 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $p_373);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_380;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_380 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_381 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_381 + -1LL) = 1024LL;
              *((value *) $y_381 + 0LL) = $y_380;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_381;
              break;
            
          }
        }
        break;
      default:
        $p_382 = *((value *) $x_372 + 0LL);
        if (($y_371 & 1) == 0) {
          switch (*((value *) $y_371 + -1LL) & 255LL) {
            case 0:
              $q_383 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_384 =
                ((value (*)(struct thread_info *, value, value)) add_carry_uncurried_known_111)
                ($tinfo, $q_383, $p_382);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_384;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_384 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_385 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_385 + -1LL) = 1025LL;
              *((value *) $y_385 + 0LL) = $y_384;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_385;
              break;
            default:
              $q_386 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_387 =
                ((value (*)(struct thread_info *, value, value)) add_uncurried_known_110)
                ($tinfo, $q_386, $p_382);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_387;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_387 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_388 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_388 + -1LL) = 1024LL;
              *((value *) $y_388 + 0LL) = $y_387;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_388;
              break;
            
          }
        } else {
          switch ($y_371 >> 1LL) {
            default:
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_389 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $p_382);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_389;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_389 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_390 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_390 + -1LL) = 1025LL;
              *((value *) $y_390 + 0LL) = $y_389;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_390;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($x_372 >> 1LL) {
      default:
        if (($y_371 & 1) == 0) {
          switch (*((value *) $y_371 + -1LL) & 255LL) {
            case 0:
              $q_391 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_392 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $q_391);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_392;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_392 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_393 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_393 + -1LL) = 1024LL;
              *((value *) $y_393 + 0LL) = $y_392;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_393;
              break;
            default:
              $q_394 = *((value *) $y_371 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_395 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $q_394);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_395;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_395 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_396 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_396 + -1LL) = 1025LL;
              *((value *) $y_396 + 0LL) = $y_395;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_396;
              break;
            
          }
        } else {
          switch ($y_371 >> 1LL) {
            default:
              $y_397 = 1LL;
              $y_398 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_398 + -1LL) = 1024LL;
              *((value *) $y_398 + 0LL) = $y_397;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_398;
              break;
            
          }
        }
        break;
      
    }
  }
}

value add_uncurried_known_110(struct thread_info *$tinfo, value $y_345, value $x_346)
{
  struct stack_frame frame;
  value root[2];
  register value $p_347;
  register value $q_348;
  register value $y_349;
  register value $y_350;
  register value $q_351;
  register value $y_352;
  register value $y_353;
  register value $y_354;
  register value $y_355;
  register value $p_356;
  register value $q_357;
  register value $y_358;
  register value $y_359;
  register value $q_360;
  register value $y_361;
  register value $y_362;
  register value $y_363;
  register value $q_364;
  register value $y_365;
  register value $y_366;
  register value $q_367;
  register value $y_368;
  register value $y_369;
  register value $y_370;
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
    *(root + 1LL) = $x_346;
    *(root + 0LL) = $y_345;
    frame.next = root + 2LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $x_346 = *(root + 1LL);
    $y_345 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_346 & 1) == 0) {
    switch (*((value *) $x_346 + -1LL) & 255LL) {
      case 0:
        $p_347 = *((value *) $x_346 + 0LL);
        if (($y_345 & 1) == 0) {
          switch (*((value *) $y_345 + -1LL) & 255LL) {
            case 0:
              $q_348 = *((value *) $y_345 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_349 =
                ((value (*)(struct thread_info *, value, value)) add_carry_uncurried_known_111)
                ($tinfo, $q_348, $p_347);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_349;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_349 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_350 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_350 + -1LL) = 1025LL;
              *((value *) $y_350 + 0LL) = $y_349;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_350;
              break;
            default:
              $q_351 = *((value *) $y_345 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_352 =
                ((value (*)(struct thread_info *, value, value)) add_uncurried_known_110)
                ($tinfo, $q_351, $p_347);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_352;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_352 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_353 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_353 + -1LL) = 1024LL;
              *((value *) $y_353 + 0LL) = $y_352;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_353;
              break;
            
          }
        } else {
          switch ($y_345 >> 1LL) {
            default:
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_354 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $p_347);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_354;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_354 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_355 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_355 + -1LL) = 1025LL;
              *((value *) $y_355 + 0LL) = $y_354;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_355;
              break;
            
          }
        }
        break;
      default:
        $p_356 = *((value *) $x_346 + 0LL);
        if (($y_345 & 1) == 0) {
          switch (*((value *) $y_345 + -1LL) & 255LL) {
            case 0:
              $q_357 = *((value *) $y_345 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_358 =
                ((value (*)(struct thread_info *, value, value)) add_uncurried_known_110)
                ($tinfo, $q_357, $p_356);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_358;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_358 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_359 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_359 + -1LL) = 1024LL;
              *((value *) $y_359 + 0LL) = $y_358;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_359;
              break;
            default:
              $q_360 = *((value *) $y_345 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_361 =
                ((value (*)(struct thread_info *, value, value)) add_uncurried_known_110)
                ($tinfo, $q_360, $p_356);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_361;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_361 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_362 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_362 + -1LL) = 1025LL;
              *((value *) $y_362 + 0LL) = $y_361;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_362;
              break;
            
          }
        } else {
          switch ($y_345 >> 1LL) {
            default:
              $y_363 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_363 + -1LL) = 1024LL;
              *((value *) $y_363 + 0LL) = $p_356;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_363;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($x_346 >> 1LL) {
      default:
        if (($y_345 & 1) == 0) {
          switch (*((value *) $y_345 + -1LL) & 255LL) {
            case 0:
              $q_364 = *((value *) $y_345 + 0LL);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              /*skip*/;
              $y_365 =
                ((value (*)(struct thread_info *, value)) succ_known_108)
                ($tinfo, $q_364);
              $alloc = (*$tinfo).alloc;
              $limit = (*$tinfo).limit;
              if (!(2LL <= $limit - $alloc)) {
                *(root + 0LL) = $y_365;
                frame.next = root + 1LL;
                (*$tinfo).fp = &frame;
                (*$tinfo).nalloc = 2LL;
                garbage_collect($tinfo);
                $y_365 = *(root + 0LL);
                (*$tinfo).fp = frame.prev;
                $alloc = (*$tinfo).alloc;
                $limit = (*$tinfo).limit;
              }
              /*skip*/;
              $y_366 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_366 + -1LL) = 1025LL;
              *((value *) $y_366 + 0LL) = $y_365;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_366;
              break;
            default:
              $q_367 = *((value *) $y_345 + 0LL);
              $y_368 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_368 + -1LL) = 1024LL;
              *((value *) $y_368 + 0LL) = $q_367;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_368;
              break;
            
          }
        } else {
          switch ($y_345 >> 1LL) {
            default:
              $y_369 = 1LL;
              $y_370 = (value) ($alloc + 1LL);
              $alloc = $alloc + 2LL;
              *((value *) $y_370 + -1LL) = 1025LL;
              *((value *) $y_370 + 0LL) = $y_369;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $y_370;
              break;
            
          }
        }
        break;
      
    }
  }
}

value mul_uncurried_known_109(struct thread_info *$tinfo, value $y_337, value $x_338)
{
  struct stack_frame frame;
  value root[2];
  register value $p_339;
  register value $y_340;
  register value $y_341;
  register value $p_342;
  register value $y_343;
  register value $y_344;
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
  if (($x_338 & 1) == 0) {
    switch (*((value *) $x_338 + -1LL) & 255LL) {
      case 0:
        $p_339 = *((value *) $x_338 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_337;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_340 =
          ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
          ($tinfo, $y_337, $p_339);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_340;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_340 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_337 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_341 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_341 + -1LL) = 1025LL;
        *((value *) $y_341 + 0LL) = $y_340;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) add_uncurried_known_110)
          ($tinfo, $y_341, $y_337);
        return $result;
        break;
      default:
        $p_342 = *((value *) $x_338 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_343 =
          ((value (*)(struct thread_info *, value, value)) mul_uncurried_known_109)
          ($tinfo, $y_337, $p_342);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_343;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_343 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_344 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_344 + -1LL) = 1025LL;
        *((value *) $y_344 + 0LL) = $y_343;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_344;
        break;
      
    }
  } else {
    switch ($x_338 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_337;
        break;
      
    }
  }
}

value succ_known_108(struct thread_info *$tinfo, value $x_329)
{
  struct stack_frame frame;
  value root[1];
  register value $p_330;
  register value $y_331;
  register value $y_332;
  register value $p_333;
  register value $y_334;
  register value $y_335;
  register value $y_336;
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
    *(root + 0LL) = $x_329;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $x_329 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($x_329 & 1) == 0) {
    switch (*((value *) $x_329 + -1LL) & 255LL) {
      case 0:
        $p_330 = *((value *) $x_329 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_331 =
          ((value (*)(struct thread_info *, value)) succ_known_108)
          ($tinfo, $p_330);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_331;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_331 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_332 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_332 + -1LL) = 1025LL;
        *((value *) $y_332 + 0LL) = $y_331;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_332;
        break;
      default:
        $p_333 = *((value *) $x_329 + 0LL);
        $y_334 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_334 + -1LL) = 1024LL;
        *((value *) $y_334 + 0LL) = $p_333;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_334;
        break;
      
    }
  } else {
    switch ($x_329 >> 1LL) {
      default:
        $y_335 = 1LL;
        $y_336 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_336 + -1LL) = 1025LL;
        *((value *) $y_336 + 0LL) = $y_335;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_336;
        break;
      
    }
  }
}

value string_of_uint_known_107(struct thread_info *$tinfo, value $n_287)
{
  struct stack_frame frame;
  value root[2];
  register value $y_288;
  register value $n_289;
  register value $y_290;
  register value $y_291;
  register value $y_292;
  register value $n_293;
  register value $y_294;
  register value $y_295;
  register value $y_296;
  register value $n_297;
  register value $y_298;
  register value $y_299;
  register value $y_300;
  register value $n_301;
  register value $y_302;
  register value $y_303;
  register value $y_304;
  register value $n_305;
  register value $y_306;
  register value $y_307;
  register value $y_308;
  register value $n_309;
  register value $y_310;
  register value $y_311;
  register value $y_312;
  register value $n_313;
  register value $y_314;
  register value $y_315;
  register value $y_316;
  register value $n_317;
  register value $y_318;
  register value $y_319;
  register value $y_320;
  register value $n_321;
  register value $y_322;
  register value $y_323;
  register value $y_324;
  register value $n_325;
  register value $y_326;
  register value $y_327;
  register value $y_328;
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
  if (($n_287 & 1) == 0) {
    switch (*((value *) $n_287 + -1LL) & 255LL) {
      case 0:
        $n_289 = *((value *) $n_287 + 0LL);
        $y_290 = 97LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_290;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_291 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_289);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_291;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_291 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_290 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_292 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_292 + -1LL) = 2048LL;
        *((value *) $y_292 + 0LL) = $y_290;
        *((value *) $y_292 + 1LL) = $y_291;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_292;
        break;
      case 1:
        $n_293 = *((value *) $n_287 + 0LL);
        $y_294 = 99LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_294;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_295 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_293);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_295;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_295 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_294 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_296 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_296 + -1LL) = 2048LL;
        *((value *) $y_296 + 0LL) = $y_294;
        *((value *) $y_296 + 1LL) = $y_295;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_296;
        break;
      case 2:
        $n_297 = *((value *) $n_287 + 0LL);
        $y_298 = 101LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_298;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_299 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_297);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_299;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_299 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_298 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_300 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_300 + -1LL) = 2048LL;
        *((value *) $y_300 + 0LL) = $y_298;
        *((value *) $y_300 + 1LL) = $y_299;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_300;
        break;
      case 3:
        $n_301 = *((value *) $n_287 + 0LL);
        $y_302 = 103LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_302;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_303 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_301);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_303;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_303 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_302 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_304 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_304 + -1LL) = 2048LL;
        *((value *) $y_304 + 0LL) = $y_302;
        *((value *) $y_304 + 1LL) = $y_303;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_304;
        break;
      case 4:
        $n_305 = *((value *) $n_287 + 0LL);
        $y_306 = 105LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_306;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_307 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_305);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_307;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_307 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_306 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_308 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_308 + -1LL) = 2048LL;
        *((value *) $y_308 + 0LL) = $y_306;
        *((value *) $y_308 + 1LL) = $y_307;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_308;
        break;
      case 5:
        $n_309 = *((value *) $n_287 + 0LL);
        $y_310 = 107LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_310;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_311 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_309);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_311;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_311 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_310 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_312 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_312 + -1LL) = 2048LL;
        *((value *) $y_312 + 0LL) = $y_310;
        *((value *) $y_312 + 1LL) = $y_311;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_312;
        break;
      case 6:
        $n_313 = *((value *) $n_287 + 0LL);
        $y_314 = 109LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_314;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_315 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_313);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_315;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_315 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_314 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_316 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_316 + -1LL) = 2048LL;
        *((value *) $y_316 + 0LL) = $y_314;
        *((value *) $y_316 + 1LL) = $y_315;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_316;
        break;
      case 7:
        $n_317 = *((value *) $n_287 + 0LL);
        $y_318 = 111LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_318;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_319 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_317);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_319;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_319 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_318 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_320 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_320 + -1LL) = 2048LL;
        *((value *) $y_320 + 0LL) = $y_318;
        *((value *) $y_320 + 1LL) = $y_319;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_320;
        break;
      case 8:
        $n_321 = *((value *) $n_287 + 0LL);
        $y_322 = 113LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_322;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_323 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_321);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_323;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_323 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_322 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_324 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_324 + -1LL) = 2048LL;
        *((value *) $y_324 + 0LL) = $y_322;
        *((value *) $y_324 + 1LL) = $y_323;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_324;
        break;
      default:
        $n_325 = *((value *) $n_287 + 0LL);
        $y_326 = 115LL;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_326;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_327 =
          ((value (*)(struct thread_info *, value)) string_of_uint_known_107)
          ($tinfo, $n_325);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_327;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_327 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_326 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_328 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_328 + -1LL) = 2048LL;
        *((value *) $y_328 + 0LL) = $y_326;
        *((value *) $y_328 + 1LL) = $y_327;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_328;
        break;
      
    }
  } else {
    switch ($n_287 >> 1LL) {
      default:
        $y_288 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_288;
        break;
      
    }
  }
}

value revapp_uncurried_known_106(struct thread_info *$tinfo, value $dp_265, value $d_266)
{
  struct stack_frame frame;
  value root[2];
  register value $d_267;
  register value $y_268;
  register value $d_269;
  register value $y_270;
  register value $d_271;
  register value $y_272;
  register value $d_273;
  register value $y_274;
  register value $d_275;
  register value $y_276;
  register value $d_277;
  register value $y_278;
  register value $d_279;
  register value $y_280;
  register value $d_281;
  register value $y_282;
  register value $d_283;
  register value $y_284;
  register value $d_285;
  register value $y_286;
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
    *(root + 1LL) = $d_266;
    *(root + 0LL) = $dp_265;
    frame.next = root + 2LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $d_266 = *(root + 1LL);
    $dp_265 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($d_266 & 1) == 0) {
    switch (*((value *) $d_266 + -1LL) & 255LL) {
      case 0:
        $d_267 = *((value *) $d_266 + 0LL);
        $y_268 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_268 + -1LL) = 1024LL;
        *((value *) $y_268 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_268, $d_267);
        return $result;
        break;
      case 1:
        $d_269 = *((value *) $d_266 + 0LL);
        $y_270 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_270 + -1LL) = 1025LL;
        *((value *) $y_270 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_270, $d_269);
        return $result;
        break;
      case 2:
        $d_271 = *((value *) $d_266 + 0LL);
        $y_272 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_272 + -1LL) = 1026LL;
        *((value *) $y_272 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_272, $d_271);
        return $result;
        break;
      case 3:
        $d_273 = *((value *) $d_266 + 0LL);
        $y_274 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_274 + -1LL) = 1027LL;
        *((value *) $y_274 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_274, $d_273);
        return $result;
        break;
      case 4:
        $d_275 = *((value *) $d_266 + 0LL);
        $y_276 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_276 + -1LL) = 1028LL;
        *((value *) $y_276 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_276, $d_275);
        return $result;
        break;
      case 5:
        $d_277 = *((value *) $d_266 + 0LL);
        $y_278 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_278 + -1LL) = 1029LL;
        *((value *) $y_278 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_278, $d_277);
        return $result;
        break;
      case 6:
        $d_279 = *((value *) $d_266 + 0LL);
        $y_280 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_280 + -1LL) = 1030LL;
        *((value *) $y_280 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_280, $d_279);
        return $result;
        break;
      case 7:
        $d_281 = *((value *) $d_266 + 0LL);
        $y_282 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_282 + -1LL) = 1031LL;
        *((value *) $y_282 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_282, $d_281);
        return $result;
        break;
      case 8:
        $d_283 = *((value *) $d_266 + 0LL);
        $y_284 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_284 + -1LL) = 1032LL;
        *((value *) $y_284 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_284, $d_283);
        return $result;
        break;
      default:
        $d_285 = *((value *) $d_266 + 0LL);
        $y_286 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_286 + -1LL) = 1033LL;
        *((value *) $y_286 + 0LL) = $dp_265;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value, value)) revapp_uncurried_known_106)
          ($tinfo, $y_286, $d_285);
        return $result;
        break;
      
    }
  } else {
    switch ($d_266 >> 1LL) {
      default:
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $dp_265;
        break;
      
    }
  }
}

value succ_double_known_105(struct thread_info *$tinfo, value $d_232)
{
  struct stack_frame frame;
  value root[1];
  register value $y_233;
  register value $y_234;
  register value $d_235;
  register value $y_236;
  register value $y_237;
  register value $d_238;
  register value $y_239;
  register value $y_240;
  register value $d_241;
  register value $y_242;
  register value $y_243;
  register value $d_244;
  register value $y_245;
  register value $y_246;
  register value $d_247;
  register value $y_248;
  register value $y_249;
  register value $d_250;
  register value $y_251;
  register value $y_252;
  register value $d_253;
  register value $y_254;
  register value $y_255;
  register value $d_256;
  register value $y_257;
  register value $y_258;
  register value $d_259;
  register value $y_260;
  register value $y_261;
  register value $d_262;
  register value $y_263;
  register value $y_264;
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
    *(root + 0LL) = $d_232;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $d_232 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($d_232 & 1) == 0) {
    switch (*((value *) $d_232 + -1LL) & 255LL) {
      case 0:
        $d_235 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_236 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_235);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_236;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_236 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_237 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_237 + -1LL) = 1025LL;
        *((value *) $y_237 + 0LL) = $y_236;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_237;
        break;
      case 1:
        $d_238 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_239 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_238);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_239;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_239 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_240 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_240 + -1LL) = 1027LL;
        *((value *) $y_240 + 0LL) = $y_239;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_240;
        break;
      case 2:
        $d_241 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_242 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_241);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_242;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_242 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_243 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_243 + -1LL) = 1029LL;
        *((value *) $y_243 + 0LL) = $y_242;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_243;
        break;
      case 3:
        $d_244 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_245 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_244);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_245;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_245 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_246 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_246 + -1LL) = 1031LL;
        *((value *) $y_246 + 0LL) = $y_245;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_246;
        break;
      case 4:
        $d_247 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_248 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_247);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_248;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_248 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_249 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_249 + -1LL) = 1033LL;
        *((value *) $y_249 + 0LL) = $y_248;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_249;
        break;
      case 5:
        $d_250 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_251 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_250);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_251;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_251 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_252 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_252 + -1LL) = 1025LL;
        *((value *) $y_252 + 0LL) = $y_251;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_252;
        break;
      case 6:
        $d_253 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_254 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_253);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_254;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_254 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_255 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_255 + -1LL) = 1027LL;
        *((value *) $y_255 + 0LL) = $y_254;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_255;
        break;
      case 7:
        $d_256 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_257 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_256);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_257;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_257 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_258 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_258 + -1LL) = 1029LL;
        *((value *) $y_258 + 0LL) = $y_257;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_258;
        break;
      case 8:
        $d_259 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_260 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_259);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_260;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_260 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_261 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_261 + -1LL) = 1031LL;
        *((value *) $y_261 + 0LL) = $y_260;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_261;
        break;
      default:
        $d_262 = *((value *) $d_232 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_263 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_262);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_263;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_263 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_264 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_264 + -1LL) = 1033LL;
        *((value *) $y_264 + 0LL) = $y_263;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_264;
        break;
      
    }
  } else {
    switch ($d_232 >> 1LL) {
      default:
        $y_233 = 1LL;
        $y_234 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_234 + -1LL) = 1025LL;
        *((value *) $y_234 + 0LL) = $y_233;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_234;
        break;
      
    }
  }
}

value double_known_104(struct thread_info *$tinfo, value $d_200)
{
  struct stack_frame frame;
  value root[1];
  register value $y_201;
  register value $d_202;
  register value $y_203;
  register value $y_204;
  register value $d_205;
  register value $y_206;
  register value $y_207;
  register value $d_208;
  register value $y_209;
  register value $y_210;
  register value $d_211;
  register value $y_212;
  register value $y_213;
  register value $d_214;
  register value $y_215;
  register value $y_216;
  register value $d_217;
  register value $y_218;
  register value $y_219;
  register value $d_220;
  register value $y_221;
  register value $y_222;
  register value $d_223;
  register value $y_224;
  register value $y_225;
  register value $d_226;
  register value $y_227;
  register value $y_228;
  register value $d_229;
  register value $y_230;
  register value $y_231;
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
  if (($d_200 & 1) == 0) {
    switch (*((value *) $d_200 + -1LL) & 255LL) {
      case 0:
        $d_202 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_203 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_202);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_203;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_203 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_204 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_204 + -1LL) = 1024LL;
        *((value *) $y_204 + 0LL) = $y_203;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_204;
        break;
      case 1:
        $d_205 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_206 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_205);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_206;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_206 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_207 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_207 + -1LL) = 1026LL;
        *((value *) $y_207 + 0LL) = $y_206;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_207;
        break;
      case 2:
        $d_208 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_209 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_208);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_209;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_209 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_210 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_210 + -1LL) = 1028LL;
        *((value *) $y_210 + 0LL) = $y_209;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_210;
        break;
      case 3:
        $d_211 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_212 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_211);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_212;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_212 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_213 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_213 + -1LL) = 1030LL;
        *((value *) $y_213 + 0LL) = $y_212;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_213;
        break;
      case 4:
        $d_214 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_215 =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $d_214);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_215;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_215 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_216 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_216 + -1LL) = 1032LL;
        *((value *) $y_216 + 0LL) = $y_215;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_216;
        break;
      case 5:
        $d_217 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_218 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_217);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_218;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_218 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_219 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_219 + -1LL) = 1024LL;
        *((value *) $y_219 + 0LL) = $y_218;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_219;
        break;
      case 6:
        $d_220 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_221 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_220);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_221;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_221 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_222 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_222 + -1LL) = 1026LL;
        *((value *) $y_222 + 0LL) = $y_221;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_222;
        break;
      case 7:
        $d_223 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_224 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_223);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_224;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_224 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_225 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_225 + -1LL) = 1028LL;
        *((value *) $y_225 + 0LL) = $y_224;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_225;
        break;
      case 8:
        $d_226 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_227 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_226);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_227;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_227 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_228 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_228 + -1LL) = 1030LL;
        *((value *) $y_228 + 0LL) = $y_227;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_228;
        break;
      default:
        $d_229 = *((value *) $d_200 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_230 =
          ((value (*)(struct thread_info *, value)) succ_double_known_105)
          ($tinfo, $d_229);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_230;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_230 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_231 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_231 + -1LL) = 1032LL;
        *((value *) $y_231 + 0LL) = $y_230;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_231;
        break;
      
    }
  } else {
    switch ($d_200 >> 1LL) {
      default:
        $y_201 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_201;
        break;
      
    }
  }
}

value succ_double_known_103(struct thread_info *$tinfo, value $d_167)
{
  struct stack_frame frame;
  value root[1];
  register value $y_168;
  register value $y_169;
  register value $d_170;
  register value $y_171;
  register value $y_172;
  register value $d_173;
  register value $y_174;
  register value $y_175;
  register value $d_176;
  register value $y_177;
  register value $y_178;
  register value $d_179;
  register value $y_180;
  register value $y_181;
  register value $d_182;
  register value $y_183;
  register value $y_184;
  register value $d_185;
  register value $y_186;
  register value $y_187;
  register value $d_188;
  register value $y_189;
  register value $y_190;
  register value $d_191;
  register value $y_192;
  register value $y_193;
  register value $d_194;
  register value $y_195;
  register value $y_196;
  register value $d_197;
  register value $y_198;
  register value $y_199;
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
    *(root + 0LL) = $d_167;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $d_167 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($d_167 & 1) == 0) {
    switch (*((value *) $d_167 + -1LL) & 255LL) {
      case 0:
        $d_170 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_171 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_170);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_171;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_171 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_172 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_172 + -1LL) = 1025LL;
        *((value *) $y_172 + 0LL) = $y_171;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_172;
        break;
      case 1:
        $d_173 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_174 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_173);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_174;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_174 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_175 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_175 + -1LL) = 1027LL;
        *((value *) $y_175 + 0LL) = $y_174;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_175;
        break;
      case 2:
        $d_176 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_177 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_176);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_177;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_177 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_178 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_178 + -1LL) = 1029LL;
        *((value *) $y_178 + 0LL) = $y_177;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_178;
        break;
      case 3:
        $d_179 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_180 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_179);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_180;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_180 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_181 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_181 + -1LL) = 1031LL;
        *((value *) $y_181 + 0LL) = $y_180;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_181;
        break;
      case 4:
        $d_182 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_183 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_182);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_183;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_183 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_184 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_184 + -1LL) = 1033LL;
        *((value *) $y_184 + 0LL) = $y_183;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_184;
        break;
      case 5:
        $d_185 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_186 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_185);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_186;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_186 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_187 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_187 + -1LL) = 1025LL;
        *((value *) $y_187 + 0LL) = $y_186;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_187;
        break;
      case 6:
        $d_188 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_189 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_188);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_189;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_189 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_190 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_190 + -1LL) = 1027LL;
        *((value *) $y_190 + 0LL) = $y_189;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_190;
        break;
      case 7:
        $d_191 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_192 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_191);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_192;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_192 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_193 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_193 + -1LL) = 1029LL;
        *((value *) $y_193 + 0LL) = $y_192;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_193;
        break;
      case 8:
        $d_194 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_195 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_194);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_195;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_195 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_196 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_196 + -1LL) = 1031LL;
        *((value *) $y_196 + 0LL) = $y_195;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_196;
        break;
      default:
        $d_197 = *((value *) $d_167 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_198 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_197);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_198;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_198 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_199 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_199 + -1LL) = 1033LL;
        *((value *) $y_199 + 0LL) = $y_198;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_199;
        break;
      
    }
  } else {
    switch ($d_167 >> 1LL) {
      default:
        $y_168 = 1LL;
        $y_169 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_169 + -1LL) = 1025LL;
        *((value *) $y_169 + 0LL) = $y_168;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_169;
        break;
      
    }
  }
}

value double_known_102(struct thread_info *$tinfo, value $d_135)
{
  struct stack_frame frame;
  value root[1];
  register value $y_136;
  register value $d_137;
  register value $y_138;
  register value $y_139;
  register value $d_140;
  register value $y_141;
  register value $y_142;
  register value $d_143;
  register value $y_144;
  register value $y_145;
  register value $d_146;
  register value $y_147;
  register value $y_148;
  register value $d_149;
  register value $y_150;
  register value $y_151;
  register value $d_152;
  register value $y_153;
  register value $y_154;
  register value $d_155;
  register value $y_156;
  register value $y_157;
  register value $d_158;
  register value $y_159;
  register value $y_160;
  register value $d_161;
  register value $y_162;
  register value $y_163;
  register value $d_164;
  register value $y_165;
  register value $y_166;
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
  if (($d_135 & 1) == 0) {
    switch (*((value *) $d_135 + -1LL) & 255LL) {
      case 0:
        $d_137 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_138 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_137);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_138;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_138 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_139 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_139 + -1LL) = 1024LL;
        *((value *) $y_139 + 0LL) = $y_138;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_139;
        break;
      case 1:
        $d_140 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_141 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_140);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_141;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_141 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_142 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_142 + -1LL) = 1026LL;
        *((value *) $y_142 + 0LL) = $y_141;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_142;
        break;
      case 2:
        $d_143 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_144 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_143);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_144;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_144 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_145 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_145 + -1LL) = 1028LL;
        *((value *) $y_145 + 0LL) = $y_144;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_145;
        break;
      case 3:
        $d_146 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_147 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_146);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_147;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_147 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_148 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_148 + -1LL) = 1030LL;
        *((value *) $y_148 + 0LL) = $y_147;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_148;
        break;
      case 4:
        $d_149 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_150 =
          ((value (*)(struct thread_info *, value)) double_known_102)
          ($tinfo, $d_149);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_150;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_150 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_151 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_151 + -1LL) = 1032LL;
        *((value *) $y_151 + 0LL) = $y_150;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_151;
        break;
      case 5:
        $d_152 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_153 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_152);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_153;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_153 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_154 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_154 + -1LL) = 1024LL;
        *((value *) $y_154 + 0LL) = $y_153;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_154;
        break;
      case 6:
        $d_155 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_156 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_155);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_156;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_156 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_157 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_157 + -1LL) = 1026LL;
        *((value *) $y_157 + 0LL) = $y_156;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_157;
        break;
      case 7:
        $d_158 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_159 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_158);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_159;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_159 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_160 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_160 + -1LL) = 1028LL;
        *((value *) $y_160 + 0LL) = $y_159;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_160;
        break;
      case 8:
        $d_161 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_162 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_161);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_162;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_162 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_163 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_163 + -1LL) = 1030LL;
        *((value *) $y_163 + 0LL) = $y_162;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_163;
        break;
      default:
        $d_164 = *((value *) $d_135 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_165 =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $d_164);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(2LL <= $limit - $alloc)) {
          *(root + 0LL) = $y_165;
          frame.next = root + 1LL;
          (*$tinfo).fp = &frame;
          (*$tinfo).nalloc = 2LL;
          garbage_collect($tinfo);
          $y_165 = *(root + 0LL);
          (*$tinfo).fp = frame.prev;
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        /*skip*/;
        $y_166 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_166 + -1LL) = 1032LL;
        *((value *) $y_166 + 0LL) = $y_165;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_166;
        break;
      
    }
  } else {
    switch ($d_135 >> 1LL) {
      default:
        $y_136 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_136;
        break;
      
    }
  }
}

value to_little_uint_known_101(struct thread_info *$tinfo, value $p_128)
{
  struct stack_frame frame;
  value root[1];
  register value $p_129;
  register value $y_130;
  register value $p_131;
  register value $y_132;
  register value $y_133;
  register value $y_134;
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
    *(root + 0LL) = $p_128;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 2LL;
    garbage_collect($tinfo);
    $p_128 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($p_128 & 1) == 0) {
    switch (*((value *) $p_128 + -1LL) & 255LL) {
      case 0:
        $p_129 = *((value *) $p_128 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_130 =
          ((value (*)(struct thread_info *, value)) to_little_uint_known_101)
          ($tinfo, $p_129);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value)) succ_double_known_103)
          ($tinfo, $y_130);
        return $result;
        break;
      default:
        $p_131 = *((value *) $p_128 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        /*skip*/;
        $y_132 =
          ((value (*)(struct thread_info *, value)) to_little_uint_known_101)
          ($tinfo, $p_131);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        /*skip*/;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        $result =
          ((value (*)(struct thread_info *, value)) double_known_104)
          ($tinfo, $y_132);
        return $result;
        break;
      
    }
  } else {
    switch ($p_128 >> 1LL) {
      default:
        $y_133 = 1LL;
        $y_134 = (value) ($alloc + 1LL);
        $alloc = $alloc + 2LL;
        *((value *) $y_134 + -1LL) = 1025LL;
        *((value *) $y_134 + 0LL) = $y_133;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_134;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[2];
  register value $y_531;
  register value $y_532;
  register value $y_533;
  register value $env_534;
  register value $y_535;
  register value $y_536;
  register value $y_537;
  register value $y_538;
  register value $y_539;
  register value $y_540;
  register value $y_541;
  register value $y_542;
  register value $y_543;
  register value $y_544;
  register value $y_545;
  register value $y_546;
  register value $y_547;
  register value $y_548;
  register value $y_549;
  register value $y_550;
  register value $y_551;
  register value $y_552;
  register value $y_553;
  register value $y_554;
  register value $y_555;
  register value $y_556;
  register value $y_557;
  register value $y_558;
  register value $y_559;
  register value $y_560;
  register value $y_561;
  register value $y_562;
  register value $y_563;
  register value $y_564;
  register value $y_565;
  register value $y_566;
  register value $y_567;
  register value $y_568;
  register value $y_569;
  register value $y_570;
  register value $y_571;
  register value $y_572;
  register value $y_573;
  register value $y_574;
  register value $y_575;
  register value $y_576;
  register value $y_577;
  register value $y_578;
  register value $y_579;
  register value $y_580;
  register value $y_581;
  register value $y_582;
  register value $y_583;
  register value $y_584;
  register value $y_585;
  register value $y_586;
  register value $y_587;
  register value $y_588;
  register value $y_589;
  register value $y_590;
  register value $y_591;
  register value $y_592;
  register value $y_593;
  register value $y_594;
  register value $y_595;
  register value $y_596;
  register value $y_597;
  register value $y_598;
  register value $y_599;
  register value $y_600;
  register value $y_601;
  register value $y_602;
  register value $y_603;
  register value $y_604;
  register value $y_605;
  register value $y_606;
  register value $y_607;
  register value $y_608;
  register value $y_609;
  register value $y_610;
  register value $y_611;
  register value $y_612;
  register value $y_613;
  register value $y_614;
  register value $y_615;
  register value $y_616;
  register value $y_617;
  register value $y_618;
  register value $y_619;
  register value $y_620;
  register value $y_621;
  register value $y_622;
  register value $y_623;
  register value $y_624;
  register value $y_625;
  register value $y_626;
  register value $y_627;
  register value $y_628;
  register value $y_629;
  register value $y_630;
  register value $y_631;
  register value $y_632;
  register value $y_633;
  register value $y_634;
  register value $y_635;
  register value $y_636;
  register value $y_637;
  register value $y_638;
  register value $y_639;
  register value $y_640;
  register value $y_641;
  register value $y_642;
  register value $y_643;
  register value $y_644;
  register value $y_645;
  register value $y_646;
  register value $y_647;
  register value $y_648;
  register value $y_649;
  register value $y_650;
  register value $y_651;
  register value $y_652;
  register value $y_653;
  register value $y_654;
  register value $y_655;
  register value $y_656;
  register value $y_657;
  register value $y_658;
  register value $y_659;
  register value $y_660;
  register value $y_661;
  register value $y_662;
  register value $y_663;
  register value $y_664;
  register value $y_665;
  register value $y_666;
  register value $y_667;
  register value $y_668;
  register value $y_669;
  register value $y_670;
  register value $y_671;
  register value $y_672;
  register value $y_673;
  register value $y_674;
  register value $y_675;
  register value $y_676;
  register value $y_677;
  register value $y_678;
  register value $y_679;
  register value $y_680;
  register value $y_681;
  register value $y_682;
  register value $y_683;
  register value $y_684;
  register value $y_685;
  register value $y_wrapper_clo_686;
  register value $y_687;
  register value $y_688;
  register value $CertiCoqdTestsdtestsdlazy_factorial_689;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  $y_531 = 1LL;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $y_531;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_532 =
    ((value (*)(struct thread_info *, value)) tfact_known_115)
    ($tinfo, $y_531);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(308LL <= $limit - $alloc)) {
    *(root + 1LL) = $y_532;
    frame.next = root + 2LL;
    (*$tinfo).nalloc = 308LL;
    garbage_collect($tinfo);
    $y_532 = *(root + 1LL);
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_531 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $y_533 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_533 + -1LL) = 2048LL;
  *((value *) $y_533 + 0LL) = $y_531;
  *((value *) $y_533 + 1LL) = $y_532;
  $env_534 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $env_534 + -1LL) = 1024LL;
  *((value *) $env_534 + 0LL) = $y_533;
  $y_535 = 1LL;
  $y_536 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_536 + -1LL) = 1024LL;
  *((value *) $y_536 + 0LL) = $y_535;
  $y_537 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_537 + -1LL) = 1024LL;
  *((value *) $y_537 + 0LL) = $y_536;
  $y_538 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_538 + -1LL) = 1024LL;
  *((value *) $y_538 + 0LL) = $y_537;
  $y_539 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_539 + -1LL) = 1024LL;
  *((value *) $y_539 + 0LL) = $y_538;
  $y_540 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_540 + -1LL) = 1024LL;
  *((value *) $y_540 + 0LL) = $y_539;
  $y_541 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_541 + -1LL) = 1024LL;
  *((value *) $y_541 + 0LL) = $y_540;
  $y_542 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_542 + -1LL) = 1024LL;
  *((value *) $y_542 + 0LL) = $y_541;
  $y_543 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_543 + -1LL) = 1024LL;
  *((value *) $y_543 + 0LL) = $y_542;
  $y_544 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_544 + -1LL) = 1024LL;
  *((value *) $y_544 + 0LL) = $y_543;
  $y_545 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_545 + -1LL) = 1024LL;
  *((value *) $y_545 + 0LL) = $y_544;
  $y_546 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_546 + -1LL) = 1024LL;
  *((value *) $y_546 + 0LL) = $y_545;
  $y_547 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_547 + -1LL) = 1024LL;
  *((value *) $y_547 + 0LL) = $y_546;
  $y_548 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_548 + -1LL) = 1024LL;
  *((value *) $y_548 + 0LL) = $y_547;
  $y_549 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_549 + -1LL) = 1024LL;
  *((value *) $y_549 + 0LL) = $y_548;
  $y_550 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_550 + -1LL) = 1024LL;
  *((value *) $y_550 + 0LL) = $y_549;
  $y_551 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_551 + -1LL) = 1024LL;
  *((value *) $y_551 + 0LL) = $y_550;
  $y_552 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_552 + -1LL) = 1024LL;
  *((value *) $y_552 + 0LL) = $y_551;
  $y_553 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_553 + -1LL) = 1024LL;
  *((value *) $y_553 + 0LL) = $y_552;
  $y_554 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_554 + -1LL) = 1024LL;
  *((value *) $y_554 + 0LL) = $y_553;
  $y_555 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_555 + -1LL) = 1024LL;
  *((value *) $y_555 + 0LL) = $y_554;
  $y_556 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_556 + -1LL) = 1024LL;
  *((value *) $y_556 + 0LL) = $y_555;
  $y_557 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_557 + -1LL) = 1024LL;
  *((value *) $y_557 + 0LL) = $y_556;
  $y_558 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_558 + -1LL) = 1024LL;
  *((value *) $y_558 + 0LL) = $y_557;
  $y_559 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_559 + -1LL) = 1024LL;
  *((value *) $y_559 + 0LL) = $y_558;
  $y_560 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_560 + -1LL) = 1024LL;
  *((value *) $y_560 + 0LL) = $y_559;
  $y_561 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_561 + -1LL) = 1024LL;
  *((value *) $y_561 + 0LL) = $y_560;
  $y_562 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_562 + -1LL) = 1024LL;
  *((value *) $y_562 + 0LL) = $y_561;
  $y_563 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_563 + -1LL) = 1024LL;
  *((value *) $y_563 + 0LL) = $y_562;
  $y_564 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_564 + -1LL) = 1024LL;
  *((value *) $y_564 + 0LL) = $y_563;
  $y_565 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_565 + -1LL) = 1024LL;
  *((value *) $y_565 + 0LL) = $y_564;
  $y_566 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_566 + -1LL) = 1024LL;
  *((value *) $y_566 + 0LL) = $y_565;
  $y_567 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_567 + -1LL) = 1024LL;
  *((value *) $y_567 + 0LL) = $y_566;
  $y_568 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_568 + -1LL) = 1024LL;
  *((value *) $y_568 + 0LL) = $y_567;
  $y_569 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_569 + -1LL) = 1024LL;
  *((value *) $y_569 + 0LL) = $y_568;
  $y_570 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_570 + -1LL) = 1024LL;
  *((value *) $y_570 + 0LL) = $y_569;
  $y_571 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_571 + -1LL) = 1024LL;
  *((value *) $y_571 + 0LL) = $y_570;
  $y_572 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_572 + -1LL) = 1024LL;
  *((value *) $y_572 + 0LL) = $y_571;
  $y_573 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_573 + -1LL) = 1024LL;
  *((value *) $y_573 + 0LL) = $y_572;
  $y_574 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_574 + -1LL) = 1024LL;
  *((value *) $y_574 + 0LL) = $y_573;
  $y_575 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_575 + -1LL) = 1024LL;
  *((value *) $y_575 + 0LL) = $y_574;
  $y_576 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_576 + -1LL) = 1024LL;
  *((value *) $y_576 + 0LL) = $y_575;
  $y_577 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_577 + -1LL) = 1024LL;
  *((value *) $y_577 + 0LL) = $y_576;
  $y_578 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_578 + -1LL) = 1024LL;
  *((value *) $y_578 + 0LL) = $y_577;
  $y_579 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_579 + -1LL) = 1024LL;
  *((value *) $y_579 + 0LL) = $y_578;
  $y_580 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_580 + -1LL) = 1024LL;
  *((value *) $y_580 + 0LL) = $y_579;
  $y_581 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_581 + -1LL) = 1024LL;
  *((value *) $y_581 + 0LL) = $y_580;
  $y_582 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_582 + -1LL) = 1024LL;
  *((value *) $y_582 + 0LL) = $y_581;
  $y_583 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_583 + -1LL) = 1024LL;
  *((value *) $y_583 + 0LL) = $y_582;
  $y_584 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_584 + -1LL) = 1024LL;
  *((value *) $y_584 + 0LL) = $y_583;
  $y_585 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_585 + -1LL) = 1024LL;
  *((value *) $y_585 + 0LL) = $y_584;
  $y_586 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_586 + -1LL) = 1024LL;
  *((value *) $y_586 + 0LL) = $y_585;
  $y_587 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_587 + -1LL) = 1024LL;
  *((value *) $y_587 + 0LL) = $y_586;
  $y_588 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_588 + -1LL) = 1024LL;
  *((value *) $y_588 + 0LL) = $y_587;
  $y_589 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_589 + -1LL) = 1024LL;
  *((value *) $y_589 + 0LL) = $y_588;
  $y_590 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_590 + -1LL) = 1024LL;
  *((value *) $y_590 + 0LL) = $y_589;
  $y_591 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_591 + -1LL) = 1024LL;
  *((value *) $y_591 + 0LL) = $y_590;
  $y_592 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_592 + -1LL) = 1024LL;
  *((value *) $y_592 + 0LL) = $y_591;
  $y_593 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_593 + -1LL) = 1024LL;
  *((value *) $y_593 + 0LL) = $y_592;
  $y_594 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_594 + -1LL) = 1024LL;
  *((value *) $y_594 + 0LL) = $y_593;
  $y_595 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_595 + -1LL) = 1024LL;
  *((value *) $y_595 + 0LL) = $y_594;
  $y_596 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_596 + -1LL) = 1024LL;
  *((value *) $y_596 + 0LL) = $y_595;
  $y_597 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_597 + -1LL) = 1024LL;
  *((value *) $y_597 + 0LL) = $y_596;
  $y_598 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_598 + -1LL) = 1024LL;
  *((value *) $y_598 + 0LL) = $y_597;
  $y_599 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_599 + -1LL) = 1024LL;
  *((value *) $y_599 + 0LL) = $y_598;
  $y_600 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_600 + -1LL) = 1024LL;
  *((value *) $y_600 + 0LL) = $y_599;
  $y_601 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_601 + -1LL) = 1024LL;
  *((value *) $y_601 + 0LL) = $y_600;
  $y_602 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_602 + -1LL) = 1024LL;
  *((value *) $y_602 + 0LL) = $y_601;
  $y_603 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_603 + -1LL) = 1024LL;
  *((value *) $y_603 + 0LL) = $y_602;
  $y_604 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_604 + -1LL) = 1024LL;
  *((value *) $y_604 + 0LL) = $y_603;
  $y_605 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_605 + -1LL) = 1024LL;
  *((value *) $y_605 + 0LL) = $y_604;
  $y_606 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_606 + -1LL) = 1024LL;
  *((value *) $y_606 + 0LL) = $y_605;
  $y_607 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_607 + -1LL) = 1024LL;
  *((value *) $y_607 + 0LL) = $y_606;
  $y_608 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_608 + -1LL) = 1024LL;
  *((value *) $y_608 + 0LL) = $y_607;
  $y_609 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_609 + -1LL) = 1024LL;
  *((value *) $y_609 + 0LL) = $y_608;
  $y_610 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_610 + -1LL) = 1024LL;
  *((value *) $y_610 + 0LL) = $y_609;
  $y_611 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_611 + -1LL) = 1024LL;
  *((value *) $y_611 + 0LL) = $y_610;
  $y_612 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_612 + -1LL) = 1024LL;
  *((value *) $y_612 + 0LL) = $y_611;
  $y_613 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_613 + -1LL) = 1024LL;
  *((value *) $y_613 + 0LL) = $y_612;
  $y_614 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_614 + -1LL) = 1024LL;
  *((value *) $y_614 + 0LL) = $y_613;
  $y_615 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_615 + -1LL) = 1024LL;
  *((value *) $y_615 + 0LL) = $y_614;
  $y_616 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_616 + -1LL) = 1024LL;
  *((value *) $y_616 + 0LL) = $y_615;
  $y_617 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_617 + -1LL) = 1024LL;
  *((value *) $y_617 + 0LL) = $y_616;
  $y_618 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_618 + -1LL) = 1024LL;
  *((value *) $y_618 + 0LL) = $y_617;
  $y_619 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_619 + -1LL) = 1024LL;
  *((value *) $y_619 + 0LL) = $y_618;
  $y_620 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_620 + -1LL) = 1024LL;
  *((value *) $y_620 + 0LL) = $y_619;
  $y_621 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_621 + -1LL) = 1024LL;
  *((value *) $y_621 + 0LL) = $y_620;
  $y_622 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_622 + -1LL) = 1024LL;
  *((value *) $y_622 + 0LL) = $y_621;
  $y_623 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_623 + -1LL) = 1024LL;
  *((value *) $y_623 + 0LL) = $y_622;
  $y_624 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_624 + -1LL) = 1024LL;
  *((value *) $y_624 + 0LL) = $y_623;
  $y_625 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_625 + -1LL) = 1024LL;
  *((value *) $y_625 + 0LL) = $y_624;
  $y_626 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_626 + -1LL) = 1024LL;
  *((value *) $y_626 + 0LL) = $y_625;
  $y_627 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_627 + -1LL) = 1024LL;
  *((value *) $y_627 + 0LL) = $y_626;
  $y_628 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_628 + -1LL) = 1024LL;
  *((value *) $y_628 + 0LL) = $y_627;
  $y_629 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_629 + -1LL) = 1024LL;
  *((value *) $y_629 + 0LL) = $y_628;
  $y_630 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_630 + -1LL) = 1024LL;
  *((value *) $y_630 + 0LL) = $y_629;
  $y_631 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_631 + -1LL) = 1024LL;
  *((value *) $y_631 + 0LL) = $y_630;
  $y_632 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_632 + -1LL) = 1024LL;
  *((value *) $y_632 + 0LL) = $y_631;
  $y_633 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_633 + -1LL) = 1024LL;
  *((value *) $y_633 + 0LL) = $y_632;
  $y_634 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_634 + -1LL) = 1024LL;
  *((value *) $y_634 + 0LL) = $y_633;
  $y_635 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_635 + -1LL) = 1024LL;
  *((value *) $y_635 + 0LL) = $y_634;
  $y_636 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_636 + -1LL) = 1024LL;
  *((value *) $y_636 + 0LL) = $y_635;
  $y_637 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_637 + -1LL) = 1024LL;
  *((value *) $y_637 + 0LL) = $y_636;
  $y_638 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_638 + -1LL) = 1024LL;
  *((value *) $y_638 + 0LL) = $y_637;
  $y_639 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_639 + -1LL) = 1024LL;
  *((value *) $y_639 + 0LL) = $y_638;
  $y_640 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_640 + -1LL) = 1024LL;
  *((value *) $y_640 + 0LL) = $y_639;
  $y_641 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_641 + -1LL) = 1024LL;
  *((value *) $y_641 + 0LL) = $y_640;
  $y_642 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_642 + -1LL) = 1024LL;
  *((value *) $y_642 + 0LL) = $y_641;
  $y_643 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_643 + -1LL) = 1024LL;
  *((value *) $y_643 + 0LL) = $y_642;
  $y_644 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_644 + -1LL) = 1024LL;
  *((value *) $y_644 + 0LL) = $y_643;
  $y_645 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_645 + -1LL) = 1024LL;
  *((value *) $y_645 + 0LL) = $y_644;
  $y_646 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_646 + -1LL) = 1024LL;
  *((value *) $y_646 + 0LL) = $y_645;
  $y_647 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_647 + -1LL) = 1024LL;
  *((value *) $y_647 + 0LL) = $y_646;
  $y_648 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_648 + -1LL) = 1024LL;
  *((value *) $y_648 + 0LL) = $y_647;
  $y_649 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_649 + -1LL) = 1024LL;
  *((value *) $y_649 + 0LL) = $y_648;
  $y_650 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_650 + -1LL) = 1024LL;
  *((value *) $y_650 + 0LL) = $y_649;
  $y_651 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_651 + -1LL) = 1024LL;
  *((value *) $y_651 + 0LL) = $y_650;
  $y_652 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_652 + -1LL) = 1024LL;
  *((value *) $y_652 + 0LL) = $y_651;
  $y_653 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_653 + -1LL) = 1024LL;
  *((value *) $y_653 + 0LL) = $y_652;
  $y_654 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_654 + -1LL) = 1024LL;
  *((value *) $y_654 + 0LL) = $y_653;
  $y_655 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_655 + -1LL) = 1024LL;
  *((value *) $y_655 + 0LL) = $y_654;
  $y_656 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_656 + -1LL) = 1024LL;
  *((value *) $y_656 + 0LL) = $y_655;
  $y_657 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_657 + -1LL) = 1024LL;
  *((value *) $y_657 + 0LL) = $y_656;
  $y_658 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_658 + -1LL) = 1024LL;
  *((value *) $y_658 + 0LL) = $y_657;
  $y_659 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_659 + -1LL) = 1024LL;
  *((value *) $y_659 + 0LL) = $y_658;
  $y_660 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_660 + -1LL) = 1024LL;
  *((value *) $y_660 + 0LL) = $y_659;
  $y_661 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_661 + -1LL) = 1024LL;
  *((value *) $y_661 + 0LL) = $y_660;
  $y_662 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_662 + -1LL) = 1024LL;
  *((value *) $y_662 + 0LL) = $y_661;
  $y_663 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_663 + -1LL) = 1024LL;
  *((value *) $y_663 + 0LL) = $y_662;
  $y_664 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_664 + -1LL) = 1024LL;
  *((value *) $y_664 + 0LL) = $y_663;
  $y_665 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_665 + -1LL) = 1024LL;
  *((value *) $y_665 + 0LL) = $y_664;
  $y_666 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_666 + -1LL) = 1024LL;
  *((value *) $y_666 + 0LL) = $y_665;
  $y_667 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_667 + -1LL) = 1024LL;
  *((value *) $y_667 + 0LL) = $y_666;
  $y_668 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_668 + -1LL) = 1024LL;
  *((value *) $y_668 + 0LL) = $y_667;
  $y_669 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_669 + -1LL) = 1024LL;
  *((value *) $y_669 + 0LL) = $y_668;
  $y_670 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_670 + -1LL) = 1024LL;
  *((value *) $y_670 + 0LL) = $y_669;
  $y_671 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_671 + -1LL) = 1024LL;
  *((value *) $y_671 + 0LL) = $y_670;
  $y_672 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_672 + -1LL) = 1024LL;
  *((value *) $y_672 + 0LL) = $y_671;
  $y_673 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_673 + -1LL) = 1024LL;
  *((value *) $y_673 + 0LL) = $y_672;
  $y_674 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_674 + -1LL) = 1024LL;
  *((value *) $y_674 + 0LL) = $y_673;
  $y_675 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_675 + -1LL) = 1024LL;
  *((value *) $y_675 + 0LL) = $y_674;
  $y_676 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_676 + -1LL) = 1024LL;
  *((value *) $y_676 + 0LL) = $y_675;
  $y_677 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_677 + -1LL) = 1024LL;
  *((value *) $y_677 + 0LL) = $y_676;
  $y_678 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_678 + -1LL) = 1024LL;
  *((value *) $y_678 + 0LL) = $y_677;
  $y_679 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_679 + -1LL) = 1024LL;
  *((value *) $y_679 + 0LL) = $y_678;
  $y_680 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_680 + -1LL) = 1024LL;
  *((value *) $y_680 + 0LL) = $y_679;
  $y_681 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_681 + -1LL) = 1024LL;
  *((value *) $y_681 + 0LL) = $y_680;
  $y_682 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_682 + -1LL) = 1024LL;
  *((value *) $y_682 + 0LL) = $y_681;
  $y_683 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_683 + -1LL) = 1024LL;
  *((value *) $y_683 + 0LL) = $y_682;
  $y_684 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_684 + -1LL) = 1024LL;
  *((value *) $y_684 + 0LL) = $y_683;
  $y_685 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_685 + -1LL) = 1024LL;
  *((value *) $y_685 + 0LL) = $y_684;
  $y_wrapper_clo_686 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_wrapper_clo_686 + -1LL) = 2048LL;
  *((value *) $y_wrapper_clo_686 + 0LL) = y_wrapper_118;
  *((value *) $y_wrapper_clo_686 + 1LL) = $env_534;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  *(root + 0LL) = $y_685;
  frame.next = root + 1LL;
  (*$tinfo).fp = &frame;
  $y_687 =
    ((value (*)(struct thread_info *, value, value)) memo_get_uncurried_known_119)
    ($tinfo, $y_wrapper_clo_686, $y_685);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $y_685 = *(root + 0LL);
  (*$tinfo).fp = frame.prev;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $y_688 =
    ((value (*)(struct thread_info *, value, value)) f_case_known_121)
    ($tinfo, $y_687, $y_685);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdTestsdtestsdlazy_factorial_689 =
    ((value (*)(struct thread_info *, value)) f_case_known_126)
    ($tinfo, $y_688);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdTestsdtestsdlazy_factorial_689;
}


#endif /* CERTICOQ_TESTS_TESTS_LAZY_FACTORIAL_OPT2_C */
