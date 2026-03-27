#ifndef CERTICOQ_TESTS_TESTS_PRINT_LST_C
#define CERTICOQ_TESTS_TESTS_PRINT_LST_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "print.h"
#include "CertiCoq.Tests.tests.print_lst.h"
extern struct thread_info *make_tinfo(void);
extern value aux_known_104(struct thread_info *, value);
extern value body(struct thread_info *);
value aux_known_104(struct thread_info *, value);
value body(struct thread_info *);
unsigned long long const body_info_179[2] = { 57LL, 0LL, };

unsigned long long const aux_known_info_178[3] = { 12LL, 1LL, 0LL, };

value aux_known_104(struct thread_info *$tinfo, value $l_106)
{
  struct stack_frame frame;
  value root[1];
  register value $y_107;
  register value $x_108;
  register value $l_109;
  register value $prim_110;
  register value $prim_111;
  register value $y_112;
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
  register value $prim_123;
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
  if (!(12LL <= $limit - $alloc)) {
    *(root + 0LL) = $l_106;
    frame.next = root + 1LL;
    (*$tinfo).fp = &frame;
    (*$tinfo).nalloc = 12LL;
    garbage_collect($tinfo);
    $l_106 = *(root + 0LL);
    (*$tinfo).fp = frame.prev;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  if (($l_106 & 1) == 0) {
    switch (*((value *) $l_106 + -1LL) & 255LL) {
      default:
        $x_108 = *((value *) $l_106 + 0LL);
        $l_109 = *((value *) $l_106 + 1LL);
        if (($l_109 & 1) == 0) {
          switch (*((value *) $l_109 + -1LL) & 255LL) {
            default:
              $prim_111 = ((value (*)(value)) print_gallina_nat)($x_108);
              $y_112 = 3LL;
              $y_113 = 3LL;
              $y_114 = 1LL;
              $y_115 = 3LL;
              $y_116 = 3LL;
              $y_117 = 3LL;
              $y_118 = 1LL;
              $y_119 = 1LL;
              $y_120 = (value) ($alloc + 1LL);
              $alloc = $alloc + 9LL;
              *((value *) $y_120 + -1LL) = 8192LL;
              *((value *) $y_120 + 0LL) = $y_112;
              *((value *) $y_120 + 1LL) = $y_113;
              *((value *) $y_120 + 2LL) = $y_114;
              *((value *) $y_120 + 3LL) = $y_115;
              *((value *) $y_120 + 4LL) = $y_116;
              *((value *) $y_120 + 5LL) = $y_117;
              *((value *) $y_120 + 6LL) = $y_118;
              *((value *) $y_120 + 7LL) = $y_119;
              $y_121 = 1LL;
              $y_122 = (value) ($alloc + 1LL);
              $alloc = $alloc + 3LL;
              *((value *) $y_122 + -1LL) = 2048LL;
              *((value *) $y_122 + 0LL) = $y_120;
              *((value *) $y_122 + 1LL) = $y_121;
              $prim_123 = ((value (*)(value)) print_gallina_string)($y_122);
              $args = (*$tinfo).args;
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              $result =
                ((value (*)(struct thread_info *, value)) aux_known_104)
                ($tinfo, $l_109);
              return $result;
              break;
            
          }
        } else {
          switch ($l_109 >> 1LL) {
            default:
              $prim_110 = ((value (*)(value)) print_gallina_nat)($x_108);
              (*$tinfo).alloc = $alloc;
              (*$tinfo).limit = $limit;
              return $prim_110;
              break;
            
          }
        }
        break;
      
    }
  } else {
    switch ($l_106 >> 1LL) {
      default:
        $y_107 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_107;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
  register value $y_124;
  register value $y_125;
  register value $y_126;
  register value $y_127;
  register value $y_128;
  register value $y_129;
  register value $y_130;
  register value $y_131;
  register value $y_132;
  register value $y_133;
  register value $y_134;
  register value $y_135;
  register value $y_136;
  register value $y_137;
  register value $y_138;
  register value $y_139;
  register value $y_140;
  register value $y_141;
  register value $y_142;
  register value $y_143;
  register value $y_144;
  register value $y_145;
  register value $y_146;
  register value $y_147;
  register value $y_148;
  register value $y_149;
  register value $y_150;
  register value $y_151;
  register value $y_152;
  register value $y_153;
  register value $y_154;
  register value $y_155;
  register value $y_156;
  register value $y_157;
  register value $y_158;
  register value $y_159;
  register value $y_160;
  register value $prim_161;
  register value $anon_163;
  register value $y_164;
  register value $y_165;
  register value $y_166;
  register value $y_167;
  register value $y_168;
  register value $y_169;
  register value $y_170;
  register value $y_171;
  register value $y_172;
  register value $y_173;
  register value $y_174;
  register value $prim_175;
  register value $y_176;
  register value $prim_177;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(57LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 57LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_124 = 1LL;
  $y_125 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_125 + -1LL) = 1024LL;
  *((value *) $y_125 + 0LL) = $y_124;
  $y_126 = 1LL;
  $y_127 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_127 + -1LL) = 1024LL;
  *((value *) $y_127 + 0LL) = $y_126;
  $y_128 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_128 + -1LL) = 1024LL;
  *((value *) $y_128 + 0LL) = $y_127;
  $y_129 = 1LL;
  $y_130 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_130 + -1LL) = 1024LL;
  *((value *) $y_130 + 0LL) = $y_129;
  $y_131 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_131 + -1LL) = 1024LL;
  *((value *) $y_131 + 0LL) = $y_130;
  $y_132 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_132 + -1LL) = 1024LL;
  *((value *) $y_132 + 0LL) = $y_131;
  $y_133 = 1LL;
  $y_134 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_134 + -1LL) = 1024LL;
  *((value *) $y_134 + 0LL) = $y_133;
  $y_135 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_135 + -1LL) = 1024LL;
  *((value *) $y_135 + 0LL) = $y_134;
  $y_136 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_136 + -1LL) = 1024LL;
  *((value *) $y_136 + 0LL) = $y_135;
  $y_137 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_137 + -1LL) = 1024LL;
  *((value *) $y_137 + 0LL) = $y_136;
  $y_138 = 1LL;
  $y_139 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_139 + -1LL) = 1024LL;
  *((value *) $y_139 + 0LL) = $y_138;
  $y_140 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_140 + -1LL) = 1024LL;
  *((value *) $y_140 + 0LL) = $y_139;
  $y_141 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_141 + -1LL) = 1024LL;
  *((value *) $y_141 + 0LL) = $y_140;
  $y_142 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_142 + -1LL) = 1024LL;
  *((value *) $y_142 + 0LL) = $y_141;
  $y_143 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_143 + -1LL) = 1024LL;
  *((value *) $y_143 + 0LL) = $y_142;
  $y_144 = 1LL;
  $y_145 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_145 + -1LL) = 2048LL;
  *((value *) $y_145 + 0LL) = $y_143;
  *((value *) $y_145 + 1LL) = $y_144;
  $y_146 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_146 + -1LL) = 2048LL;
  *((value *) $y_146 + 0LL) = $y_137;
  *((value *) $y_146 + 1LL) = $y_145;
  $y_147 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_147 + -1LL) = 2048LL;
  *((value *) $y_147 + 0LL) = $y_132;
  *((value *) $y_147 + 1LL) = $y_146;
  $y_148 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_148 + -1LL) = 2048LL;
  *((value *) $y_148 + 0LL) = $y_128;
  *((value *) $y_148 + 1LL) = $y_147;
  $y_149 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_149 + -1LL) = 2048LL;
  *((value *) $y_149 + 0LL) = $y_125;
  *((value *) $y_149 + 1LL) = $y_148;
  $y_150 = 3LL;
  $y_151 = 3LL;
  $y_152 = 1LL;
  $y_153 = 3LL;
  $y_154 = 3LL;
  $y_155 = 1LL;
  $y_156 = 3LL;
  $y_157 = 1LL;
  $y_158 = (value) ($alloc + 1LL);
  $alloc = $alloc + 9LL;
  *((value *) $y_158 + -1LL) = 8192LL;
  *((value *) $y_158 + 0LL) = $y_150;
  *((value *) $y_158 + 1LL) = $y_151;
  *((value *) $y_158 + 2LL) = $y_152;
  *((value *) $y_158 + 3LL) = $y_153;
  *((value *) $y_158 + 4LL) = $y_154;
  *((value *) $y_158 + 5LL) = $y_155;
  *((value *) $y_158 + 6LL) = $y_156;
  *((value *) $y_158 + 7LL) = $y_157;
  $y_159 = 1LL;
  $y_160 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_160 + -1LL) = 2048LL;
  *((value *) $y_160 + 0LL) = $y_158;
  *((value *) $y_160 + 1LL) = $y_159;
  $prim_161 = ((value (*)(value)) print_gallina_string)($y_160);
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $anon_163 =
    ((value (*)(struct thread_info *, value)) aux_known_104)
    ($tinfo, $y_149);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  if (!(12LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 12LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  /*skip*/;
  $y_164 = 3LL;
  $y_165 = 1LL;
  $y_166 = 3LL;
  $y_167 = 3LL;
  $y_168 = 3LL;
  $y_169 = 1LL;
  $y_170 = 3LL;
  $y_171 = 1LL;
  $y_172 = (value) ($alloc + 1LL);
  $alloc = $alloc + 9LL;
  *((value *) $y_172 + -1LL) = 8192LL;
  *((value *) $y_172 + 0LL) = $y_164;
  *((value *) $y_172 + 1LL) = $y_165;
  *((value *) $y_172 + 2LL) = $y_166;
  *((value *) $y_172 + 3LL) = $y_167;
  *((value *) $y_172 + 4LL) = $y_168;
  *((value *) $y_172 + 5LL) = $y_169;
  *((value *) $y_172 + 6LL) = $y_170;
  *((value *) $y_172 + 7LL) = $y_171;
  $y_173 = 1LL;
  $y_174 = (value) ($alloc + 1LL);
  $alloc = $alloc + 3LL;
  *((value *) $y_174 + -1LL) = 2048LL;
  *((value *) $y_174 + 0LL) = $y_172;
  *((value *) $y_174 + 1LL) = $y_173;
  $prim_175 = ((value (*)(value)) print_gallina_string)($y_174);
  $y_176 = 1LL;
  $prim_177 = ((value (*)(value)) print_new_line)($y_176);
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $prim_177;
}


#endif /* CERTICOQ_TESTS_TESTS_PRINT_LST_C */
