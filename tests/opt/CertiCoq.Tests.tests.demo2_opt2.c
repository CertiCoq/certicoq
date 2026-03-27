#ifndef CERTICOQ_TESTS_TESTS_DEMO2_OPT2_C
#define CERTICOQ_TESTS_TESTS_DEMO2_OPT2_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Tests.tests.demo2_opt2.h"
extern struct thread_info *make_tinfo(void);
extern value f_case_known_103(struct thread_info *, value);
extern value map_known_102(struct thread_info *, value);
extern value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *, value, value, value);
extern value body(struct thread_info *);
value f_case_known_103(struct thread_info *, value);
value map_known_102(struct thread_info *, value);
value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *, value, value, value);
value body(struct thread_info *);
unsigned long long const body_info_230[2] = { 200LL, 0LL, };

unsigned long long const repeat2_uncurried_uncurried_uncurried_known_info_229[5] = {
  0LL, 3LL, 0LL, 1LL, 2LL, };

unsigned long long const map_known_info_228[3] = { 0LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_227[3] = { 0LL, 1LL, 0LL, };

value f_case_known_103(struct thread_info *$tinfo, value $s_119)
{
  struct stack_frame frame;
  value root[1];
  register value $y_120;
  register value $y_121;
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
  if (($s_119 & 1) == 0) {
    switch (*((value *) $s_119 + -1LL) & 255LL) {
      
    }
  } else {
    switch ($s_119 >> 1LL) {
      case 0:
        $y_120 = 3LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_120;
        break;
      default:
        $y_121 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_121;
        break;
      
    }
  }
}

value map_known_102(struct thread_info *$tinfo, value $l_112)
{
  struct stack_frame frame;
  value root[2];
  register value $y_113;
  register value $a_114;
  register value $t_115;
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
  if (($l_112 & 1) == 0) {
    switch (*((value *) $l_112 + -1LL) & 255LL) {
      default:
        $a_114 = *((value *) $l_112 + 0LL);
        $t_115 = *((value *) $l_112 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $t_115;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_116 =
          ((value (*)(struct thread_info *, value)) f_case_known_103)
          ($tinfo, $a_114);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $t_115 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_116;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_117 =
          ((value (*)(struct thread_info *, value)) map_known_102)
          ($tinfo, $t_115);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_117;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_117 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_116 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_118 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_118 + -1LL) = 2048LL;
        *((value *) $y_118 + 0LL) = $y_116;
        *((value *) $y_118 + 1LL) = $y_117;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_118;
        break;
      
    }
  } else {
    switch ($l_112 >> 1LL) {
      default:
        $y_113 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_113;
        break;
      
    }
  }
}

value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *$tinfo, value $n_104, value $y_105, value $x_106)
{
  struct stack_frame frame;
  value root[3];
  register value $y_107;
  register value $n_108;
  register value $y_109;
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
  if (($n_104 & 1) == 0) {
    switch (*((value *) $n_104 + -1LL) & 255LL) {
      default:
        $n_108 = *((value *) $n_104 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $x_106;
        *(root + 0LL) = $y_105;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_109 =
          ((value (*)(struct thread_info *, value, value, value)) repeat2_uncurried_uncurried_uncurried_known_101)
          ($tinfo, $n_108, $y_105, $x_106);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(6LL <= $limit - $alloc)) {
          *(root + 2LL) = $y_109;
          frame.next = root + 3LL;
          (*$tinfo).nalloc = 6LL;
          garbage_collect($tinfo);
          $y_109 = *(root + 2LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_106 = *(root + 1LL);
        $y_105 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_110 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_110 + -1LL) = 2048LL;
        *((value *) $y_110 + 0LL) = $y_105;
        *((value *) $y_110 + 1LL) = $y_109;
        $y_111 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_111 + -1LL) = 2048LL;
        *((value *) $y_111 + 0LL) = $x_106;
        *((value *) $y_111 + 1LL) = $y_110;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_111;
        break;
      
    }
  } else {
    switch ($n_104 >> 1LL) {
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
  register value $y_122;
  register value $y_123;
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
  register value $y_161;
  register value $y_162;
  register value $y_163;
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
  register value $y_175;
  register value $y_176;
  register value $y_177;
  register value $y_178;
  register value $y_179;
  register value $y_180;
  register value $y_181;
  register value $y_182;
  register value $y_183;
  register value $y_184;
  register value $y_185;
  register value $y_186;
  register value $y_187;
  register value $y_188;
  register value $y_189;
  register value $y_190;
  register value $y_191;
  register value $y_192;
  register value $y_193;
  register value $y_194;
  register value $y_195;
  register value $y_196;
  register value $y_197;
  register value $y_198;
  register value $y_199;
  register value $y_200;
  register value $y_201;
  register value $y_202;
  register value $y_203;
  register value $y_204;
  register value $y_205;
  register value $y_206;
  register value $y_207;
  register value $y_208;
  register value $y_209;
  register value $y_210;
  register value $y_211;
  register value $y_212;
  register value $y_213;
  register value $y_214;
  register value $y_215;
  register value $y_216;
  register value $y_217;
  register value $y_218;
  register value $y_219;
  register value $y_220;
  register value $y_221;
  register value $y_222;
  register value $y_223;
  register value $y_224;
  register value $y_225;
  register value $CertiCoqdTestsdtestsddemo2_226;
  register value *$alloc;
  register value *$limit;
  register value *$args;
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  $args = (*$tinfo).args;
  frame.next = root;
  frame.root = root;
  frame.prev = (*$tinfo).fp;
  if (!(200LL <= $limit - $alloc)) {
    /*skip*/;
    (*$tinfo).nalloc = 200LL;
    garbage_collect($tinfo);
    /*skip*/;
    $alloc = (*$tinfo).alloc;
    $limit = (*$tinfo).limit;
  }
  $y_122 = 3LL;
  $y_123 = 1LL;
  $y_124 = 1LL;
  $y_125 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_125 + -1LL) = 1024LL;
  *((value *) $y_125 + 0LL) = $y_124;
  $y_126 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_126 + -1LL) = 1024LL;
  *((value *) $y_126 + 0LL) = $y_125;
  $y_127 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_127 + -1LL) = 1024LL;
  *((value *) $y_127 + 0LL) = $y_126;
  $y_128 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_128 + -1LL) = 1024LL;
  *((value *) $y_128 + 0LL) = $y_127;
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
  $y_132 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_132 + -1LL) = 1024LL;
  *((value *) $y_132 + 0LL) = $y_131;
  $y_133 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_133 + -1LL) = 1024LL;
  *((value *) $y_133 + 0LL) = $y_132;
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
  $y_138 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_138 + -1LL) = 1024LL;
  *((value *) $y_138 + 0LL) = $y_137;
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
  $y_144 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_144 + -1LL) = 1024LL;
  *((value *) $y_144 + 0LL) = $y_143;
  $y_145 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_145 + -1LL) = 1024LL;
  *((value *) $y_145 + 0LL) = $y_144;
  $y_146 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_146 + -1LL) = 1024LL;
  *((value *) $y_146 + 0LL) = $y_145;
  $y_147 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_147 + -1LL) = 1024LL;
  *((value *) $y_147 + 0LL) = $y_146;
  $y_148 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_148 + -1LL) = 1024LL;
  *((value *) $y_148 + 0LL) = $y_147;
  $y_149 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_149 + -1LL) = 1024LL;
  *((value *) $y_149 + 0LL) = $y_148;
  $y_150 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_150 + -1LL) = 1024LL;
  *((value *) $y_150 + 0LL) = $y_149;
  $y_151 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_151 + -1LL) = 1024LL;
  *((value *) $y_151 + 0LL) = $y_150;
  $y_152 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_152 + -1LL) = 1024LL;
  *((value *) $y_152 + 0LL) = $y_151;
  $y_153 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_153 + -1LL) = 1024LL;
  *((value *) $y_153 + 0LL) = $y_152;
  $y_154 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_154 + -1LL) = 1024LL;
  *((value *) $y_154 + 0LL) = $y_153;
  $y_155 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_155 + -1LL) = 1024LL;
  *((value *) $y_155 + 0LL) = $y_154;
  $y_156 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_156 + -1LL) = 1024LL;
  *((value *) $y_156 + 0LL) = $y_155;
  $y_157 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_157 + -1LL) = 1024LL;
  *((value *) $y_157 + 0LL) = $y_156;
  $y_158 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_158 + -1LL) = 1024LL;
  *((value *) $y_158 + 0LL) = $y_157;
  $y_159 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_159 + -1LL) = 1024LL;
  *((value *) $y_159 + 0LL) = $y_158;
  $y_160 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_160 + -1LL) = 1024LL;
  *((value *) $y_160 + 0LL) = $y_159;
  $y_161 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_161 + -1LL) = 1024LL;
  *((value *) $y_161 + 0LL) = $y_160;
  $y_162 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_162 + -1LL) = 1024LL;
  *((value *) $y_162 + 0LL) = $y_161;
  $y_163 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_163 + -1LL) = 1024LL;
  *((value *) $y_163 + 0LL) = $y_162;
  $y_164 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_164 + -1LL) = 1024LL;
  *((value *) $y_164 + 0LL) = $y_163;
  $y_165 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_165 + -1LL) = 1024LL;
  *((value *) $y_165 + 0LL) = $y_164;
  $y_166 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_166 + -1LL) = 1024LL;
  *((value *) $y_166 + 0LL) = $y_165;
  $y_167 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_167 + -1LL) = 1024LL;
  *((value *) $y_167 + 0LL) = $y_166;
  $y_168 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_168 + -1LL) = 1024LL;
  *((value *) $y_168 + 0LL) = $y_167;
  $y_169 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_169 + -1LL) = 1024LL;
  *((value *) $y_169 + 0LL) = $y_168;
  $y_170 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_170 + -1LL) = 1024LL;
  *((value *) $y_170 + 0LL) = $y_169;
  $y_171 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_171 + -1LL) = 1024LL;
  *((value *) $y_171 + 0LL) = $y_170;
  $y_172 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_172 + -1LL) = 1024LL;
  *((value *) $y_172 + 0LL) = $y_171;
  $y_173 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_173 + -1LL) = 1024LL;
  *((value *) $y_173 + 0LL) = $y_172;
  $y_174 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_174 + -1LL) = 1024LL;
  *((value *) $y_174 + 0LL) = $y_173;
  $y_175 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_175 + -1LL) = 1024LL;
  *((value *) $y_175 + 0LL) = $y_174;
  $y_176 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_176 + -1LL) = 1024LL;
  *((value *) $y_176 + 0LL) = $y_175;
  $y_177 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_177 + -1LL) = 1024LL;
  *((value *) $y_177 + 0LL) = $y_176;
  $y_178 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_178 + -1LL) = 1024LL;
  *((value *) $y_178 + 0LL) = $y_177;
  $y_179 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_179 + -1LL) = 1024LL;
  *((value *) $y_179 + 0LL) = $y_178;
  $y_180 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_180 + -1LL) = 1024LL;
  *((value *) $y_180 + 0LL) = $y_179;
  $y_181 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_181 + -1LL) = 1024LL;
  *((value *) $y_181 + 0LL) = $y_180;
  $y_182 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_182 + -1LL) = 1024LL;
  *((value *) $y_182 + 0LL) = $y_181;
  $y_183 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_183 + -1LL) = 1024LL;
  *((value *) $y_183 + 0LL) = $y_182;
  $y_184 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_184 + -1LL) = 1024LL;
  *((value *) $y_184 + 0LL) = $y_183;
  $y_185 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_185 + -1LL) = 1024LL;
  *((value *) $y_185 + 0LL) = $y_184;
  $y_186 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_186 + -1LL) = 1024LL;
  *((value *) $y_186 + 0LL) = $y_185;
  $y_187 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_187 + -1LL) = 1024LL;
  *((value *) $y_187 + 0LL) = $y_186;
  $y_188 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_188 + -1LL) = 1024LL;
  *((value *) $y_188 + 0LL) = $y_187;
  $y_189 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_189 + -1LL) = 1024LL;
  *((value *) $y_189 + 0LL) = $y_188;
  $y_190 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_190 + -1LL) = 1024LL;
  *((value *) $y_190 + 0LL) = $y_189;
  $y_191 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_191 + -1LL) = 1024LL;
  *((value *) $y_191 + 0LL) = $y_190;
  $y_192 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_192 + -1LL) = 1024LL;
  *((value *) $y_192 + 0LL) = $y_191;
  $y_193 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_193 + -1LL) = 1024LL;
  *((value *) $y_193 + 0LL) = $y_192;
  $y_194 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_194 + -1LL) = 1024LL;
  *((value *) $y_194 + 0LL) = $y_193;
  $y_195 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_195 + -1LL) = 1024LL;
  *((value *) $y_195 + 0LL) = $y_194;
  $y_196 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_196 + -1LL) = 1024LL;
  *((value *) $y_196 + 0LL) = $y_195;
  $y_197 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_197 + -1LL) = 1024LL;
  *((value *) $y_197 + 0LL) = $y_196;
  $y_198 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_198 + -1LL) = 1024LL;
  *((value *) $y_198 + 0LL) = $y_197;
  $y_199 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_199 + -1LL) = 1024LL;
  *((value *) $y_199 + 0LL) = $y_198;
  $y_200 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_200 + -1LL) = 1024LL;
  *((value *) $y_200 + 0LL) = $y_199;
  $y_201 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_201 + -1LL) = 1024LL;
  *((value *) $y_201 + 0LL) = $y_200;
  $y_202 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_202 + -1LL) = 1024LL;
  *((value *) $y_202 + 0LL) = $y_201;
  $y_203 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_203 + -1LL) = 1024LL;
  *((value *) $y_203 + 0LL) = $y_202;
  $y_204 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_204 + -1LL) = 1024LL;
  *((value *) $y_204 + 0LL) = $y_203;
  $y_205 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_205 + -1LL) = 1024LL;
  *((value *) $y_205 + 0LL) = $y_204;
  $y_206 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_206 + -1LL) = 1024LL;
  *((value *) $y_206 + 0LL) = $y_205;
  $y_207 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_207 + -1LL) = 1024LL;
  *((value *) $y_207 + 0LL) = $y_206;
  $y_208 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_208 + -1LL) = 1024LL;
  *((value *) $y_208 + 0LL) = $y_207;
  $y_209 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_209 + -1LL) = 1024LL;
  *((value *) $y_209 + 0LL) = $y_208;
  $y_210 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_210 + -1LL) = 1024LL;
  *((value *) $y_210 + 0LL) = $y_209;
  $y_211 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_211 + -1LL) = 1024LL;
  *((value *) $y_211 + 0LL) = $y_210;
  $y_212 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_212 + -1LL) = 1024LL;
  *((value *) $y_212 + 0LL) = $y_211;
  $y_213 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_213 + -1LL) = 1024LL;
  *((value *) $y_213 + 0LL) = $y_212;
  $y_214 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_214 + -1LL) = 1024LL;
  *((value *) $y_214 + 0LL) = $y_213;
  $y_215 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_215 + -1LL) = 1024LL;
  *((value *) $y_215 + 0LL) = $y_214;
  $y_216 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_216 + -1LL) = 1024LL;
  *((value *) $y_216 + 0LL) = $y_215;
  $y_217 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_217 + -1LL) = 1024LL;
  *((value *) $y_217 + 0LL) = $y_216;
  $y_218 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_218 + -1LL) = 1024LL;
  *((value *) $y_218 + 0LL) = $y_217;
  $y_219 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_219 + -1LL) = 1024LL;
  *((value *) $y_219 + 0LL) = $y_218;
  $y_220 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_220 + -1LL) = 1024LL;
  *((value *) $y_220 + 0LL) = $y_219;
  $y_221 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_221 + -1LL) = 1024LL;
  *((value *) $y_221 + 0LL) = $y_220;
  $y_222 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_222 + -1LL) = 1024LL;
  *((value *) $y_222 + 0LL) = $y_221;
  $y_223 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_223 + -1LL) = 1024LL;
  *((value *) $y_223 + 0LL) = $y_222;
  $y_224 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_224 + -1LL) = 1024LL;
  *((value *) $y_224 + 0LL) = $y_223;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $y_225 =
    ((value (*)(struct thread_info *, value, value, value)) repeat2_uncurried_uncurried_uncurried_known_101)
    ($tinfo, $y_224, $y_123, $y_122);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdTestsdtestsddemo2_226 =
    ((value (*)(struct thread_info *, value)) map_known_102)
    ($tinfo, $y_225);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdTestsdtestsddemo2_226;
}


#endif /* CERTICOQ_TESTS_TESTS_DEMO2_OPT2_C */
