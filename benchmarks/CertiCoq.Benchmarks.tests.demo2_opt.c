#ifndef CERTICOQ_BENCHMARKS_TESTS_DEMO2_OPT_C
#define CERTICOQ_BENCHMARKS_TESTS_DEMO2_OPT_C
#include <gc_stack.h>
#include <prim_string.h>
#include <prim_floats.h>
#include <prim_int63.h>
#include <coq_c_ffi.h>
#include "CertiCoq.Benchmarks.tests.demo2_opt.h"
extern struct thread_info *make_tinfo(void);
extern value f_case_known_103(struct thread_info *, value);
extern value map_known_102(struct thread_info *, value);
extern value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *, value, value, value);
extern value body(struct thread_info *);
value f_case_known_103(struct thread_info *, value);
value map_known_102(struct thread_info *, value);
value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *, value, value, value);
value body(struct thread_info *);
unsigned long long const body_info_239[2] = { 200LL, 0LL, };

unsigned long long const repeat2_uncurried_uncurried_uncurried_known_info_238[5] = {
  0LL, 3LL, 0LL, 1LL, 2LL, };

unsigned long long const map_known_info_237[3] = { 0LL, 1LL, 0LL, };

unsigned long long const f_case_known_info_236[3] = { 0LL, 1LL, 0LL, };

value f_case_known_103(struct thread_info *$tinfo, value $s_125)
{
  struct stack_frame frame;
  value root[1];
  register value $y_126;
  register value $y_127;
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
  if (($s_125 & 1) == 0) {
    switch (*((value *) $s_125 + -1LL) & 255LL) {
      
    }
  } else {
    switch ($s_125 >> 1LL) {
      case 0:
        $y_126 = 3LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_126;
        break;
      default:
        $y_127 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_127;
        break;
      
    }
  }
}

value map_known_102(struct thread_info *$tinfo, value $l_116)
{
  struct stack_frame frame;
  value root[2];
  register value $y_117;
  register value $a_118;
  register value $t_119;
  register value $y_121;
  register value $y_122;
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
  if (($l_116 & 1) == 0) {
    switch (*((value *) $l_116 + -1LL) & 255LL) {
      default:
        $a_118 = *((value *) $l_116 + 0LL);
        $t_119 = *((value *) $l_116 + 1LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $t_119;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_121 =
          ((value (*)(struct thread_info *, value)) f_case_known_103)
          ($tinfo, $a_118);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        $t_119 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 0LL) = $y_121;
        frame.next = root + 1LL;
        (*$tinfo).fp = &frame;
        $y_122 =
          ((value (*)(struct thread_info *, value)) map_known_102)
          ($tinfo, $t_119);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(3LL <= $limit - $alloc)) {
          *(root + 1LL) = $y_122;
          frame.next = root + 2LL;
          (*$tinfo).nalloc = 3LL;
          garbage_collect($tinfo);
          $y_122 = *(root + 1LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $y_121 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_123 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_123 + -1LL) = 2048LL;
        *((value *) $y_123 + 0LL) = $y_121;
        *((value *) $y_123 + 1LL) = $y_122;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_123;
        break;
      
    }
  } else {
    switch ($l_116 >> 1LL) {
      default:
        $y_117 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_117;
        break;
      
    }
  }
}

value repeat2_uncurried_uncurried_uncurried_known_101(struct thread_info *$tinfo, value $n_105, value $y_106, value $x_107)
{
  struct stack_frame frame;
  value root[3];
  register value $y_109;
  register value $n_110;
  register value $y_112;
  register value $y_113;
  register value $y_114;
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
  if (($n_105 & 1) == 0) {
    switch (*((value *) $n_105 + -1LL) & 255LL) {
      default:
        $n_110 = *((value *) $n_105 + 0LL);
        $args = (*$tinfo).args;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        *(root + 1LL) = $x_107;
        *(root + 0LL) = $y_106;
        frame.next = root + 2LL;
        (*$tinfo).fp = &frame;
        $y_112 =
          ((value (*)(struct thread_info *, value, value, value)) repeat2_uncurried_uncurried_uncurried_known_101)
          ($tinfo, $n_110, $y_106, $x_107);
        $alloc = (*$tinfo).alloc;
        $limit = (*$tinfo).limit;
        if (!(6LL <= $limit - $alloc)) {
          *(root + 2LL) = $y_112;
          frame.next = root + 3LL;
          (*$tinfo).nalloc = 6LL;
          garbage_collect($tinfo);
          $y_112 = *(root + 2LL);
          $alloc = (*$tinfo).alloc;
          $limit = (*$tinfo).limit;
        }
        $x_107 = *(root + 1LL);
        $y_106 = *(root + 0LL);
        (*$tinfo).fp = frame.prev;
        $y_113 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_113 + -1LL) = 2048LL;
        *((value *) $y_113 + 0LL) = $y_106;
        *((value *) $y_113 + 1LL) = $y_112;
        $y_114 = (value) ($alloc + 1LL);
        $alloc = $alloc + 3LL;
        *((value *) $y_114 + -1LL) = 2048LL;
        *((value *) $y_114 + 0LL) = $x_107;
        *((value *) $y_114 + 1LL) = $y_113;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_114;
        break;
      
    }
  } else {
    switch ($n_105 >> 1LL) {
      default:
        $y_109 = 1LL;
        (*$tinfo).alloc = $alloc;
        (*$tinfo).limit = $limit;
        return $y_109;
        break;
      
    }
  }
}

value body(struct thread_info *$tinfo)
{
  struct stack_frame frame;
  value root[0];
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
  register value $y_226;
  register value $y_227;
  register value $y_228;
  register value $y_229;
  register value $y_230;
  register value $y_233;
  register value $CertiCoqdBenchmarksdtestsddemo2_235;
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
  $y_128 = 3LL;
  $y_129 = 1LL;
  $y_130 = 1LL;
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
  $y_225 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_225 + -1LL) = 1024LL;
  *((value *) $y_225 + 0LL) = $y_224;
  $y_226 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_226 + -1LL) = 1024LL;
  *((value *) $y_226 + 0LL) = $y_225;
  $y_227 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_227 + -1LL) = 1024LL;
  *((value *) $y_227 + 0LL) = $y_226;
  $y_228 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_228 + -1LL) = 1024LL;
  *((value *) $y_228 + 0LL) = $y_227;
  $y_229 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_229 + -1LL) = 1024LL;
  *((value *) $y_229 + 0LL) = $y_228;
  $y_230 = (value) ($alloc + 1LL);
  $alloc = $alloc + 2LL;
  *((value *) $y_230 + -1LL) = 1024LL;
  *((value *) $y_230 + 0LL) = $y_229;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $y_233 =
    ((value (*)(struct thread_info *, value, value, value)) repeat2_uncurried_uncurried_uncurried_known_101)
    ($tinfo, $y_230, $y_129, $y_128);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  $args = (*$tinfo).args;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  /*skip*/;
  $CertiCoqdBenchmarksdtestsddemo2_235 =
    ((value (*)(struct thread_info *, value)) map_known_102)
    ($tinfo, $y_233);
  $alloc = (*$tinfo).alloc;
  $limit = (*$tinfo).limit;
  /*skip*/;
  (*$tinfo).alloc = $alloc;
  (*$tinfo).limit = $limit;
  return $CertiCoqdBenchmarksdtestsddemo2_235;
}


#endif /* CERTICOQ_BENCHMARKS_TESTS_DEMO2_OPT_C */
