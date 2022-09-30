#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "gc_stack.h"
#include "prim_int63.h"

typedef value primfloat;
typedef value primfloatintpair;
typedef value primfloat_comparison;
typedef value primfloat_class;

primfloat mk_float (struct thread_info *tinfo, double x) {
  // trace("Calling mkC0 with %llu (%p)\n", Unsigned_long_val($arg0), (void*)$arg0);
  register value *$alloc;
  register value *$limit;
  $limit = (*tinfo).limit;
  $alloc = (*tinfo).alloc;
 if (!(2LLU <= $limit - $alloc)) {
    /*skip*/;
    (*tinfo).nalloc = 2LLU;
    garbage_collect(tinfo);
    /*skip*/;
    $alloc = (*tinfo).alloc;
    $limit = (*tinfo).limit;
  }
  *($alloc + 0LLU) = Double_tag;
  *($alloc + 1LLU) = x;
  (*tinfo).alloc = (*tinfo).alloc + 2LLU;
  // trace ("addc returns adress: %p", (void*)(((unsigned long long *) $alloc) + 1LLU));
  return (value) ((unsigned long long *) $alloc + 1LLU);
}

primfloat_comparison prim_float_compare(primfloat x, primfloat y) {
  return 0;
}

primbool prim_float_eqb(primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);
  switch (fpclassify(xv))
  { case FP_NORMAL:
    case FP_SUBNORMAL:
    case FP_INFINITE:
      return (mk_bool (xv == yv));

    case FP_NAN:
      return (mk_bool (isnan (yv)));

    case FP_ZERO:
      return (mk_bool (xv == yv && ((1 / xv) == (1 / yv))));

    default:
      exit (1); // Should not happen
  }
  // return (mk_bool (xv == yv));
}

primbool prim_float_ltb(primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);
  return (mk_bool (xv < yv));
}

primbool prim_float_leb(primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);
  return (mk_bool (xv <= yv));
}

// let eshift = 2101 (* 2*emax + prec *)
unsigned long long eshift = 2101;

primfloatintpair prim_float_frshiftexp(struct thread_info *tinfo, primfloat x) {
  double xv = Double_val(x);
  int e = 0;
  value frac;
  switch (fpclassify(xv))
  { 
    case FP_NAN: 
    case FP_INFINITE: 
    case FP_ZERO:
      return (mk_pair(tinfo, x, Val_long(0)));
    
    case FP_NORMAL:
    case FP_SUBNORMAL:
      frac = mk_float(tinfo, frexp(xv, &e));
      return (mk_pair(tinfo, frac, Val_long(e + eshift)));

    default:
      exit(1); // Should not happen
  }
}

primfloat prim_float_ldshiftexp(struct thread_info *tinfo, primfloat x, primint y) {
  //todo fix
  double xv = Double_val(x);
  int e = 0;
  value frac;
  switch (fpclassify(xv))
  { 
    case FP_NAN: 
    case FP_INFINITE: 
    case FP_ZERO:
      return (mk_pair(tinfo, x, Val_long(0)));
    
    case FP_NORMAL:
    case FP_SUBNORMAL:
      frac = mk_float(tinfo, frexp(xv, &e));
      return (mk_pair(tinfo, frac, Val_long(e + eshift)));

    default:
      exit(1); // Should not happen
  }
}

int prec = 53;

primint prim_float_normfr_mantissa(primfloat x) {
  double xv = Double_val(x);
  double f = fabs(xv);
  if (f >= 0.5 && f < 1)
  { return (Val_long ((int) (ldexp(f, prec)))); }
  else return (Val_long(0));
}

primfloat_class prim_float_classify(primfloat x) {
  double xv = Double_val(x);
  switch (fpclassify(xv))
  { 
    case FP_NAN: return ((8 << 1) + 1);
    case FP_INFINITE: return (signbit(xv) ? (7 << 1) + 1 : (6 << 1) + 1);
    case FP_ZERO: return (signbit(xv) ? (5 << 1) + 1 : (4 << 1) + 1);        
    case FP_SUBNORMAL: return (signbit(xv) ? (3 << 1) + 1 : (2 << 1) + 1);
    case FP_NORMAL: return (signbit(xv) ? (1 << 1) + 1 : 1);
    default: exit (1); // impossible
  }
}

primfloat prim_float_abs(struct thread_info *tinfo, primfloat x) {
  double xv = Double_val(x);
  return (mk_float (tinfo, fabs(xv)));
}

primfloat prim_float_sqrt(struct thread_info *tinfo, primfloat x) {
  double xv = Double_val(x);
  return (mk_float (tinfo, sqrt(xv)));
}

primfloat prim_float_opp(struct thread_info *tinfo, primfloat x) {
  double xv = Double_val(x);
  return (mk_float (tinfo, - xv));
}

primfloat prim_float_div(struct thread_info *tinfo, primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);

  return (mk_float (tinfo, xv / yv));
}

primfloat prim_float_mul(struct thread_info *tinfo, primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);

  return (mk_float (tinfo, xv * yv));
}

primfloat prim_float_add(struct thread_info *tinfo, primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);

  return (mk_float (tinfo, xv + yv));
}

primfloat prim_float_sub(struct thread_info *tinfo, primfloat x, primfloat y) {
  double xv = Double_val(x);
  double yv = Double_val(y);

  return (mk_float (tinfo, xv - yv));
}

primfloat prim_float_of_uint63(struct thread_info * tinfo, primint x) {
  double xv = (double) (Long_val(x));
  return (mk_float (tinfo, xv));
}


union double_bits {
  double d;
  uint64_t u;
};

static double next_up(double x) {
  union double_bits bits;
  if (!(x < INFINITY)) return x; // x is +oo or NaN
  bits.d = x;
  int64_t i = bits.u;
  if (i >= 0) ++bits.u; // x >= +0.0, go away from zero
  else if (bits.u + bits.u == 0) bits.u = 1; // x is -0.0, should almost never happen
  else --bits.u; // x < 0.0, go toward zero
  return bits.d;
}

static double next_down(double x) {
  union double_bits bits;
  if (!(x > -INFINITY)) return x; // x is -oo or NaN
  bits.d = x;
  int64_t i = bits.u;
  if (i == 0) bits.u = INT64_MIN + 1; // x is +0.0
  else if (i < 0) ++bits.u; // x <= -0.0, go away from zero
  else --bits.u; // x > 0.0, go toward zero
  return bits.d;
}

primfloat prim_float_next_up(struct thread_info * ti, primfloat x) {
  double xv = Double_val(x);
  return (mk_float (ti, next_up(xv)));
}

primfloat prim_float_next_down(struct thread_info * ti, primfloat x) {
  double xv = Double_val(x);
  return (mk_float (ti, next_down(xv)));
}
