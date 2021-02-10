#include <stddef.h>

extern size_t f4(size_t, size_t, size_t, size_t);
extern size_t f6(size_t, size_t, size_t, size_t, size_t, size_t);
extern size_t f8(size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t);
extern size_t f12(size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t);
extern size_t f16(size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t, size_t);

// Tail calls from n-argument functions to m-argument functions tested
// for gcc, clang, and CompCert (ccomp) targeting x86-64 on linux or macOS.
// In the comments below, gcc or clang is called with -O2 -fomit-frame-pointer
// It's not clear that -fomit-frame-pointer changes anything
// ccomp is called with -O2.
// It's possible that clang would do better using the "GHC" calling convention.

size_t g4(size_t a, size_t b, size_t c, size_t d) {
  return f4(b,b+a,c,d);
// gcc:  move, move, add(actually leaq), jmp.  Perfect.
//clang: move, add, move, move, jmp.  Perfect.
//ccomp: extra instructions to fiddle with the stack, then tail call. Adequate.
}

size_t g3(size_t a, size_t b, size_t c) {
  return f4(b,b+a,c,0);
// gcc: move, xorl(to set zero), move add(leaq), jmp.  Perfect.
//clang:move, add, xorl, move, move, jmp.  Perfect.
//ccomp: extra instructions to fiddle with the stack, then tail call. Adequate.
}

size_t g6(size_t a, size_t b, size_t c, size_t d, size_t e, size_t f) {
  return f4(b,b+a,c,d);
// gcc:  move, move, add(leaq), jmp.  Perfect.
//clang: move, add, move, move, jmp.  Perfect.
//ccomp: extra instructions to fiddle with the stack, then tail call. Adequate.
}

size_t h3(size_t a, size_t b, size_t c) {
  return f16(a,b,c,a,b,c,a,b,c,a,b,c,a,b,c,a);
// gcc: no tail call optimization.  push args on stack, call, pop stack, return.
//clang: ditto
//ccomp: ditto
}

size_t h16(size_t a, size_t b, size_t c, size_t d,
	   size_t e, size_t f, size_t g, size_t h,
	   size_t i, size_t j, size_t k, size_t l,
	   size_t m, size_t n, size_t o, size_t p) {
  return f16(b,a,d,c, e,f,g,h,i,j,k,l,m,n,  p,o);
// gcc: 6 moves, 2 loads, 2 stores, jmp.  Perfect.
//clang: lots of pushes and pops, call, then return (no tail call optimization)
//ccomp: like clang.  Disappointing.
}

size_t j16(size_t a, size_t b, size_t c, size_t d,
	   size_t e, size_t f, size_t g, size_t h,
	   size_t i, size_t j, size_t k, size_t l,
	   size_t m, size_t n, size_t o, size_t p) {
  return f4(a+b+c+d, e+f+g+h, i+j+k+l, m);
// gcc: fourteen moves, loads, and adds; then jmp.  Perfect.  But
//     I don't actually understand why it's not necessary to pop the stack.
//clang: ditto
//ccomp: 30 loads, stores, and moves; two instructions to adjust stack;
//       then jump.  Adequate.
}

size_t h6(size_t a, size_t b, size_t c, size_t d,
	   size_t e, size_t f) {
  return f6(b,a,d,c, e,f);
// gcc: 
//clang:
//ccomp: 6 moves, 3 other stack-fiddling instructions, jmp.  Adequate
}

size_t h8(size_t a, size_t b, size_t c, size_t d,
	   size_t e, size_t f, size_t g, size_t h) {
  return f8(b,a,d,c, e,f,g,h);
// gcc: 
//clang: 6 moves, then jmp.
//ccomp: call-and-return with 24-byte stack frame. No tail-call opt.
}

size_t h12(size_t a, size_t b, size_t c, size_t d,
	   size_t e, size_t f, size_t g, size_t h,
	   size_t i, size_t j, size_t k, size_t l) {
  return f12(b,a,d,c, e,f,g,h,i,j,k,l);
// gcc: 6 moves, then jmp.
//clang:
//ccomp: call-and-return with 88-byte stack frame. No tail-call opt.
}

