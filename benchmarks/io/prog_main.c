#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include "gc.h"

extern void body(struct thread_info *);
extern value args[];

extern struct thread_info;
extern unsigned int get_Coq_Strings_String_string_tag(value);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *, value, value, value, value, value, value, value, value);
extern value alloc_make_Coq_Strings_String_string_String(struct thread_info *, value, value);

extern value alloc_make_CertiCoq_Benchmarks_io_io_IO_Types_Build_IO_Types(struct thread_info *, value);
extern value alloc_make_CertiCoq_Benchmarks_io_io_IO_Impl_Build_IO_Impl(struct thread_info *, value, value);
extern value alloc_make_CertiCoq_Benchmarks_io_io_StringFFI_Build_StringFFI(struct thread_info *, value, value);

extern void* call(struct thread_info *tinfo, value clos, value arg0);

extern value const io_ret_clo[2];
extern value const io_bind_clo[2];
extern value const print_string_clo[2];
extern value const scan_string_clo[2];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

unsigned char ascii_to_char(value x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = get_Coq_Init_Datatypes_bool_tag(*((value *) *((value *) x) + i));
    c += !tag << i;
  }
  return c;
}

value print_string(struct thread_info *tinfo, value s) {
  value temp = s;

  while(1) {
    unsigned int tag = get_Coq_Strings_String_string_tag(temp);
    if(tag == 1) {
      printf("%c", ascii_to_char(temp));
      temp = *((value *) temp + 1ULL);
    } else {
      break;
    }
  } 
  printf("\n");
  fflush(stdout);

  return make_Coq_Init_Datatypes_unit_tt();
}

value bool_to_value(_Bool b) {
  if(b)
    return make_Coq_Init_Datatypes_bool_true();
  else
    return make_Coq_Init_Datatypes_bool_false();
}

value char_to_value(struct thread_info *tinfo, char c) {
  value v[8];
  for(unsigned int i = 0; i < 8; i++) {
    v[i] = bool_to_value(c & (1 << i));
  }
  return alloc_make_Coq_Strings_Ascii_ascii_Ascii(tinfo, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

value string_to_value(struct thread_info *tinfo, char *s) {
  value temp = make_Coq_Strings_String_string_EmptyString();
  for (unsigned int i = strlen(s); 0 < i; i--) {
    value c = char_to_value(tinfo, s[i-1]);
    temp = alloc_make_Coq_Strings_String_string_String(tinfo, c, temp);
  }
  return temp;
}

value scan_string(struct thread_info *tinfo) { 
  char input[100];
  scanf("%s", input);

  value s = string_to_value(tinfo, input);
  return s;
}

value calls(struct thread_info* tinfo, value clos, unsigned int n, ...)
{
  value v = clos;
  va_list args;
  va_start(args, n);

  for(; n != 0; n--) {
    v = va_arg(args, value);
    clos = call(tinfo, clos, v);
  }
  va_end(args);
  return clos;
}

value io_ret(struct thread_info * tinfo, value sigma, value x) {
  return x;
}

value io_bind(struct thread_info * tinfo, value sigma, value tau, value x, value f) {
  call(tinfo, x, 1);
  // dereference to get the first thing in A * World
  value out = *((value *) tinfo->args[1]);
  calls(tinfo, f, 2, out, 1);
  return *((value *) tinfo->args[1]);
}


/* Main */
int main(int argc, char *argv[]) {
  value clo;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;

  tinfo = make_tinfo();
  start = clock();

  // Run Coq program
  body(tinfo);
  end = clock();

  clo = tinfo -> args[1];

  // Types are dummy values
  value io_types = 
    alloc_make_CertiCoq_Benchmarks_io_io_IO_Types_Build_IO_Types(tinfo, 1);

  value io_impl = 
    alloc_make_CertiCoq_Benchmarks_io_io_IO_Impl_Build_IO_Impl(
        tinfo, 
        io_ret_clo, 
        io_bind_clo);

  value string_ffi = 
    alloc_make_CertiCoq_Benchmarks_io_io_StringFFI_Build_StringFFI(
        tinfo,
        print_string_clo,
        scan_string_clo);

  // Worlds are dummy values in runtime
  value world = 1;

  value v = calls(tinfo, clo, 4, io_types, io_impl, string_ffi, world);

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("\nTime taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
