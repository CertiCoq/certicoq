#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include "gc.h"

extern void body(struct thread_info *);
extern value args[];

extern struct thread_info;
extern void print_Coq_Init_Datatypes_bool(value);
extern value get_Coq_Init_Datatypes_pair_args(value);
extern value get_Coq_Strings_String_string_tag(value);
extern value get_Coq_Init_Datatypes_bool_tag(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value make_Coq_Strings_String_string_String(value, value, value**);
extern void print_Coq_Init_Datatypes_unit(value);
extern void* call(struct thread_info *tinfo, value clos, value arg0);
extern value make_Top_FFI_Build_FFI(value, value, value, value**);

extern value const print_string_clo[2];
extern value const scan_string_clo[2];
extern value const print_time_clo[2];


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
  unsigned int tag;
  value temp = s;

  while(1) {
    tag = get_Coq_Strings_String_string_tag(temp);
    if(tag == 1) {
        printf("%c", ascii_to_char(temp));
        fflush(stdout);
        temp = *((value *) temp + 1ULL);
    } else {
      break;
    }
  } 
  printf("\n");
  fflush(stdout);

  return make_Coq_Init_Datatypes_unit_tt();
}

value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *tinfo, value arg0, value arg1, value arg2, value arg3, value arg4, value arg5, value arg6, value arg7)
{
  value *y = tinfo->alloc;
  *((value *) y + 0LLU) = 8192LLU;
  *((value *) y + 1LLU) = arg0;
  *((value *) y + 2LLU) = arg1;
  *((value *) y + 3LLU) = arg2;
  *((value *) y + 4LLU) = arg3;
  *((value *) y + 5LLU) = arg4;
  *((value *) y + 6LLU) = arg5;
  *((value *) y + 7LLU) = arg6;
  *((value *) y + 8LLU) = arg7;
  tinfo->alloc += 9;
  return (value) (y + 1LLU);
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

value alloc_make_Coq_Strings_String_string_String(struct thread_info *tinfo, value arg0, value arg1)
{
  value *y = tinfo->alloc;
  *(y + 0LLU) = 2048LLU;
  *(y + 1LLU) = arg0;
  *(y + 2LLU) = arg1;
  tinfo->alloc += 3;
  return (value) (y + 1LLU);
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

value print_time(struct thread_info *tinfo) { 
  clock_t now = clock();
  printf("%lu\n", now);
  fflush(stdout);
  return make_Coq_Init_Datatypes_unit_tt(); 
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

  /* Get the andb function from the arguments array */
  clo = tinfo -> args[1];

  value ffi[10];
  value built_ffi = 
    make_Top_FFI_Build_FFI(
        print_string_clo,
        scan_string_clo,
        print_time_clo,
        ffi);
  value world = 1;

  value v = calls(tinfo, clo, 2, built_ffi, world);

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("\nTime taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
