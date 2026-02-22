#include "print.h"
#include "glue.CertiCoq.Benchmarks.tests.print_lst.h"

void print_gallina_nat(unsigned long long v) {
  int n = 0;
  struct Corelib_Init_Datatypes_S_args * args;

  unsigned long long val = v;
  unsigned int tag = (get_Corelib_Init_Datatypes_nat_tag)(val);

  while (tag > 0) {
      n++;
      args = get_Corelib_Init_Datatypes_S_args(val);
      val = args->Corelib_Init_Datatypes_S_arg_0;
      tag = get_Corelib_Init_Datatypes_nat_tag(val);
    };

  printf("%d", n);
}

void print_new_line(unsigned long long v) {
  printf("\n");
}


void print_gallina_ascii(unsigned long long chr) {
  int c = 0;
  unsigned long long d;
  struct Corelib_Init_Datatypes_S_args * args;

  args = get_Corelib_Init_Datatypes_S_args(chr);

  for (int i=7; i>=0; i--){
    c=c<<1;
    d = get_Corelib_Init_Datatypes_bool_tag(*((unsigned long long *) args + i));
    c+=!d;
  }

  printf("%c", c);
}


void print_gallina_string(unsigned long long str) {
  struct Corelib_Strings_String_String_args * args;

  unsigned long long chr;
  unsigned long long val = str;

  unsigned int tag = (get_Corelib_Strings_String_string_tag)(val);

  while (tag > 0) {
      args = get_Corelib_Strings_String_String_args(val);
      chr = args->Corelib_Strings_String_String_arg_0;
      print_gallina_ascii(chr);
      val = args->Corelib_Strings_String_String_arg_1;
      tag = get_Corelib_Init_Datatypes_nat_tag(val);
    };

}
