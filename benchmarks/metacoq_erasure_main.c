#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>

extern void body(struct thread_info *);
extern unsigned int get_Coq_Strings_Ascii_ascii_tag(unsigned long long);
extern unsigned int get_Coq_Strings_String_string_tag(unsigned long long);

extern void print_Coq_Strings_String_string(unsigned long long);
extern void print_Coq_Strings_Ascii_ascii(unsigned long long);
extern void print_Coq_Init_Datatypes_bool(unsigned long long);

extern struct Coq_Strings_Ascii_Ascii_args *get_Coq_Strings_Ascii_Ascii_args(unsigned long long);
extern struct Coq_Strings_String_EmptyString_args *get_Coq_Strings_String_EmptyString_args(unsigned long long);
extern struct Coq_Strings_String_String_args *get_Coq_Strings_String_String_args(unsigned long long);


extern value args[];

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

//extern void print_Coq_Init_Datatypes_prod(unsigned long long, void (*)(unsigned long long), void (*)(unsigned long long));
//extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));

// void print_kn_global_decl(unsigned long long decl) {
//   print_Coq_Init_Datatypes_prod(val, print_MetaCoqker  print_MetaCoq_Erasure_EAst_global_decl);

// }
// void print_global_decls(unsigned long long decls) {
//   print_Coq_Init_Datatypes_list(val, print_kn_global_decl);

// }


unsigned int get_bool(unsigned long long $v)
{
  unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_bool_tag($v);
  switch ($tag) {
      case 0:
        return 1;
      case 1: 
        return 0;
  }
}

unsigned int get_ascii(unsigned long long $v)
{
  register unsigned int $tag;
  register void *$args;
  unsigned int x0 = 0, x1 = 0, x2 = 0, x3 = 0, x4 = 0, x5 = 0, x6 = 0, x7 = 0, c = 0;
  $tag = get_Coq_Strings_Ascii_ascii_tag($v);
  switch ($tag) {
    case 0:
      $args = get_Coq_Strings_Ascii_Ascii_args($v);
      x0 = get_bool(*((unsigned long long *) $args + 0));
      x1 = get_bool(*((unsigned long long *) $args + 1));
      x2 = get_bool(*((unsigned long long *) $args + 2));
      x3 = get_bool(*((unsigned long long *) $args + 3));
      x4 = get_bool(*((unsigned long long *) $args + 4));
      x5 = get_bool(*((unsigned long long *) $args + 5));
      x6 = get_bool(*((unsigned long long *) $args + 6));
      x7 = get_bool(*((unsigned long long *) $args + 7));
      c = (x0 + 2 * x1 + 4 * x2 + 8 * x3 + 16 * x4 + 32 * x5 + 64 * x6 + 128 * x7);
      return c;
  }
}
void print_string(unsigned long long $v)
{
  register unsigned int $tag;
  register void *$args;
  unsigned int c;
  $tag = get_Coq_Strings_String_string_tag($v);
  switch ($tag) {
    case 0: break;
    case 1:
      $args = get_Coq_Strings_String_String_args($v);
      c = get_ascii(*((unsigned long long *) $args + 0));
      printf("%c", (char) c);
      print_string(*((unsigned long long *) $args + 1));
      break;
    
  }
}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  
  // Specify number of runs
  int n = 1;
  if (argc > 1) n = atoi(argv[1]);

  start = clock();
  // Run Coq program
  for (int i = 0; i < n; i ++) {
    tinfo = make_tinfo();
    body(tinfo);
  }
  end = clock();

  val = tinfo -> args[1];
  // TODO : fold over nat to print the C string
  print_string(val);
  printf("\n");

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
