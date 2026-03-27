#ifndef GLUE_H
#define GLUE_H
#include <gc_stack.h>
#include <stdio.h>
extern unsigned long long get_unboxed_ordinal(value);
extern unsigned long long get_boxed_ordinal(value);
extern value *get_args(value);
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_nat_S(value, value *);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Strings_Ascii_ascii_Ascii(value, value, value, value, value, value, value, value, value *);
extern value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *, value, value, value, value, value, value, value, value);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value make_Coq_Strings_String_string_String(value, value, value *);
extern value alloc_make_Coq_Strings_String_string_String(struct thread_info *, value, value);
extern unsigned long long get_Coq_Init_Datatypes_nat_tag(value);
extern unsigned long long get_Coq_Init_Datatypes_bool_tag(value);
extern unsigned long long get_Coq_Strings_Ascii_ascii_tag(value);
extern unsigned long long get_Coq_Strings_String_string_tag(value);
extern void print_Coq_Init_Datatypes_nat(value);
extern void print_Coq_Init_Datatypes_bool(value);
extern void print_Coq_Strings_Ascii_ascii(value);
extern void print_Coq_Strings_String_string(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_bool[2][6];

extern signed char const names_of_Coq_Strings_Ascii_ascii[1][6];

extern signed char const names_of_Coq_Strings_String_string[2][12];


#endif /* GLUE_H */
