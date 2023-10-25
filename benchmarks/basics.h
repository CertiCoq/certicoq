#include "gc_stack.h"
struct closure;
struct closure {
  value (*func)(struct thread_info, value, value);
  value env;
};

extern unsigned int get_unboxed_ordinal(value);
extern unsigned int get_boxed_ordinal(value);
extern value *get_args(value);
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_nat_S(value, value *);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_list_nil(void);
extern value make_Coq_Init_Datatypes_list_cons(value, value, value *);
extern value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(value);
extern unsigned int get_Coq_Init_Datatypes_list_tag(value);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern void print_Coq_Init_Datatypes_nat(value);
extern void print_Coq_Init_Datatypes_list(value, void (*)(value));
extern void print_Coq_Init_Datatypes_bool(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_list[2][5];

extern signed char const names_of_Coq_Init_Datatypes_bool[2][6];


