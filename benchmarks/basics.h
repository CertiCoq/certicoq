
struct thread_info;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct Coq_Init_Datatypes_nil_args;
struct Coq_Init_Datatypes_cons_args;
struct Coq_Init_Datatypes_true_args;
struct Coq_Init_Datatypes_false_args;
struct thread_info {
  unsigned long long *alloc;
  unsigned long long *limit;
  struct heap *heap;
  unsigned long long args[1024];
};

struct Coq_Init_Datatypes_O_args {
};

struct Coq_Init_Datatypes_S_args {
  unsigned long long Coq_Init_Datatypes_S_arg_0;
};

struct Coq_Init_Datatypes_nil_args {
};

struct Coq_Init_Datatypes_cons_args {
  unsigned long long Coq_Init_Datatypes_cons_arg_0;
  unsigned long long Coq_Init_Datatypes_cons_arg_1;
};

struct Coq_Init_Datatypes_true_args {
};

struct Coq_Init_Datatypes_false_args {
};

extern unsigned int get_unboxed_ordinal(unsigned long long);
extern unsigned int get_boxed_ordinal(unsigned long long);
extern unsigned long long make_Coq_Init_Datatypes_nat_O(void);
extern unsigned long long make_Coq_Init_Datatypes_nat_S(unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, unsigned long long);
extern unsigned long long make_Coq_Init_Datatypes_list_nil(void);
extern unsigned long long make_Coq_Init_Datatypes_list_cons(unsigned long long, unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, unsigned long long, unsigned long long);
extern unsigned long long make_Coq_Init_Datatypes_bool_true(void);
extern unsigned long long make_Coq_Init_Datatypes_bool_false(void);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(unsigned long long);
extern unsigned int get_Coq_Init_Datatypes_list_tag(unsigned long long);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(unsigned long long);
extern struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(unsigned long long);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(unsigned long long);
extern struct Coq_Init_Datatypes_nil_args *get_Coq_Init_Datatypes_nil_args(unsigned long long);
extern struct Coq_Init_Datatypes_cons_args *get_Coq_Init_Datatypes_cons_args(unsigned long long);
extern struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(unsigned long long);
extern struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(unsigned long long);
extern void print_Coq_Init_Datatypes_nat(unsigned long long);
extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));
extern void print_Coq_Init_Datatypes_bool(unsigned long long);
extern void halt(struct thread_info *, unsigned long long, unsigned long long);
extern unsigned long long call(struct thread_info *, unsigned long long, unsigned long long);
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

extern unsigned long long const halt_clo[2];


