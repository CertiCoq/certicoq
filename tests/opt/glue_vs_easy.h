#ifndef GLUE_VS_EASY_H
#define GLUE_VS_EASY_H
#include <gc_stack.h>
#include <stdio.h>
extern unsigned long long get_unboxed_ordinal(value);
extern unsigned long long get_boxed_ordinal(value);
extern value *get_args(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_Coq_Init_Datatypes_list_nil(void);
extern value make_Coq_Init_Datatypes_list_cons(value, value, value *);
extern value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);
extern value make_Coq_Numbers_BinNums_positive_xI(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_positive_xO(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_positive_xH(void);
extern value make_CertiCoq_Tests_lib_vs_expr_Nil(void);
extern value make_CertiCoq_Tests_lib_vs_expr_Var(value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_expr_Var(struct thread_info *, value);
extern value make_CertiCoq_Tests_lib_vs_space_atom_Next(value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Next(struct thread_info *, value, value);
extern value make_CertiCoq_Tests_lib_vs_space_atom_Lseg(value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_space_atom_Lseg(struct thread_info *, value, value);
extern value make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_pure_atom_Eqv(struct thread_info *, value, value);
extern value make_Coq_Numbers_BinNums_Z_Z0(void);
extern value make_Coq_Numbers_BinNums_Z_Zpos(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_Z_Zneg(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, value);
extern value make_CertiCoq_Tests_lib_vs_clause_PureClause(value, value, value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_clause_PureClause(struct thread_info *, value, value, value, value);
extern value make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(value, value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_clause_PosSpaceClause(struct thread_info *, value, value, value);
extern value make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(value, value, value, value *);
extern value alloc_make_CertiCoq_Tests_lib_vs_clause_NegSpaceClause(struct thread_info *, value, value, value);
extern unsigned long long get_Coq_Init_Datatypes_bool_tag(value);
extern unsigned long long get_Coq_Init_Datatypes_list_tag(value);
extern unsigned long long get_Coq_Numbers_BinNums_positive_tag(value);
extern unsigned long long get_CertiCoq_Tests_lib_vs_expr_tag(value);
extern unsigned long long get_CertiCoq_Tests_lib_vs_space_atom_tag(value);
extern unsigned long long get_CertiCoq_Tests_lib_vs_pure_atom_tag(value);
extern unsigned long long get_Coq_Numbers_BinNums_Z_tag(value);
extern unsigned long long get_CertiCoq_Tests_lib_vs_clause_tag(value);
extern void print_Coq_Init_Datatypes_bool(value);
extern void print_Coq_Init_Datatypes_list(value, void (*)(value));
extern void print_Coq_Numbers_BinNums_positive(value);
extern void print_CertiCoq_Tests_lib_vs_expr(value);
extern void print_CertiCoq_Tests_lib_vs_space_atom(value);
extern void print_CertiCoq_Tests_lib_vs_pure_atom(value);
extern void print_Coq_Numbers_BinNums_Z(value);
extern void print_CertiCoq_Tests_lib_vs_clause(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_bool[2][6];

extern signed char const names_of_Coq_Init_Datatypes_list[2][5];

extern signed char const names_of_Coq_Numbers_BinNums_positive[3][3];

extern signed char const names_of_CertiCoq_Tests_lib_vs_expr[2][4];

extern signed char const names_of_CertiCoq_Tests_lib_vs_space_atom[2][5];

extern signed char const names_of_CertiCoq_Tests_lib_vs_pure_atom[1][4];

extern signed char const names_of_Coq_Numbers_BinNums_Z[3][5];

extern signed char const names_of_CertiCoq_Tests_lib_vs_clause[3][15];


#endif /* GLUE_VS_EASY_H */
