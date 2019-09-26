extern void body(struct thread_info *);

extern void halt(struct thread_info *);

extern unsigned long long const halt_clo[2];

extern struct thread_info *tinfo;

extern void *call_1(unsigned long long, unsigned long long);

extern void *call_1_export(unsigned long long, unsigned long long);

extern void *call_2(unsigned long long, unsigned long long, unsigned long long);

extern void *call_3_export(unsigned long long, unsigned long long, unsigned long long, unsigned long long);

extern unsigned long long make_option_None(void);

extern unsigned long long make_option_Some(unsigned long long, unsigned long long **);

extern signed char const names_of_option[2][5];

extern int const arities_of_option[2];

extern void elim_option(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_bool_false(void);

extern unsigned long long make_bool_true(void);

extern signed char const names_of_bool[2][6];

extern int const arities_of_bool[2];

extern void elim_bool(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_list_cons(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_list_nil(void);

extern signed char const names_of_list[2][5];

extern int const arities_of_list[2];

extern void elim_list(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_prod_pair(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_prod[1][5];

extern int const arities_of_prod[1];

extern void elim_prod(unsigned long long, unsigned long long *, unsigned long long **);


