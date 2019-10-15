extern void body(struct thread_info *);

extern void halt(struct thread_info *);

extern unsigned long long const halt_clo[2];

extern struct thread_info *tinfo;

extern void *call_1(unsigned long long, unsigned long long);

extern void *call_1_export(unsigned long long, unsigned long long);

extern void *call_2(unsigned long long, unsigned long long, unsigned long long);

extern void *call_3_export(unsigned long long, unsigned long long, unsigned long long, unsigned long long);

extern unsigned long long make_nat_S(unsigned long long, unsigned long long **);

extern unsigned long long make_nat_O(void);

extern signed char const names_of_nat[2][2];

extern int const arities_of_nat[2];

extern void elim_nat(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_list_cons(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_list_nil(void);

extern signed char const names_of_list[2][5];

extern int const arities_of_list[2];

extern void elim_list(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_bool_false(void);

extern unsigned long long make_bool_true(void);

extern signed char const names_of_bool[2][6];

extern int const arities_of_bool[2];

extern void elim_bool(unsigned long long, unsigned long long *, unsigned long long **);


