extern void body(struct thread_info *);

extern void halt(struct thread_info *);

extern unsigned int const halt_clo[2];

extern struct thread_info *tinfo;

extern void *call_1(unsigned int, unsigned int);

extern void *call_1_export(unsigned int, unsigned int);

extern void *call_2(unsigned int, unsigned int, unsigned int);

extern void *call_3_export(unsigned int, unsigned int, unsigned int, unsigned int);

extern unsigned int make_option_None(void);

extern unsigned int make_option_Some(unsigned int, unsigned int **);

extern signed char const names_of_option[2][5];

extern int const arities_of_option[2];

extern void elim_option(unsigned int, unsigned int *, unsigned int **);

extern unsigned int make_bool_false(void);

extern unsigned int make_bool_true(void);

extern signed char const names_of_bool[2][6];

extern int const arities_of_bool[2];

extern void elim_bool(unsigned int, unsigned int *, unsigned int **);

extern unsigned int make_list_cons(unsigned int, unsigned int, unsigned int **);

extern unsigned int make_list_nil(void);

extern signed char const names_of_list[2][5];

extern int const arities_of_list[2];

extern void elim_list(unsigned int, unsigned int *, unsigned int **);

extern unsigned int make_prod_pair(unsigned int, unsigned int, unsigned int **);

extern signed char const names_of_prod[1][5];

extern int const arities_of_prod[1];

extern void elim_prod(unsigned int, unsigned int *, unsigned int **);


