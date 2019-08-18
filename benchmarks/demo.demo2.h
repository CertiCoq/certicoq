extern void body(struct thread_info *);

extern void halt(struct thread_info *);

extern unsigned long long const halt_clo[2];

extern struct thread_info *tinfo;

extern void *call_1(unsigned long long, unsigned long long);

extern void *call_1_export(unsigned long long, unsigned long long);

extern void *call_2(unsigned long long, unsigned long long, unsigned long long);

extern void *call_3_export(unsigned long long, unsigned long long, unsigned long long, unsigned long long);


