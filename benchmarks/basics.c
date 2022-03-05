
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

extern int printf(signed char *);
extern _Bool is_ptr(unsigned long long);
unsigned int get_unboxed_ordinal(unsigned long long);
unsigned int get_boxed_ordinal(unsigned long long);
unsigned long long make_Coq_Init_Datatypes_nat_O(void);
unsigned long long make_Coq_Init_Datatypes_nat_S(unsigned long long, unsigned long long *);
unsigned long long alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, unsigned long long);
unsigned long long make_Coq_Init_Datatypes_list_nil(void);
unsigned long long make_Coq_Init_Datatypes_list_cons(unsigned long long, unsigned long long, unsigned long long *);
unsigned long long alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, unsigned long long, unsigned long long);
unsigned long long make_Coq_Init_Datatypes_bool_true(void);
unsigned long long make_Coq_Init_Datatypes_bool_false(void);
unsigned int get_Coq_Init_Datatypes_nat_tag(unsigned long long);
unsigned int get_Coq_Init_Datatypes_list_tag(unsigned long long);
unsigned int get_Coq_Init_Datatypes_bool_tag(unsigned long long);
struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(unsigned long long);
struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(unsigned long long);
struct Coq_Init_Datatypes_nil_args *get_Coq_Init_Datatypes_nil_args(unsigned long long);
struct Coq_Init_Datatypes_cons_args *get_Coq_Init_Datatypes_cons_args(unsigned long long);
struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(unsigned long long);
struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(unsigned long long);
void print_Coq_Init_Datatypes_nat(unsigned long long);
void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));
void print_Coq_Init_Datatypes_bool(unsigned long long);
void halt(struct thread_info *, unsigned long long, unsigned long long);
unsigned long long call(struct thread_info *, unsigned long long, unsigned long long);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned int get_unboxed_ordinal(unsigned long long $v)
{
  return $v >> 1LLU;
}

unsigned int get_boxed_ordinal(unsigned long long $v)
{
  return *((unsigned long long *) $v + 18446744073709551615LLU) & 255LLU;
}

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_list[2][5] = { 110, 105, 108,
  0, 0, 99, 111, 110, 115, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_bool[2][6] = { 116, 114, 117,
  101, 0, 0, 102, 97, 108, 115, 101, 0, /* skip 0 */ };

unsigned long long make_Coq_Init_Datatypes_nat_O(void)
{
  return 1;
}

unsigned long long make_Coq_Init_Datatypes_nat_S(unsigned long long $arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1024LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return $argv + 1LLU;
}

unsigned long long alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *$tinfo, unsigned long long $arg0)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 1024LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LLU;
  return $argv + 1LLU;
}

unsigned long long make_Coq_Init_Datatypes_list_nil(void)
{
  return 1;
}

unsigned long long make_Coq_Init_Datatypes_list_cons(unsigned long long $arg0, unsigned long long $arg1, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 2048LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  return $argv + 1LLU;
}

unsigned long long alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *$tinfo, unsigned long long $arg0, unsigned long long $arg1)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 2048LLU;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LLU;
  return $argv + 1LLU;
}

unsigned long long make_Coq_Init_Datatypes_bool_true(void)
{
  return 1;
}

unsigned long long make_Coq_Init_Datatypes_bool_false(void)
{
  return 3;
}

unsigned int get_Coq_Init_Datatypes_nat_tag(unsigned long long $v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      
    }
  }
}

unsigned int get_Coq_Init_Datatypes_list_tag(unsigned long long $v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      
    }
  }
}

unsigned int get_Coq_Init_Datatypes_bool_tag(unsigned long long $v)
{
  register unsigned int $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_O_args *) 0;
}

struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_S_args *) $v;
}

struct Coq_Init_Datatypes_nil_args *get_Coq_Init_Datatypes_nil_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_nil_args *) 0;
}

struct Coq_Init_Datatypes_cons_args *get_Coq_Init_Datatypes_cons_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_cons_args *) $v;
}

struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_true_args *) 0;
}

struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(unsigned long long $v)
{
  return (struct Coq_Init_Datatypes_false_args *) 0;
}

void print_Coq_Init_Datatypes_nat(unsigned long long $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_nat_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      break;
    case 1:
      $args = get_Coq_Init_Datatypes_S_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat(*((unsigned long long *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_list(unsigned long long $v, void $print_param_A(unsigned long long))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_list_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      break;
    case 1:
      $args = get_Coq_Init_Datatypes_cons_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_list + $tag));
      printf(space_lit);
      $print_param_A(*((unsigned long long *) $args + 0));
      printf(space_lit);
      print_Coq_Init_Datatypes_list
        (*((unsigned long long *) $args + 1), $print_param_A);
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_bool(unsigned long long $v)
{
  register unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_bool_tag($v);
  printf(*(names_of_Coq_Init_Datatypes_bool + $tag));
}

void halt(struct thread_info *$tinfo, unsigned long long $env, unsigned long long $arg)
{
  *((unsigned long long *) (*$tinfo).args + 1LLU) = $arg;
  return;
}

unsigned long long const halt_clo[2] = { &halt, 1LL, };

unsigned long long call(struct thread_info *$tinfo, unsigned long long $clo, unsigned long long $arg)
{
  register unsigned long long *$f;
  register unsigned long long *$envi;
  $f = *((unsigned long long *) $clo + 0LLU);
  $envi = *((unsigned long long *) $clo + 1LLU);
  ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
    $f)
    ($tinfo, $envi, $arg);
  return *((unsigned long long *) (*$tinfo).args + 1LLU);
}


