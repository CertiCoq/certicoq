struct thread_info;
struct thread_info {
  unsigned long long *alloc;
  unsigned long long *limit;
  struct heap *heap;
  unsigned long long args[1024];
};

extern struct thread_info *make_tinfo(void);

extern unsigned long long *export(struct thread_info *);

extern void anon_uncurried_11011000(struct thread_info *);

extern void anon_11011011(struct thread_info *);

extern void anon_11010111(struct thread_info *);

extern void anon_11010101(struct thread_info *);

extern void body(struct thread_info *);

extern void garbage_collect(unsigned long long *, struct thread_info *);

extern _Bool is_ptr(unsigned long long);

unsigned long long const body_info_11110010[2] = { 9LL, 0LL, };

unsigned long long const anon_info_11110001[5] = { 0LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const anon_info_11110000[5] = { 5LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const anon_info_11101111[5] = { 0LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const anon_uncurried_info_11101110[6] = { 2LL, 4LL, 0LL,
  1LL, 2LL, 3LL, };

void anon_uncurried_11011000(struct thread_info *tinfo)
{
  unsigned long long env_11100100;
  unsigned long long k_10000100;
  unsigned long long l_10000011;
  unsigned long long A_10000000;
  unsigned long long x_10001100;
  unsigned long long x_10010111;
  unsigned long long k_code_11100101;
  unsigned long long k_env_11100110;
  unsigned long long x_10001010;
  unsigned long long k_code_11100111;
  unsigned long long k_env_11101000;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_uncurried_info_11101110 <= limit - alloc)) {
    (garbage_collect)(anon_uncurried_info_11101110, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_11100100 = *(args + 0LLU);
  k_10000100 = *(args + 1LLU);
  l_10000011 = *(args + 2LLU);
  A_10000000 = *(args + 3LLU);
  x83 = (is_ptr)((unsigned long long) l_10000011);
  if (x83) {
    switch (*((unsigned long long *) l_10000011 + 18446744073709551615LLU)
              & 255) {
      default:
        x_10001100 = *((unsigned long long *) l_10000011 + 0LLU);
        x_10010111 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 2LLU;
        *((unsigned long long *) x_10010111 + 18446744073709551615LLU) =
          1024LLU;
        *((unsigned long long *) x_10010111 + 0LLU) = x_10001100;
        k_code_11100101 = *((unsigned long long *) k_10000100 + 0LLU);
        k_env_11100110 = *((unsigned long long *) k_10000100 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_11100110;
        *(args + 1LLU) = x_10010111;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_11100101)(tinfo);
      
    }
  } else {
    switch (l_10000011 >> 1) {
      default:
        x_10001010 = 3LLU;
        k_code_11100111 = *((unsigned long long *) k_10000100 + 0LLU);
        k_env_11101000 = *((unsigned long long *) k_10000100 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_11101000;
        *(args + 1LLU) = x_10001010;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_11100111)(tinfo);
      
    }
  }
}

void anon_11011011(struct thread_info *tinfo)
{
  unsigned long long env_11011110;
  unsigned long long k_11010000;
  unsigned long long l_11010001;
  unsigned long long A_proj_11100001;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_11101111 <= limit - alloc)) {
    (garbage_collect)(anon_info_11101111, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_11011110 = *(args + 0LLU);
  k_11010000 = *(args + 1LLU);
  l_11010001 = *(args + 2LLU);
  A_proj_11100001 = *((unsigned long long *) env_11011110 + 0LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = env_11011110;
  *(args + 1LLU) = k_11010000;
  *(args + 2LLU) = l_11010001;
  *(args + 3LLU) = A_proj_11100001;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) anon_uncurried_11011000)(tinfo);
}

void anon_11010111(struct thread_info *tinfo)
{
  unsigned long long env_11011001;
  unsigned long long k_10000001;
  unsigned long long A_11010010;
  unsigned long long env_11011010;
  unsigned long long x_10101101;
  unsigned long long k_code_11011100;
  unsigned long long k_env_11011101;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_11110000 <= limit - alloc)) {
    (garbage_collect)(anon_info_11110000, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_11011001 = *(args + 0LLU);
  k_10000001 = *(args + 1LLU);
  A_11010010 = *(args + 2LLU);
  env_11011010 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) env_11011010 + 18446744073709551615LLU) = 1024LLU;
  *((unsigned long long *) env_11011010 + 0LLU) = A_11010010;
  x_10101101 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_10101101 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_10101101 + 0LLU) = anon_11011011;
  *((unsigned long long *) x_10101101 + 1LLU) = env_11011010;
  k_code_11011100 = *((unsigned long long *) k_10000001 + 0LLU);
  k_env_11011101 = *((unsigned long long *) k_10000001 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_11011101;
  *(args + 1LLU) = x_10101101;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_11011100)(tinfo);
}

void anon_11010101(struct thread_info *tinfo)
{
  unsigned long long env_11101001;
  unsigned long long k_10111010;
  unsigned long long b_10111001;
  unsigned long long x_11000011;
  unsigned long long k_code_11101010;
  unsigned long long k_env_11101011;
  unsigned long long x_11000000;
  unsigned long long k_code_11101100;
  unsigned long long k_env_11101101;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_11110001 <= limit - alloc)) {
    (garbage_collect)(anon_info_11110001, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_11101001 = *(args + 0LLU);
  k_10111010 = *(args + 1LLU);
  b_10111001 = *(args + 2LLU);
  x83 = (is_ptr)((unsigned long long) b_10111001);
  if (x83) {
    switch (*((unsigned long long *) b_10111001 + 18446744073709551615LLU)
              & 255) {
      
    }
  } else {
    switch (b_10111001 >> 1) {
      case 1:
        x_11000011 = 1LLU;
        k_code_11101010 = *((unsigned long long *) k_10111010 + 0LLU);
        k_env_11101011 = *((unsigned long long *) k_10111010 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_11101011;
        *(args + 1LLU) = x_11000011;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_11101010)(tinfo);
        break;
      default:
        x_11000000 = 3LLU;
        k_code_11101100 = *((unsigned long long *) k_10111010 + 0LLU);
        k_env_11101101 = *((unsigned long long *) k_10111010 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_11101101;
        *(args + 1LLU) = x_11000000;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_11101100)(tinfo);
      
    }
  }
}

void body(struct thread_info *tinfo)
{
  unsigned long long env_11010100;
  unsigned long long x_11000111;
  unsigned long long env_11010110;
  unsigned long long x_10101111;
  unsigned long long x_1110110;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*body_info_11110010 <= limit - alloc)) {
    (garbage_collect)(body_info_11110010, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_11010100 = 1LLU;
  x_11000111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_11000111 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_11000111 + 0LLU) = anon_11010101;
  *((unsigned long long *) x_11000111 + 1LLU) = env_11010100;
  env_11010110 = 1LLU;
  x_10101111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_10101111 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_10101111 + 0LLU) = anon_11010111;
  *((unsigned long long *) x_10101111 + 1LLU) = env_11010110;
  x_1110110 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_1110110 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_1110110 + 0LLU) = x_11000111;
  *((unsigned long long *) x_1110110 + 1LLU) = x_10101111;
  *(args + 1LLU) = x_1110110;
  return;
}

void halt(struct thread_info *tinfo)
{
  return;
}

unsigned long long const halt_clo[2] = { &halt, 1LL, };

struct thread_info *tinfo;

void *call_1(unsigned long long clos, unsigned long long arg0)
{
  register unsigned long long *f;
  register unsigned long long *envi;
  register unsigned long long *ret;
  if (tinfo == (void *) 0) {
    tinfo = (make_tinfo)();
  }
  f = *((unsigned long long *) clos + 0LLU);
  envi = *((unsigned long long *) clos + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg0;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = *((unsigned long long *) (*tinfo).args + 1LLU);
  return ret;
}

void *call_1_export(unsigned long long clos, unsigned long long arg0)
{
  register unsigned long long *f;
  register unsigned long long *envi;
  register unsigned long long *ret;
  if (tinfo == (void *) 0) {
    tinfo = (make_tinfo)();
  }
  f = *((unsigned long long *) clos + 0LLU);
  envi = *((unsigned long long *) clos + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg0;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = (export)(tinfo);
  return ret;
}

void *call_2(unsigned long long clos, unsigned long long arg0, unsigned long long arg1)
{
  register unsigned long long *f;
  register unsigned long long *envi;
  register unsigned long long *ret;
  if (tinfo == (void *) 0) {
    tinfo = (make_tinfo)();
  }
  f = *((unsigned long long *) clos + 0LLU);
  envi = *((unsigned long long *) clos + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg0;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = *((unsigned long long *) (*tinfo).args + 1LLU);
  f = *((unsigned long long *) ret + 0LLU);
  envi = *((unsigned long long *) ret + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg1;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = *((unsigned long long *) (*tinfo).args + 1LLU);
  return ret;
}

void *call_3_export(unsigned long long clos, unsigned long long arg0, unsigned long long arg1, unsigned long long arg2)
{
  register unsigned long long *f;
  register unsigned long long *envi;
  register unsigned long long *ret;
  if (tinfo == (void *) 0) {
    tinfo = (make_tinfo)();
  }
  f = *((unsigned long long *) clos + 0LLU);
  envi = *((unsigned long long *) clos + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg0;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = *((unsigned long long *) (*tinfo).args + 1LLU);
  f = *((unsigned long long *) ret + 0LLU);
  envi = *((unsigned long long *) ret + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg1;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = *((unsigned long long *) (*tinfo).args + 1LLU);
  f = *((unsigned long long *) ret + 0LLU);
  envi = *((unsigned long long *) ret + 1LLU);
  *((unsigned long long *) (*tinfo).args + 0LLU) = envi;
  *((unsigned long long *) (*tinfo).args + 1LLU) = halt_clo;
  *((unsigned long long *) (*tinfo).args + 2LLU) = arg2;
  ((void (*)(struct thread_info *)) f)(tinfo);
  ret = (export)(tinfo);
  return ret;
}

unsigned long long make_option_None(void)
{
  return 3;
}

unsigned long long make_option_Some(unsigned long long arg0, unsigned long long **argv)
{
  *((unsigned long long *) argv + 0LLU) = 1024LLU;
  *((unsigned long long *) argv + 1LLU) = arg0;
  return argv + 1LLU;
}

signed char const names_of_option[2][5] = { 78, 111, 110, 101, 0, 83, 111,
  109, 101, 0, };

int const arities_of_option[2] = { 0LL, 1LL, };

void elim_option(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      case 0:
        *((unsigned long long *) ordinal + 0LLU) = 1LLU;
        *((unsigned long long *) argv + 0LLU) =
          *((unsigned long long *) val + 0LLU);
        break;
      
    }
  } else {
    switch (val >> 1) {
      case 1:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        break;
      
    }
  }
}

unsigned long long make_bool_false(void)
{
  return 3;
}

unsigned long long make_bool_true(void)
{
  return 1;
}

signed char const names_of_bool[2][6] = { 102, 97, 108, 115, 101, 0, 116,
  114, 117, 101, 0, 0, };

int const arities_of_bool[2] = { 0LL, 0LL, };

void elim_bool(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      
    }
  } else {
    switch (val >> 1) {
      case 1:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        break;
      case 0:
        *((unsigned long long *) ordinal + 0LLU) = 1LLU;
        break;
      
    }
  }
}

unsigned long long make_list_cons(unsigned long long arg0, unsigned long long arg1, unsigned long long **argv)
{
  *((unsigned long long *) argv + 0LLU) = 2049LLU;
  *((unsigned long long *) argv + 1LLU) = arg0;
  *((unsigned long long *) argv + 2LLU) = arg1;
  return argv + 1LLU;
}

unsigned long long make_list_nil(void)
{
  return 1;
}

signed char const names_of_list[2][5] = { 99, 111, 110, 115, 0, 110, 105,
  108, 0, 0, };

int const arities_of_list[2] = { 2LL, 0LL, };

void elim_list(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      case 1:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        *((unsigned long long *) argv + 0LLU) =
          *((unsigned long long *) val + 0LLU);
        *((unsigned long long *) argv + 1LLU) =
          *((unsigned long long *) val + 1LLU);
        break;
      
    }
  } else {
    switch (val >> 1) {
      case 0:
        *((unsigned long long *) ordinal + 0LLU) = 1LLU;
        break;
      
    }
  }
}

unsigned long long make_prod_pair(unsigned long long arg0, unsigned long long arg1, unsigned long long **argv)
{
  *((unsigned long long *) argv + 0LLU) = 2048LLU;
  *((unsigned long long *) argv + 1LLU) = arg0;
  *((unsigned long long *) argv + 2LLU) = arg1;
  return argv + 1LLU;
}

signed char const names_of_prod[1][5] = { 112, 97, 105, 114, 0, };

int const arities_of_prod[1] = { 2LL, };

void elim_prod(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      case 0:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        *((unsigned long long *) argv + 0LLU) =
          *((unsigned long long *) val + 0LLU);
        *((unsigned long long *) argv + 1LLU) =
          *((unsigned long long *) val + 1LLU);
        break;
      
    }
  } else {
    switch (val >> 1) {
      
    }
  }
}


