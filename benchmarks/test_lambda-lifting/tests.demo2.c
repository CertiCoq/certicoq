struct thread_info;
struct thread_info {
  unsigned long long *alloc;
  unsigned long long *limit;
  struct heap *heap;
  unsigned long long args[1024];
};

extern struct thread_info *make_tinfo(void);

extern unsigned long long *export(struct thread_info *);

extern void anon_uncurried_11011000(struct thread_info *, unsigned long long, unsigned long long, unsigned long long, unsigned long long);

extern void anon_11011011(struct thread_info *, unsigned long long, unsigned long long, unsigned long long);

extern void anon_11010111(struct thread_info *, unsigned long long, unsigned long long, unsigned long long);

extern void anon_11010101(struct thread_info *, unsigned long long, unsigned long long, unsigned long long);

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

void anon_uncurried_11011000(struct thread_info *tinfo, unsigned long long env_11100100, unsigned long long k_10000100, unsigned long long l_10000011, unsigned long long A_10000000)
{
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
    *(args + 3LLU) = A_10000000;
    *(args + 2LLU) = l_10000011;
    *(args + 1LLU) = k_10000100;
    *(args + 0LLU) = env_11100100;
    (garbage_collect)(anon_uncurried_info_11101110, tinfo);
    alloc = (*tinfo).alloc;
    env_11100100 = *(args + 0LLU);
    k_10000100 = *(args + 1LLU);
    l_10000011 = *(args + 2LLU);
    A_10000000 = *(args + 3LLU);
  }
  x83 = (is_ptr)((unsigned long long) l_10000011);
  if (x83) {
    switch (*((unsigned long long *) l_10000011 + 18446744073709551615LLU)
              & 255LLU) {
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
        (*tinfo).alloc = alloc;
        (*tinfo).limit = limit;
        ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
           k_code_11100101
          )(tinfo, k_env_11100110, x_10010111);
        break;
      
    }
  } else {
    switch (l_10000011 >> 1LLU) {
      default:
        x_10001010 = 3LLU;
        k_code_11100111 = *((unsigned long long *) k_10000100 + 0LLU);
        k_env_11101000 = *((unsigned long long *) k_10000100 + 1LLU);
        args = (*tinfo).args;
        (*tinfo).alloc = alloc;
        (*tinfo).limit = limit;
        ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
           k_code_11100111
          )(tinfo, k_env_11101000, x_10001010);
        break;
      
    }
  }
}

void anon_11011011(struct thread_info *tinfo, unsigned long long env_11011110, unsigned long long k_11010000, unsigned long long l_11010001)
{
  unsigned long long A_proj_11100001;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_11101111 <= limit - alloc)) {
    *(args + 2LLU) = l_11010001;
    *(args + 1LLU) = k_11010000;
    *(args + 0LLU) = env_11011110;
    (garbage_collect)(anon_info_11101111, tinfo);
    alloc = (*tinfo).alloc;
    env_11011110 = *(args + 0LLU);
    k_11010000 = *(args + 1LLU);
    l_11010001 = *(args + 2LLU);
  }
  A_proj_11100001 = *((unsigned long long *) env_11011110 + 0LLU);
  args = (*tinfo).args;
  (*tinfo).alloc = alloc;
  (*tinfo).limit = limit;
  ((void (*)(struct thread_info *, unsigned long long, unsigned long long, unsigned long long, unsigned long long)) 
     anon_uncurried_11011000
    )(tinfo, env_11011110, k_11010000, l_11010001, A_proj_11100001);
}

void anon_11010111(struct thread_info *tinfo, unsigned long long env_11011001, unsigned long long k_10000001, unsigned long long A_11010010)
{
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
    *(args + 2LLU) = A_11010010;
    *(args + 1LLU) = k_10000001;
    *(args + 0LLU) = env_11011001;
    (garbage_collect)(anon_info_11110000, tinfo);
    alloc = (*tinfo).alloc;
    env_11011001 = *(args + 0LLU);
    k_10000001 = *(args + 1LLU);
    A_11010010 = *(args + 2LLU);
  }
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
  (*tinfo).alloc = alloc;
  (*tinfo).limit = limit;
  ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
     k_code_11011100
    )(tinfo, k_env_11011101, x_10101101);
}

void anon_11010101(struct thread_info *tinfo, unsigned long long env_11101001, unsigned long long k_10111010, unsigned long long b_10111001)
{
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
    *(args + 2LLU) = b_10111001;
    *(args + 1LLU) = k_10111010;
    *(args + 0LLU) = env_11101001;
    (garbage_collect)(anon_info_11110001, tinfo);
    alloc = (*tinfo).alloc;
    env_11101001 = *(args + 0LLU);
    k_10111010 = *(args + 1LLU);
    b_10111001 = *(args + 2LLU);
  }
  x83 = (is_ptr)((unsigned long long) b_10111001);
  if (x83) {
    switch (*((unsigned long long *) b_10111001 + 18446744073709551615LLU)
              & 255LLU) {
      
    }
  } else {
    switch (b_10111001 >> 1LLU) {
      case 1:
        x_11000011 = 1LLU;
        k_code_11101010 = *((unsigned long long *) k_10111010 + 0LLU);
        k_env_11101011 = *((unsigned long long *) k_10111010 + 1LLU);
        args = (*tinfo).args;
        (*tinfo).alloc = alloc;
        (*tinfo).limit = limit;
        ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
           k_code_11101010
          )(tinfo, k_env_11101011, x_11000011);
        break;
      default:
        x_11000000 = 3LLU;
        k_code_11101100 = *((unsigned long long *) k_10111010 + 0LLU);
        k_env_11101101 = *((unsigned long long *) k_10111010 + 1LLU);
        args = (*tinfo).args;
        (*tinfo).alloc = alloc;
        (*tinfo).limit = limit;
        ((void (*)(struct thread_info *, unsigned long long, unsigned long long)) 
           k_code_11101100
          )(tinfo, k_env_11101101, x_11000000);
        break;
      
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
}


