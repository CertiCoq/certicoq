struct thread_info;
struct thread_info {
  unsigned long long *alloc;
  unsigned long long *limit;
  struct heap *heap;
  unsigned long long args[1024];
};

extern struct thread_info *make_tinfo(void);

extern unsigned long long *export(struct thread_info *);

extern void anon_111000000(struct thread_info *);

extern void anon_110111110(struct thread_info *);

extern void anon_110111000(struct thread_info *);

extern void repeat_110110011(struct thread_info *);

extern void anon_110110001(struct thread_info *);

extern void anon_110101111(struct thread_info *);

extern void anon_111110000(struct thread_info *);

extern void anon_111101110(struct thread_info *);

extern void anon_111101000(struct thread_info *);

extern void repeat_111100011(struct thread_info *);

extern void anon_111100001(struct thread_info *);

extern void anon_111011111(struct thread_info *);

extern void anon_111011101(struct thread_info *);

extern void anon_110101101(struct thread_info *);

extern void anon_1000010100(struct thread_info *);

extern void app_uncurried_110101011(struct thread_info *);

extern void anon_110101001(struct thread_info *);

extern void anon_110100111(struct thread_info *);

extern void body(struct thread_info *);

extern void garbage_collect(unsigned long long *, struct thread_info *);

extern _Bool is_ptr(unsigned long long);

unsigned long long const body_info_1000110110[2] = { 3LL, 0LL, };

unsigned long long const anon_info_1000110101[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000110100[5] = { 3LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const app_uncurried_info_1000110011[6] = { 6LL, 4LL, 0LL,
  1LL, 2LL, 3LL, };

unsigned long long const anon_info_1000110010[4] = { 3LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000110001[4] = { 10LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000110000[4] = { 3LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000101111[4] = { 6LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000101110[5] = { 3LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const repeat_info_1000101101[5] = { 5LL, 3LL, 0LL, 1LL,
  2LL, };

unsigned long long const anon_info_1000101100[5] = { 12LL, 3LL, 0LL, 1LL,
  2LL, };

unsigned long long const anon_info_1000101011[4] = { 3LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000101010[4] = { 0LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000101001[4] = { 13LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000101000[5] = { 3LL, 3LL, 0LL, 1LL, 2LL,
  };

unsigned long long const repeat_info_1000100111[5] = { 5LL, 3LL, 0LL, 1LL,
  2LL, };

unsigned long long const anon_info_1000100110[5] = { 12LL, 3LL, 0LL, 1LL,
  2LL, };

unsigned long long const anon_info_1000100101[4] = { 3LL, 2LL, 0LL, 1LL, };

unsigned long long const anon_info_1000100100[4] = { 0LL, 2LL, 0LL, 1LL, };

void anon_111000000(struct thread_info *tinfo)
{
  unsigned long long env_111000110;
  unsigned long long kapf_110100100;
  unsigned long long anon_proj_111000111;
  unsigned long long anon_proj_111001000;
  unsigned long long kapf_code_111001001;
  unsigned long long kapf_env_111001010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000100100 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000100100, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111000110 = *(args + 0LLU);
  kapf_110100100 = *(args + 1LLU);
  anon_proj_111000111 = *((unsigned long long *) env_111000110 + 1LLU);
  anon_proj_111001000 = *((unsigned long long *) env_111000110 + 0LLU);
  kapf_code_111001001 = *((unsigned long long *) kapf_110100100 + 0LLU);
  kapf_env_111001010 = *((unsigned long long *) kapf_110100100 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = kapf_env_111001010;
  *(args + 1LLU) = anon_proj_111000111;
  *(args + 2LLU) = anon_proj_111001000;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) kapf_code_111001001)(tinfo);
}

void anon_110111110(struct thread_info *tinfo)
{
  unsigned long long env_111001011;
  unsigned long long x1kdcon_110100001;
  unsigned long long x_proj_111001100;
  unsigned long long anon_110100010;
  unsigned long long k_proj_111001101;
  unsigned long long k_code_111001110;
  unsigned long long k_env_111001111;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000100101 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000100101, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111001011 = *(args + 0LLU);
  x1kdcon_110100001 = *(args + 1LLU);
  x_proj_111001100 = *((unsigned long long *) env_111001011 + 0LLU);
  anon_110100010 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_110100010 + 18446744073709551615LLU) =
    2049LLU;
  *((unsigned long long *) anon_110100010 + 0LLU) = x_proj_111001100;
  *((unsigned long long *) anon_110100010 + 1LLU) = x1kdcon_110100001;
  k_proj_111001101 = *((unsigned long long *) env_111001011 + 1LLU);
  k_code_111001110 = *((unsigned long long *) k_proj_111001101 + 0LLU);
  k_env_111001111 = *((unsigned long long *) k_proj_111001101 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_111001111;
  *(args + 1LLU) = anon_110100010;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_111001110)(tinfo);
}

void anon_110111000(struct thread_info *tinfo)
{
  unsigned long long env_110111011;
  unsigned long long k_110011101;
  unsigned long long n_110011110;
  unsigned long long anon_110011111;
  unsigned long long x_proj_110111101;
  unsigned long long env_110111100;
  unsigned long long anon_110100000;
  unsigned long long env_110111111;
  unsigned long long anon_110100011;
  unsigned long long x_proj_111000011;
  unsigned long long anon_110100101;
  unsigned long long k_code_111010000;
  unsigned long long k_env_111010001;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000100110 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000100110, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_110111011 = *(args + 0LLU);
  k_110011101 = *(args + 1LLU);
  n_110011110 = *(args + 2LLU);
  x83 = (is_ptr)((unsigned long long) n_110011110);
  if (x83) {
    switch (*((unsigned long long *) n_110011110 + 18446744073709551615LLU)
              & 255) {
      default:
        anon_110011111 = *((unsigned long long *) n_110011110 + 0LLU);
        x_proj_110111101 = *((unsigned long long *) env_110111011 + 0LLU);
        env_110111100 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) env_110111100 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) env_110111100 + 0LLU) = x_proj_110111101;
        *((unsigned long long *) env_110111100 + 1LLU) = k_110011101;
        anon_110100000 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) anon_110100000 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) anon_110100000 + 0LLU) = anon_110111110;
        *((unsigned long long *) anon_110100000 + 1LLU) = env_110111100;
        env_110111111 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) env_110111111 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) env_110111111 + 0LLU) = anon_110011111;
        *((unsigned long long *) env_110111111 + 1LLU) = anon_110100000;
        anon_110100011 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) anon_110100011 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) anon_110100011 + 0LLU) = anon_111000000;
        *((unsigned long long *) anon_110100011 + 1LLU) = env_110111111;
        x_proj_111000011 = *((unsigned long long *) env_110111011 + 0LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = env_110111011;
        *(args + 1LLU) = anon_110100011;
        *(args + 2LLU) = x_proj_111000011;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) repeat_110110011)(tinfo);
      
    }
  } else {
    switch (n_110011110 >> 1) {
      default:
        anon_110100101 = 1LLU;
        k_code_111010000 = *((unsigned long long *) k_110011101 + 0LLU);
        k_env_111010001 = *((unsigned long long *) k_110011101 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_111010001;
        *(args + 1LLU) = anon_110100101;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_111010000)(tinfo);
      
    }
  }
}

void repeat_110110011(struct thread_info *tinfo)
{
  unsigned long long env_110110110;
  unsigned long long k_110011010;
  unsigned long long x_110011011;
  unsigned long long env_110110111;
  unsigned long long anon_110011100;
  unsigned long long k_code_110111001;
  unsigned long long k_env_110111010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*repeat_info_1000100111 <= limit - alloc)) {
    (garbage_collect)(repeat_info_1000100111, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_110110110 = *(args + 0LLU);
  k_110011010 = *(args + 1LLU);
  x_110011011 = *(args + 2LLU);
  env_110110111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) env_110110111 + 18446744073709551615LLU) =
    1024LLU;
  *((unsigned long long *) env_110110111 + 0LLU) = x_110011011;
  anon_110011100 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_110011100 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_110011100 + 0LLU) = anon_110111000;
  *((unsigned long long *) anon_110011100 + 1LLU) = env_110110111;
  k_code_110111001 = *((unsigned long long *) k_110011010 + 0LLU);
  k_env_110111010 = *((unsigned long long *) k_110011010 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_110111010;
  *(args + 1LLU) = anon_110011100;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_110111001)(tinfo);
}

void anon_110110001(struct thread_info *tinfo)
{
  unsigned long long env_111010010;
  unsigned long long k_10010000;
  unsigned long long x_10001111;
  unsigned long long anon_clo_111010011;
  unsigned long long k_code_111010100;
  unsigned long long k_env_111010101;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101000 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101000, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111010010 = *(args + 0LLU);
  k_10010000 = *(args + 1LLU);
  x_10001111 = *(args + 2LLU);
  anon_clo_111010011 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_clo_111010011 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_clo_111010011 + 0LLU) = anon_110110001;
  *((unsigned long long *) anon_clo_111010011 + 1LLU) = env_111010010;
  k_code_111010100 = *((unsigned long long *) k_10010000 + 0LLU);
  k_env_111010101 = *((unsigned long long *) k_10010000 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_111010101;
  *(args + 1LLU) = anon_clo_111010011;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_111010100)(tinfo);
}

void anon_110101111(struct thread_info *tinfo)
{
  unsigned long long env_111010110;
  unsigned long long kapf_10100000;
  unsigned long long x_10100010;
  unsigned long long x_10100011;
  unsigned long long x_10100100;
  unsigned long long x_10100101;
  unsigned long long x_10100110;
  unsigned long long x_10100111;
  unsigned long long anon_clo_111011000;
  unsigned long long kapf_code_111011001;
  unsigned long long kapf_env_111011010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101001 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101001, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111010110 = *(args + 0LLU);
  kapf_10100000 = *(args + 1LLU);
  x_10100010 = 1LLU;
  x_10100011 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_10100011 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_10100011 + 0LLU) = x_10100010;
  x_10100100 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_10100100 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_10100100 + 0LLU) = x_10100011;
  x_10100101 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_10100101 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_10100101 + 0LLU) = x_10100100;
  x_10100110 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_10100110 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_10100110 + 0LLU) = x_10100101;
  x_10100111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_10100111 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_10100111 + 0LLU) = x_10100110;
  anon_clo_111011000 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_clo_111011000 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_clo_111011000 + 0LLU) = anon_110101101;
  *((unsigned long long *) anon_clo_111011000 + 1LLU) = env_111010110;
  kapf_code_111011001 = *((unsigned long long *) kapf_10100000 + 0LLU);
  kapf_env_111011010 = *((unsigned long long *) kapf_10100000 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = kapf_env_111011010;
  *(args + 1LLU) = anon_clo_111011000;
  *(args + 2LLU) = x_10100111;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) kapf_code_111011001)(tinfo);
}

void anon_111110000(struct thread_info *tinfo)
{
  unsigned long long env_111110110;
  unsigned long long kapf_110010001;
  unsigned long long anon_proj_111110111;
  unsigned long long anon_proj_111111000;
  unsigned long long kapf_code_111111001;
  unsigned long long kapf_env_111111010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101010 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101010, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111110110 = *(args + 0LLU);
  kapf_110010001 = *(args + 1LLU);
  anon_proj_111110111 = *((unsigned long long *) env_111110110 + 1LLU);
  anon_proj_111111000 = *((unsigned long long *) env_111110110 + 0LLU);
  kapf_code_111111001 = *((unsigned long long *) kapf_110010001 + 0LLU);
  kapf_env_111111010 = *((unsigned long long *) kapf_110010001 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = kapf_env_111111010;
  *(args + 1LLU) = anon_proj_111110111;
  *(args + 2LLU) = anon_proj_111111000;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) kapf_code_111111001)(tinfo);
}

void anon_111101110(struct thread_info *tinfo)
{
  unsigned long long env_111111011;
  unsigned long long x1kdcon_110001110;
  unsigned long long x_proj_111111100;
  unsigned long long anon_110001111;
  unsigned long long k_proj_111111101;
  unsigned long long k_code_111111110;
  unsigned long long k_env_111111111;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101011 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101011, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111111011 = *(args + 0LLU);
  x1kdcon_110001110 = *(args + 1LLU);
  x_proj_111111100 = *((unsigned long long *) env_111111011 + 0LLU);
  anon_110001111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_110001111 + 18446744073709551615LLU) =
    2049LLU;
  *((unsigned long long *) anon_110001111 + 0LLU) = x_proj_111111100;
  *((unsigned long long *) anon_110001111 + 1LLU) = x1kdcon_110001110;
  k_proj_111111101 = *((unsigned long long *) env_111111011 + 1LLU);
  k_code_111111110 = *((unsigned long long *) k_proj_111111101 + 0LLU);
  k_env_111111111 = *((unsigned long long *) k_proj_111111101 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_111111111;
  *(args + 1LLU) = anon_110001111;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_111111110)(tinfo);
}

void anon_111101000(struct thread_info *tinfo)
{
  unsigned long long env_111101011;
  unsigned long long k_110001010;
  unsigned long long n_110001011;
  unsigned long long anon_110001100;
  unsigned long long x_proj_111101101;
  unsigned long long env_111101100;
  unsigned long long anon_110001101;
  unsigned long long env_111101111;
  unsigned long long anon_110010000;
  unsigned long long x_proj_111110011;
  unsigned long long anon_110010010;
  unsigned long long k_code_1000000000;
  unsigned long long k_env_1000000001;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101100 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101100, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111101011 = *(args + 0LLU);
  k_110001010 = *(args + 1LLU);
  n_110001011 = *(args + 2LLU);
  x83 = (is_ptr)((unsigned long long) n_110001011);
  if (x83) {
    switch (*((unsigned long long *) n_110001011 + 18446744073709551615LLU)
              & 255) {
      default:
        anon_110001100 = *((unsigned long long *) n_110001011 + 0LLU);
        x_proj_111101101 = *((unsigned long long *) env_111101011 + 0LLU);
        env_111101100 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) env_111101100 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) env_111101100 + 0LLU) = x_proj_111101101;
        *((unsigned long long *) env_111101100 + 1LLU) = k_110001010;
        anon_110001101 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) anon_110001101 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) anon_110001101 + 0LLU) = anon_111101110;
        *((unsigned long long *) anon_110001101 + 1LLU) = env_111101100;
        env_111101111 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) env_111101111 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) env_111101111 + 0LLU) = anon_110001100;
        *((unsigned long long *) env_111101111 + 1LLU) = anon_110001101;
        anon_110010000 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) anon_110010000 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) anon_110010000 + 0LLU) = anon_111110000;
        *((unsigned long long *) anon_110010000 + 1LLU) = env_111101111;
        x_proj_111110011 = *((unsigned long long *) env_111101011 + 0LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = env_111101011;
        *(args + 1LLU) = anon_110010000;
        *(args + 2LLU) = x_proj_111110011;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) repeat_111100011)(tinfo);
      
    }
  } else {
    switch (n_110001011 >> 1) {
      default:
        anon_110010010 = 1LLU;
        k_code_1000000000 = *((unsigned long long *) k_110001010 + 0LLU);
        k_env_1000000001 = *((unsigned long long *) k_110001010 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_1000000001;
        *(args + 1LLU) = anon_110010010;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_1000000000)(tinfo);
      
    }
  }
}

void repeat_111100011(struct thread_info *tinfo)
{
  unsigned long long env_111100110;
  unsigned long long k_110000111;
  unsigned long long x_110001000;
  unsigned long long env_111100111;
  unsigned long long anon_110001001;
  unsigned long long k_code_111101001;
  unsigned long long k_env_111101010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*repeat_info_1000101101 <= limit - alloc)) {
    (garbage_collect)(repeat_info_1000101101, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111100110 = *(args + 0LLU);
  k_110000111 = *(args + 1LLU);
  x_110001000 = *(args + 2LLU);
  env_111100111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) env_111100111 + 18446744073709551615LLU) =
    1024LLU;
  *((unsigned long long *) env_111100111 + 0LLU) = x_110001000;
  anon_110001001 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_110001001 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_110001001 + 0LLU) = anon_111101000;
  *((unsigned long long *) anon_110001001 + 1LLU) = env_111100111;
  k_code_111101001 = *((unsigned long long *) k_110000111 + 0LLU);
  k_env_111101010 = *((unsigned long long *) k_110000111 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_111101010;
  *(args + 1LLU) = anon_110001001;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_111101001)(tinfo);
}

void anon_111100001(struct thread_info *tinfo)
{
  unsigned long long env_1000000010;
  unsigned long long k_10111011;
  unsigned long long x_10111010;
  unsigned long long anon_clo_1000000011;
  unsigned long long k_code_1000000100;
  unsigned long long k_env_1000000101;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101110 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101110, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000000010 = *(args + 0LLU);
  k_10111011 = *(args + 1LLU);
  x_10111010 = *(args + 2LLU);
  anon_clo_1000000011 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_clo_1000000011 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_clo_1000000011 + 0LLU) = anon_111100001;
  *((unsigned long long *) anon_clo_1000000011 + 1LLU) = env_1000000010;
  k_code_1000000100 = *((unsigned long long *) k_10111011 + 0LLU);
  k_env_1000000101 = *((unsigned long long *) k_10111011 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_1000000101;
  *(args + 1LLU) = anon_clo_1000000011;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_1000000100)(tinfo);
}

void anon_111011111(struct thread_info *tinfo)
{
  unsigned long long env_1000000110;
  unsigned long long kapf_11001011;
  unsigned long long x_11001101;
  unsigned long long x_11001110;
  unsigned long long x_11001111;
  unsigned long long x_11010000;
  unsigned long long anon_proj_1000000111;
  unsigned long long kapf_code_1000001000;
  unsigned long long kapf_env_1000001001;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000101111 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000101111, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000000110 = *(args + 0LLU);
  kapf_11001011 = *(args + 1LLU);
  x_11001101 = 1LLU;
  x_11001110 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_11001110 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_11001110 + 0LLU) = x_11001101;
  x_11001111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_11001111 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_11001111 + 0LLU) = x_11001110;
  x_11010000 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) x_11010000 + 18446744073709551615LLU) = 1025LLU;
  *((unsigned long long *) x_11010000 + 0LLU) = x_11001111;
  anon_proj_1000000111 = *((unsigned long long *) env_1000000110 + 0LLU);
  kapf_code_1000001000 = *((unsigned long long *) kapf_11001011 + 0LLU);
  kapf_env_1000001001 = *((unsigned long long *) kapf_11001011 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = kapf_env_1000001001;
  *(args + 1LLU) = anon_proj_1000000111;
  *(args + 2LLU) = x_11010000;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) kapf_code_1000001000)(tinfo);
}

void anon_111011101(struct thread_info *tinfo)
{
  unsigned long long env_1000001010;
  unsigned long long kapArg_11010110;
  unsigned long long anon_clo_1000001110;
  unsigned long long kapArg_proj_1000001111;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000110000 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000110000, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000001010 = *(args + 0LLU);
  kapArg_11010110 = *(args + 1LLU);
  anon_clo_1000001110 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_clo_1000001110 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_clo_1000001110 + 0LLU) = anon_110100111;
  *((unsigned long long *) anon_clo_1000001110 + 1LLU) = env_1000001010;
  kapArg_proj_1000001111 = *((unsigned long long *) env_1000001010 + 0LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = env_1000001010;
  *(args + 1LLU) = anon_clo_1000001110;
  *(args + 2LLU) = kapArg_11010110;
  *(args + 3LLU) = kapArg_proj_1000001111;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) app_uncurried_110101011)(tinfo);
}

void anon_110101101(struct thread_info *tinfo)
{
  unsigned long long env_111011011;
  unsigned long long kapArg_10101101;
  unsigned long long env_111011100;
  unsigned long long x_11010111;
  unsigned long long env_111011110;
  unsigned long long x_11010100;
  unsigned long long env_111100010;
  unsigned long long x_11000101;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000110001 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000110001, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_111011011 = *(args + 0LLU);
  kapArg_10101101 = *(args + 1LLU);
  env_111011100 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) env_111011100 + 18446744073709551615LLU) =
    1024LLU;
  *((unsigned long long *) env_111011100 + 0LLU) = kapArg_10101101;
  x_11010111 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_11010111 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_11010111 + 0LLU) = anon_111011101;
  *((unsigned long long *) x_11010111 + 1LLU) = env_111011100;
  env_111011110 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 2LLU;
  *((unsigned long long *) env_111011110 + 18446744073709551615LLU) =
    1024LLU;
  *((unsigned long long *) env_111011110 + 0LLU) = x_11010111;
  x_11010100 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_11010100 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_11010100 + 0LLU) = anon_111011111;
  *((unsigned long long *) x_11010100 + 1LLU) = env_111011110;
  env_111100010 = 1LLU;
  x_11000101 = 3LLU;
  args = (*tinfo).args;
  *(args + 0LLU) = env_111100010;
  *(args + 1LLU) = x_11010100;
  *(args + 2LLU) = x_11000101;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) repeat_111100011)(tinfo);
}

void anon_1000010100(struct thread_info *tinfo)
{
  unsigned long long env_1000011000;
  unsigned long long x1kdcon_101011001;
  unsigned long long anon_proj_1000011001;
  unsigned long long x_101011010;
  unsigned long long k_proj_1000011010;
  unsigned long long k_code_1000011011;
  unsigned long long k_env_1000011100;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000110010 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000110010, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000011000 = *(args + 0LLU);
  x1kdcon_101011001 = *(args + 1LLU);
  anon_proj_1000011001 = *((unsigned long long *) env_1000011000 + 1LLU);
  x_101011010 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_101011010 + 18446744073709551615LLU) = 2049LLU;
  *((unsigned long long *) x_101011010 + 0LLU) = anon_proj_1000011001;
  *((unsigned long long *) x_101011010 + 1LLU) = x1kdcon_101011001;
  k_proj_1000011010 = *((unsigned long long *) env_1000011000 + 0LLU);
  k_code_1000011011 = *((unsigned long long *) k_proj_1000011010 + 0LLU);
  k_env_1000011100 = *((unsigned long long *) k_proj_1000011010 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_1000011100;
  *(args + 1LLU) = x_101011010;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_1000011011)(tinfo);
}

void app_uncurried_110101011(struct thread_info *tinfo)
{
  unsigned long long env_1000010010;
  unsigned long long k_100110010;
  unsigned long long m_100110001;
  unsigned long long l_100101110;
  unsigned long long x_100111010;
  unsigned long long x_100111001;
  unsigned long long env_1000010011;
  unsigned long long x_101011011;
  unsigned long long k_code_1000011101;
  unsigned long long k_env_1000011110;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*app_uncurried_info_1000110011 <= limit - alloc)) {
    (garbage_collect)(app_uncurried_info_1000110011, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000010010 = *(args + 0LLU);
  k_100110010 = *(args + 1LLU);
  m_100110001 = *(args + 2LLU);
  l_100101110 = *(args + 3LLU);
  x83 = (is_ptr)((unsigned long long) l_100101110);
  if (x83) {
    switch (*((unsigned long long *) l_100101110 + 18446744073709551615LLU)
              & 255) {
      default:
        x_100111010 = *((unsigned long long *) l_100101110 + 1LLU);
        x_100111001 = *((unsigned long long *) l_100101110 + 0LLU);
        env_1000010011 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) env_1000010011 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) env_1000010011 + 0LLU) = k_100110010;
        *((unsigned long long *) env_1000010011 + 1LLU) = x_100111001;
        x_101011011 = (unsigned long long) (alloc + 1LLU);
        alloc = alloc + 3LLU;
        *((unsigned long long *) x_101011011 + 18446744073709551615LLU) =
          2048LLU;
        *((unsigned long long *) x_101011011 + 0LLU) = anon_1000010100;
        *((unsigned long long *) x_101011011 + 1LLU) = env_1000010011;
        args = (*tinfo).args;
        *(args + 0LLU) = env_1000010010;
        *(args + 1LLU) = x_101011011;
        *(args + 2LLU) = m_100110001;
        *(args + 3LLU) = x_100111010;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) app_uncurried_110101011)(tinfo);
      
    }
  } else {
    switch (l_100101110 >> 1) {
      default:
        k_code_1000011101 = *((unsigned long long *) k_100110010 + 0LLU);
        k_env_1000011110 = *((unsigned long long *) k_100110010 + 1LLU);
        args = (*tinfo).args;
        *(args + 0LLU) = k_env_1000011110;
        *(args + 1LLU) = m_100110001;
        (*tinfo).alloc = alloc;
        ((void (*)(struct thread_info *)) k_code_1000011101)(tinfo);
      
    }
  }
}

void anon_110101001(struct thread_info *tinfo)
{
  unsigned long long env_1000011111;
  unsigned long long k_1111110;
  unsigned long long x_1111101;
  unsigned long long anon_clo_1000100000;
  unsigned long long k_code_1000100001;
  unsigned long long k_env_1000100010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000110100 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000110100, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000011111 = *(args + 0LLU);
  k_1111110 = *(args + 1LLU);
  x_1111101 = *(args + 2LLU);
  anon_clo_1000100000 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) anon_clo_1000100000 + 18446744073709551615LLU) =
    2048LLU;
  *((unsigned long long *) anon_clo_1000100000 + 0LLU) = anon_110101001;
  *((unsigned long long *) anon_clo_1000100000 + 1LLU) = env_1000011111;
  k_code_1000100001 = *((unsigned long long *) k_1111110 + 0LLU);
  k_env_1000100010 = *((unsigned long long *) k_1111110 + 1LLU);
  args = (*tinfo).args;
  *(args + 0LLU) = k_env_1000100010;
  *(args + 1LLU) = anon_clo_1000100000;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) k_code_1000100001)(tinfo);
}

void anon_110100111(struct thread_info *tinfo)
{
  unsigned long long env_1000100011;
  unsigned long long kapArg_11011010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  _Bool x83;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*anon_info_1000110101 <= limit - alloc)) {
    (garbage_collect)(anon_info_1000110101, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_1000100011 = *(args + 0LLU);
  kapArg_11011010 = *(args + 1LLU);
  *(args + 1LLU) = kapArg_11011010;
  return;
}

void body(struct thread_info *tinfo)
{
  unsigned long long env_110101110;
  unsigned long long x_10101011;
  unsigned long long env_110110010;
  unsigned long long x_10011010;
  unsigned long long *alloc;
  unsigned long long *limit;
  unsigned long long *args;
  alloc = (*tinfo).alloc;
  limit = (*tinfo).limit;
  args = (*tinfo).args;
  if (!(*body_info_1000110110 <= limit - alloc)) {
    (garbage_collect)(body_info_1000110110, tinfo);
    alloc = (*tinfo).alloc;
  }
  env_110101110 = 1LLU;
  x_10101011 = (unsigned long long) (alloc + 1LLU);
  alloc = alloc + 3LLU;
  *((unsigned long long *) x_10101011 + 18446744073709551615LLU) = 2048LLU;
  *((unsigned long long *) x_10101011 + 0LLU) = anon_110101111;
  *((unsigned long long *) x_10101011 + 1LLU) = env_110101110;
  env_110110010 = 1LLU;
  x_10011010 = 1LLU;
  args = (*tinfo).args;
  *(args + 0LLU) = env_110110010;
  *(args + 1LLU) = x_10101011;
  *(args + 2LLU) = x_10011010;
  (*tinfo).alloc = alloc;
  ((void (*)(struct thread_info *)) repeat_110110011)(tinfo);
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

unsigned long long make_nat_S(unsigned long long arg0, unsigned long long **argv)
{
  *((unsigned long long *) argv + 0LLU) = 1025LLU;
  *((unsigned long long *) argv + 1LLU) = arg0;
  return argv + 1LLU;
}

unsigned long long make_nat_O(void)
{
  return 1;
}

signed char const names_of_nat[2][2] = { 83, 0, 79, 0, };

int const arities_of_nat[2] = { 1LL, 0LL, };

void elim_nat(unsigned long long val, unsigned long long *ordinal, unsigned long long **argv)
{
  _Bool x83;
  x83 = (is_ptr)((unsigned long long) val);
  if (x83) {
    switch (*((unsigned long long *) val + 18446744073709551615LLU) & 255) {
      case 1:
        *((unsigned long long *) ordinal + 0LLU) = 0LLU;
        *((unsigned long long *) argv + 0LLU) =
          *((unsigned long long *) val + 0LLU);
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


