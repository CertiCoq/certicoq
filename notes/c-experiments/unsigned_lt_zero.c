#include <stddef.h>

// Will {gcc, clang, compcert} optimize away unsigned comparisons (_ < 0) on -O2?
// gcc: yes
// clang: yes
// compcert: no

extern int f(size_t limit, size_t alloc);
extern int g(size_t limit, size_t alloc);
extern int h(size_t limit, size_t alloc);
extern int i(size_t limit, size_t alloc);

int f(size_t limit, size_t alloc)
{
  if (limit - alloc < (size_t)0)
    return 1;
  return 0;
}

int g(size_t limit, size_t alloc)
{
  if (limit - alloc < 0LL)
    return 1;
  return 0;
}

int h(size_t limit, size_t alloc)
{
  if ((size_t)(limit - alloc) < (size_t)0)
    return 1;
  return 0;
}

int i(size_t limit, size_t alloc)
{
  if (limit - alloc < 0)
    return 1;
  return 0;
}
