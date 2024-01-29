#include "gc_stack.h"

value get_unboxed_ordinal(value $v)
{
  return Val_long($v);
  // >> 1LLU);
}

value get_boxed_ordinal(value $v)
{
  return Val_long(*((unsigned long long *) $v + 18446744073709551615LLU) & 255LLU);
}
