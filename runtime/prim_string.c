#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include "prim_int63.h"

typedef value primstring;

#define trace(...) printf(__VA_ARGS__)

value prim_string_compare(primstring x, primstring y)
{
  /* register signed long long xr = Unsigned_long_val(x); */
  /* register signed long long yr = Unsigned_long_val(y); */
  /* register signed long long result = xr - yr; */
  trace("Calling prim_string_compare\n");
  /* trace("Calling prim_string_compare on %llu and %llu: %lli \n", x, y); */
  /* if (result == 0) return 1; */
  /* else if (result < 0) return 3; */
  /* else */
    return 1;
}

primint prim_string_get(primstring x, primint y)
{
  /* register signed long long xr = Unsigned_long_val(x); */
  /* register signed long long yr = Unsigned_long_val(y); */
  /* register signed long long result = xr - yr; */
  trace("Calling prim_string_get\n");
  /* trace("Calling prim_int63_compare on %llu and %llu: %lli \n", xr, yr, result); */
  /* if (result == 0) return 1; */
  /* else if (result < 0) return 3; */
  /* else */
    return 97;
}

primint prim_string_length(primstring x)
{
  /* register signed long long xr = Unsigned_long_val(x); */
  /* register signed long long yr = Unsigned_long_val(y); */
  /* register signed long long result = xr - yr; */
  trace("Calling prim_string_length\n");
  /* trace("Calling prim_int63_compare on %llu and %llu: %lli \n", xr, yr, result); */
  /* if (result == 0) return 1; */
  /* else if (result < 0) return 3; */
  /* else */
  return 0;
}
