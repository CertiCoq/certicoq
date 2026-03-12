#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include "prim_int63.h"

typedef value primstring;

#define trace(...) printf(__VA_ARGS__)

intnat prim_strlen(primstring s) {
  // number_of_words_in_block * sizeof(word) - last_byte_of_block - 1
  /* returns a number of bytes (chars) */
  intnat temp;
  temp = Bosize_val(s) - 1;
  return temp - Byte (s, temp);
}

value prim_string_compare(primstring x, primstring y)
{
  trace("Calling prim_string_compare\n");
  intnat lenx = prim_strlen(x);
  intnat leny = prim_strlen(y);
  intnat cmp = 0;
  if (lenx == leny) {
    for (intnat i = 0; i < lenx; i++) {
      cmp = Byte(x, i) - Byte (y, i);
      if (cmp != 0) { return cmp; };
    }
    return 0;
  }
  { return Val_long (lenx - leny); }
}

primint prim_string_get(primstring x, primint i)
{
  return Byte(x, i);
}

primint prim_string_length(primstring x)
{
  return Val_long(prim_strlen(x));
}
