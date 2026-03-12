#include "values.h"
#include "prim_int63.h"

typedef value primstring;

intnat prim_strlen(primstring s);
extern value prim_string_compare(primstring x);
extern primint prim_string_get(primstring x, primint y);
extern value prim_string_length(primstring x);
