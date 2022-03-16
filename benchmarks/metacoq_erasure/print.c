#include <stdio.h>
#include <stdlib.h>
#include "print.h"
#include "gc.h"
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/callback.h>

void call_coq_msg_info(value msg)
{
  static const value * closure_f = NULL;
  if (closure_f == NULL) {
     /* First time around, look up by name */
    closure_f = caml_named_value("coq_msg_info");
  }
  caml_callback(*closure_f, msg);
}

value print_msg_info(value msg) {
  call_coq_msg_info(msg);
  return Val_unit;
}

void call_coq_msg_debug(value msg)
{
  static const value * closure_f = NULL;
  if (closure_f == NULL) {
     /* First time around, look up by name */
    closure_f = caml_named_value("coq_msg_debug");
  }
  caml_callback(*closure_f, msg);
}

value print_msg_debug(value msg) {
  call_coq_msg_debug(msg);
  return Val_unit;
}
