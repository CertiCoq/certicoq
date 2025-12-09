#include <caml/mlvalues.h>

extern value coq_msg_debug(value msg);
extern value coq_msg_info(value msg);
extern value coq_user_error(value msg);

extern value metacoq_guard_impl(value fixcofix, value globalenv, value context, value term);
