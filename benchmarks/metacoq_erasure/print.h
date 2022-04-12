#include <caml/mlvalues.h>

extern value print_msg_debug(value msg);
extern value print_msg_info(value msg);

// MetaCoq axiom
//PCUICTyping.FixCoFix -> PCUICAst.PCUICEnvironment.global_env_ext ->
// PCUICAst.PCUICEnvironment.context -> BasicAst.mfixpoint PCUICAst.term -> bool

extern value metacoq_guard_impl(value fixcofix, value globalenv, value context, value term);
