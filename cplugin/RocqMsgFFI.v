Require Import MetaRocq.Utils.bytestring.
From CertiRocq.VanillaPlugin Require Import Loader.

Axiom (rocq_msg_info : string -> unit).
Axiom (rocq_msg_notice : string -> unit).
Axiom (rocq_msg_debug : string -> unit).
Axiom (rocq_user_error : string -> unit).

CertiRocq Register [
  rocq_msg_info => "rocq_msg_info",
  rocq_msg_notice => "rocq_msg_notice",
  rocq_msg_debug => "rocq_msg_debug",
  rocq_user_error => "rocq_user_error" ]
Include [ Library "rocq_c_ffi.h" "coq_ffi.h" ].
