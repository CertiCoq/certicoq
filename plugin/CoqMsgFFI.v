Require Import MetaCoq.Utils.bytestring.
From CertiCoq.Plugin Require Import Loader.

Axiom (coq_msg_info : string -> unit).
Axiom (coq_msg_notice : string -> unit).
Axiom (coq_msg_debug : string -> unit).
Axiom (coq_user_error : string -> unit).

CertiCoq Register [ 
  coq_msg_info => "coq_msg_info",
  coq_msg_notice => "coq_msg_notice",
  coq_msg_debug => "coq_msg_debug",
  coq_user_error => "coq_user_error" ]
Include [ Library "coq_c_ffi.h" "coq_ffi.h" ].
