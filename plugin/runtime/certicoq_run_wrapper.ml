open Tm_util
open Pp
open Universes0
open BasicAst
open Ast0

external certicoq_run : unit -> Obj.t = "certicoq_run"

let info s = Feedback.msg_info (Pp.str s)

(** Run a program knowing it returns a value of the given type, 
    and reify the return value at that type. *)

let run (env : Ast0.Env.global_env) ~(typ : Ast0.term) : Obj.t =
  certicoq_run ()

let _ = Certicoq_plugin.Certicoq.register_certicoq_run "certicoq_run" (Obj.magic run)