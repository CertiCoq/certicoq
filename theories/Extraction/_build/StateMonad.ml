open Monad0
open MonadState

type __ = Obj.t

type ('s, 't) state =
  's -> 't * 's
  (* singleton inductive, whose constructor was mkState *)

(** val runState : ('a1, 'a2) state -> 'a1 -> 'a2 * 'a1 **)

let runState s =
  s

(** val coq_Monad_state : ('a1, __) state coq_Monad **)

let coq_Monad_state =
  { ret = (fun _ v s -> (v, s)); bind = (fun _ _ c1 c2 s ->
    let (v, s0) = runState c1 s in runState (c2 v) s0) }

(** val coq_MonadState_state : ('a1, ('a1, __) state) coq_MonadState **)

let coq_MonadState_state =
  { get = (fun x -> ((Obj.magic x), x)); put = (fun v _ -> ((Obj.magic ()),
    v)) }
