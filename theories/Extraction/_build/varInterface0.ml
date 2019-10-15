open BasicAst

type 't coq_UpdateName = ('t * name) -> 't

(** val updateName : 'a1 coq_UpdateName -> ('a1 * name) -> 'a1 **)

let updateName updateName0 =
  updateName0
