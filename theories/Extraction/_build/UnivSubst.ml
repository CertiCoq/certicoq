open List0
open Univ0

(** val subst_instance_level : Level.t list -> Level.t -> Level.t **)

let subst_instance_level u l = match l with
| Level.Var n -> nth n u Level.Coq_lProp
| _ -> l

(** val subst_instance_level_expr :
    universe_instance -> Universe.Expr.t -> Level.t * bool **)

let subst_instance_level_expr u = function
| (l, b) -> ((subst_instance_level u l), b)

(** val subst_instance_univ :
    universe_instance -> universe -> (Level.t * bool) list **)

let subst_instance_univ u s =
  map (subst_instance_level_expr u) s

(** val subst_instance_instance :
    universe_instance -> universe_instance -> Level.t list **)

let subst_instance_instance u u' =
  map (subst_instance_level u) u'
