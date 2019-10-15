open List0
open Univ0

val subst_instance_level : Level.t list -> Level.t -> Level.t

val subst_instance_level_expr :
  universe_instance -> Universe.Expr.t -> Level.t * bool

val subst_instance_univ :
  universe_instance -> universe -> (Level.t * bool) list

val subst_instance_instance :
  universe_instance -> universe_instance -> Level.t list
