open Univ0

type t = LevelSet.t * ConstraintSet.t

(** val init_graph : t **)

let init_graph =
  let levels = LevelSet.add Level.prop (LevelSet.add Level.set LevelSet.empty)
  in
  let constraints =
    ConstraintSet.add ((Level.prop, ConstraintType.Lt), Level.set)
      ConstraintSet.empty
  in
  (levels, constraints)
