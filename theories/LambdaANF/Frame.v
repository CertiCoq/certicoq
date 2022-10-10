(* One layer of a 1-hole context *)
Class Frame (U : Set) := {
  (* The type to poke holes in + all its transitive dependencies *)
  univD : U -> Set;
  (* Frames, indexed by hole type + root type *)
  frame_t : U -> U -> Set;
  (* Frame application *)
  frameD : forall {A B : U}, frame_t A B -> univD A -> univD B }.
