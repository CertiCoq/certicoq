
type __ = Obj.t

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 coq_Monad -> 'a2 -> 'a1

val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

type 'm coq_PMonad = { pret : (__ -> __ -> __ -> 'm);
                       pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) coq_MonP = __

val pbind :
  'a1 coq_PMonad -> ('a1, 'a3) coq_MonP -> 'a1 -> ('a2 -> 'a1) -> 'a1

val coq_PMonad_Monad : 'a1 coq_Monad -> 'a1 coq_PMonad
