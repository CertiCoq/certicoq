
type __ = Obj.t

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 coq_Monad -> 'a2 -> 'a1

val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2

val option_monad : __ option coq_Monad

val monad_map : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1
