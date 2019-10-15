
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let ret monad x =
  let { ret = ret0; bind = _ } = monad in Obj.magic ret0 __ x

(** val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad x x0 =
  let { ret = _; bind = bind0 } = monad in Obj.magic bind0 __ __ x x0

type 'm coq_PMonad = { pret : (__ -> __ -> __ -> 'm);
                       pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) coq_MonP = __

(** val pbind :
    'a1 coq_PMonad -> ('a1, 'a3) coq_MonP -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let pbind pMonad pu x x0 =
  let { pret = _; pbind = pbind0 } = pMonad in Obj.magic pbind0 __ __ pu x x0

(** val coq_PMonad_Monad : 'a1 coq_Monad -> 'a1 coq_PMonad **)

let coq_PMonad_Monad m =
  { pret = (fun _ -> Obj.magic (fun _ x -> ret m x)); pbind = (fun _ _ ->
    Obj.magic (fun _ c f -> bind m c f)) }
