
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

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

(** val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2 **)

let raise monadExc x =
  monadExc.raise __ x

(** val option_monad : __ option coq_Monad **)

let option_monad =
  { ret = (fun _ a -> Some a); bind = (fun _ _ m f ->
    match m with
    | Some a -> f a
    | None -> None) }

(** val monad_map : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let rec monad_map m f = function
| [] -> ret m []
| x :: l0 ->
  bind m (f x) (fun x' ->
    bind m (monad_map m f l0) (fun l' -> ret m (x' :: l')))
