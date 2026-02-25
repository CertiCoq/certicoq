
type unit0 =
| Tt

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t) -> fold_left f t (f a0 b)

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> Nil
| S k -> Cons (x, (repeat x k))

(** val list_sum : unit0 -> nat **)

let list_sum _ =
  fold_left add
    (repeat (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    O
