open Bool
open Coqlib0
open Datatypes
open List0
open Nat0
open Cps

type live_fun =
| Live of var list list * bool list list

(** val bool_live : live_fun -> bool list list **)

let rec bool_live = function
| Live (_, bss) -> bss

(** val get_vars : fundefs -> var list list **)

let rec get_vars = function
| Fcons (_, _, xs, _, b') -> xs :: (get_vars b')
| Fnil -> []

(** val get_funs : fundefs -> var list **)

let rec get_funs = function
| Fcons (f, _, _, _, b') -> f :: (get_funs b')
| Fnil -> []

(** val get_bool_false : var list -> bool list **)

let rec get_bool_false = function
| [] -> []
| _ :: ys' -> false :: (get_bool_false ys')

(** val get_bool_true : var list -> bool list **)

let rec get_bool_true = function
| [] -> []
| _ :: ys' -> true :: (get_bool_true ys')

(** val get_bools : fundefs -> bool list list **)

let rec get_bools = function
| Fcons (_, _, ys, _, b') -> (get_bool_false ys) :: (get_bools b')
| Fnil -> []

(** val get_live_initial : fundefs -> live_fun **)

let rec get_live_initial b =
  let yss = get_vars b in let bss = get_bools b in Live (yss, bss)

(** val replace_nth : nat -> 'a1 list -> 'a1 -> 'a1 list **)

let rec replace_nth n ys x =
  match n with
  | O -> (match ys with
          | [] -> ys
          | _ :: ys' -> x :: ys')
  | S n' -> (match ys with
             | [] -> ys
             | y :: ys' -> y :: (replace_nth n' ys' x))

(** val find_fun : var -> var list -> nat -> bool * nat **)

let rec find_fun x funs n =
  match funs with
  | [] -> (false, n)
  | f :: funs' ->
    if peq f x then (true, n) else find_fun x funs' (add n (S O))

(** val add_escaping : var -> live_fun -> var list -> live_fun **)

let rec add_escaping x l funs =
  let (b, n) = find_fun x funs O in
  if b
  then let Live (yss, bss) = l in
       let ys = nth n yss [] in
       let bs = get_bool_true ys in
       let bss' = replace_nth n bss bs in Live (yss, bss')
  else l

(** val add_escapings' : var list -> live_fun -> var list -> live_fun **)

let rec add_escapings' xs l funs =
  match xs with
  | [] -> l
  | x :: xs' -> add_escapings' xs' (add_escaping x l funs) funs

(** val add_var_helper : var -> var list -> bool list -> bool list **)

let rec add_var_helper x ys bs =
  match ys with
  | [] -> bs
  | y :: ys' ->
    (match bs with
     | [] -> bs
     | b :: bs' ->
       if peq x y then true :: bs' else b :: (add_var_helper x ys' bs'))

(** val add_var : var -> live_fun -> nat -> live_fun **)

let rec add_var x l n =
  let Live (yss, bss) = l in
  let ys = nth n yss [] in
  let bs = nth n bss [] in
  let bs' = add_var_helper x ys bs in
  let bss' = replace_nth n bss bs' in Live (yss, bss')

(** val add_vars : var list -> live_fun -> nat -> live_fun **)

let rec add_vars xs l n =
  match xs with
  | [] -> l
  | x :: xs' -> add_vars xs' (add_var x l n) n

(** val add_fun_args :
    nat -> var list -> bool list -> live_fun -> live_fun **)

let rec add_fun_args n xs bs l =
  match xs with
  | [] -> l
  | x :: xs' ->
    (match bs with
     | [] -> l
     | b :: bs' ->
       if Bool.eqb b true
       then let l' = add_var x l n in add_fun_args n xs' bs' l'
       else add_fun_args n xs' bs' l)

(** val add_fun_vars :
    var -> var list -> var list -> live_fun -> nat -> live_fun **)

let rec add_fun_vars f funs xs l m =
  let (b, n) = find_fun f funs O in
  if b
  then let bss = bool_live l in
       let bs = nth n bss [] in add_fun_args m xs bs l
  else add_vars xs l m

(** val escaping_fun_exp : exp -> live_fun -> var list -> live_fun **)

let rec escaping_fun_exp e l funs =
  match e with
  | Econstr (_, _, ys, e') ->
    escaping_fun_exp e' (add_escapings' ys l funs) funs
  | Ecase (_, p) ->
    let rec mapM_LD l0 l1 =
      match l0 with
      | [] -> l1
      | p0 :: l' ->
        let (_, e') = p0 in
        let l'0 = escaping_fun_exp e' l1 funs in mapM_LD l' l'0
    in mapM_LD p l
  | Eproj (_, _, _, _, e') -> escaping_fun_exp e' l funs
  | Efun (_, _) -> l
  | Eapp (_, _, ys) -> add_escapings' ys l funs
  | Eprim (_, _, _, e') -> escaping_fun_exp e' l funs
  | Ehalt x -> add_escaping x l funs

(** val escaping_fun_fundefs : fundefs -> live_fun -> var list -> live_fun **)

let rec escaping_fun_fundefs b l funs =
  match b with
  | Fcons (_, _, _, e, b') ->
    let l' = escaping_fun_exp e l funs in escaping_fun_fundefs b' l' funs
  | Fnil -> l

(** val live_expr :
    fundefs -> live_fun -> var list -> nat -> exp -> live_fun **)

let rec live_expr b l funs n = function
| Econstr (_, _, ys, e') ->
  let l' = add_vars ys l n in live_expr b l' funs n e'
| Ecase (x, p) ->
  let l' = add_var x l n in
  let rec mapM_LD l0 l1 =
    match l0 with
    | [] -> l1
    | p0 :: l'0 ->
      let (_, e') = p0 in
      let l'1 = live_expr b l1 funs n e' in mapM_LD l'0 l'1
  in mapM_LD p l'
| Eproj (_, _, _, y, e') -> let l' = add_var y l n in live_expr b l' funs n e'
| Efun (_, _) -> l
| Eapp (f, _, ys) -> let l' = add_var f l n in add_fun_vars f funs ys l' n
| Eprim (_, f, ys, e') ->
  let l' = add_var f l n in
  let l'' = add_vars ys l' n in live_expr b l'' funs n e'
| Ehalt x -> add_var x l n

(** val live : fundefs -> live_fun -> var list -> nat -> live_fun **)

let rec live b l funs n =
  match b with
  | Fcons (_, _, _, e, b') ->
    let l' = live_expr b l funs n e in live b' l' funs (add n (S O))
  | Fnil -> l

(** val check_list_equality : bool list -> bool list -> bool **)

let rec check_list_equality l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | hd1 :: tl1 ->
    (match l2 with
     | [] -> false
     | hd2 :: tl2 ->
       if Bool.eqb hd1 hd2 then check_list_equality tl1 tl2 else false)

(** val check_list_list_equality :
    bool list list -> bool list list -> bool **)

let rec check_list_list_equality l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | hd1 :: tl1 ->
    (match l2 with
     | [] -> false
     | hd2 :: tl2 ->
       if check_list_equality hd1 hd2
       then check_list_list_equality tl1 tl2
       else false)

(** val live_equality : live_fun -> live_fun -> bool **)

let rec live_equality l1 l2 =
  let Live (_, bss1) = l1 in
  let Live (_, bss2) = l2 in check_list_list_equality bss1 bss2

(** val num_vars : fundefs -> nat -> nat **)

let rec num_vars b n =
  match b with
  | Fcons (_, _, xs, _, b') -> num_vars b' (add n (length xs))
  | Fnil -> n

(** val find_live_helper :
    fundefs -> live_fun -> var list -> nat -> live_fun **)

let rec find_live_helper b prev_L funs = function
| O -> prev_L
| S n' ->
  let curr_L = live b prev_L funs O in
  if live_equality prev_L curr_L
  then prev_L
  else find_live_helper b curr_L funs n'

(** val find_live : exp -> live_fun **)

let rec find_live = function
| Efun (b, e') ->
  let funs = get_funs b in
  let initial_L = get_live_initial b in
  let l' = escaping_fun_exp e' (escaping_fun_fundefs b initial_L funs) funs in
  let n = num_vars b O in find_live_helper b l' funs n
| _ -> Live (([] :: []), ([] :: []))

(** val live_args : var list -> bool list -> var list **)

let rec live_args ys bs =
  match ys with
  | [] -> ys
  | y :: ys' ->
    (match bs with
     | [] -> ys
     | b :: bs' ->
       if Bool.eqb b true then y :: (live_args ys' bs') else live_args ys' bs')

(** val eliminate_expr : live_fun -> var list -> exp -> exp **)

let rec eliminate_expr l funs e = match e with
| Econstr (x, t, ys, e') -> Econstr (x, t, ys, (eliminate_expr l funs e'))
| Ecase (x, p) ->
  let p' =
    let rec mapM_LD l0 = match l0 with
    | [] -> l0
    | p0 :: l' ->
      let (c', e') = p0 in (c', (eliminate_expr l funs e')) :: (mapM_LD l')
    in mapM_LD p
  in
  Ecase (x, p')
| Eproj (x, t, m, y, e') -> Eproj (x, t, m, y, (eliminate_expr l funs e'))
| Efun (_, _) -> e
| Eapp (f, t, ys) ->
  let (b, n) = find_fun f funs O in
  if b
  then let bss = bool_live l in
       let ys' = live_args ys (nth n bss []) in Eapp (f, t, ys')
  else Eapp (f, t, ys)
| Eprim (x, f, ys, e') -> Eprim (x, f, ys, (eliminate_expr l funs e'))
| Ehalt x -> Ehalt x

(** val eliminate_fundefs :
    fundefs -> live_fun -> var list -> nat -> fundefs **)

let rec eliminate_fundefs b l funs n =
  let Live (_, bss) = l in
  (match b with
   | Fcons (f, ft, ys, e, b') ->
     let ys' = live_args ys (nth n bss []) in
     let e' = eliminate_expr l funs e in
     Fcons (f, ft, ys', e', (eliminate_fundefs b' l funs (add n (S O))))
   | Fnil -> b)

(** val eliminate : exp -> exp **)

let rec eliminate e = match e with
| Efun (b, e') ->
  let funs = get_funs b in
  let l = find_live e in
  let b' = eliminate_fundefs b l funs O in
  let e'' = eliminate_expr l funs e' in Efun (b', e'')
| _ -> e
