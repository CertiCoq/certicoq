(* Freshen the names in a term by renaming its bound variables to be unique positives starting from a given positive, except for a finite number of positives *)

Require Import L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Require Import L6.shrink_cps.

  Definition state:Type := (positive * list positive).  (* n <= hd l *)

  
Fixpoint get_next (curr:positive) (l:list positive) : (positive * positive * list positive) :=
  match l with
  | nil => (curr, Pos.succ curr, nil)
  | hd::l' => 
    if (Pos.eqb curr hd) then
        get_next (Pos.succ curr) l'
    else
        (curr, Pos.succ curr, hd::l')
  end.

Fixpoint get_n_next (curr:positive) (l:list positive) (n:nat) : (list positive * positive * list positive ) :=
  match n with
  | 0 => ([], curr, l)
  | S n' => let '(x, curr, l) := get_next curr l in
            let '(xs, curr, l) := get_n_next curr l n' in
            (x::xs, curr, l)
  end.


(* TODO: move apply_r and apply_r_list to cps_util, and all_fun_name (and proofs) to identifiers *)
(* after freshen_term e sigma curr l = e', curr', l', BV(e') are in interval [curr, curr'[ and disjoint from l *)
Fixpoint freshen_term (e:exp) (sigma:M.t positive) (curr:positive) (l:list positive) : (exp * positive * list positive) :=
  match e with
  | Econstr x t ys e => let '(x', curr, l) := get_next curr l in
                        let ys' := apply_r_list sigma ys in
                        let '(e', curr, l) := freshen_term e (M.set x x' sigma) curr l in 
                        (Econstr x' t ys' e', curr, l)
  | Ecase v cl =>
    let '(cl', curr, l) :=
        (fix alpha_list (br: list (cTag*exp)) (curr:positive) (l:list positive): (list (cTag*exp) * positive * list positive) :=
           (match br with
            | nil => (nil, curr, l)
            | h::br' =>
              (match h with
               | (t, e) =>
                 let '(e', curr, l) := freshen_term e sigma curr l in
                 let '(br'', curr, l) := alpha_list br' curr l in
                 ((t, e')::br'', curr, l)
               end)
            end)) cl curr l in
    (Ecase (apply_r sigma v) cl', curr, l)    
  | Eproj x t n y e => let '(x', curr, l) := get_next curr l in
                       let y' := apply_r sigma y in
                        let '(e', curr, l) := freshen_term e (M.set x x' sigma) curr l in
                        (Eproj x' t n y' e', curr, l)
  | Efun fds e =>
    let f_names := all_fun_name fds in
    let '(f_names', curr, l) := get_n_next curr l (List.length f_names) in
    let sigma' := set_list (combine f_names f_names') sigma in
    let '(fds', curr, l) := freshen_fun fds sigma' curr l in
    let '(e', curr, l) := freshen_term e sigma' curr l in
    (Efun fds' e', curr, l)

  | Eapp f t ys =>
    let f' := apply_r sigma f  in
    let ys' := apply_r_list sigma ys in    
    (Eapp f' t ys', curr, l)
  | Eprim x t ys e =>
    let '(x', curr, l) := get_next curr l in
    let ys' := apply_r_list sigma ys in
    let '(e', curr, l) := freshen_term e (M.set x x' sigma) curr l in
    (Eprim x' t ys' e', curr, l)
  | Ehalt x =>
    let x' := apply_r sigma x in
    (Ehalt x', curr, l)
  end
with freshen_fun (fds:fundefs) (sigma:M.t positive) (curr:positive) (l:list positive) : (fundefs* positive * list positive) :=
       match fds with
       | Fcons f t xs e fds =>
         let f' := apply_r sigma f in
         let '(xs', curr, l) := get_n_next curr l (List.length xs) in
         let sigma' := set_list (combine xs xs') sigma in
         let '(e', curr, l) := freshen_term e sigma' curr l in
         let '(fds', curr, l) := freshen_fun fds sigma curr l in
         (Fcons f' t xs' e' fds', curr, l)
       | Fnil => (Fnil, curr, l)
       end.
         


