(* Freshen the names in a term by renaming its bound variables to be unique positives starting from a given positive, except for a finite number of positives *)

Require Import L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.Strings.Ascii.
Import ListNotations.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import L6.shrink_cps L6.cps_util L6.cps_util L6.cps_show.

Open Scope monad_scope.
Import MonadNotation.

Definition freshM : Type -> Type := state (positive * nEnv * list string).


Definition log_msg (msg : string) : freshM unit :=
  s <- get ;;
  let '(p, name, msgs) := s in
  put (p, name, msg::msgs).

Definition chr_newline : ascii := Eval compute in ascii_of_nat 10.
Definition newline : string := (String chr_newline EmptyString).

Definition log_to_string (log : list string) :=
  (concat "" ("Debug messages" :: newline :: (List.rev log)))%string.

Fixpoint get_next (old : var) : freshM var :=
  s <- get ;;
  let '(curr, names, log) := s in
  let names' := add_entry names curr old "" in
  _ <- put ((curr + 1)%positive, names', log);; ret curr.

Fixpoint get_next_lst (old : list var) : freshM (list var) :=
  match old with
  | [] => ret []
  | o :: os =>
    x <- get_next o ;;
    xs <- get_next_lst os ;;
    ret (x :: xs)
  end.


(* TODO: move apply_r and apply_r_list to cps_util, and all_fun_name (and proofs) to identifiers *)
(* after freshen_term e sigma curr l = e', curr', l', BV(e') are in interval [curr, curr'[ and disjoint from l *)


Fixpoint freshen_term (e:exp) (sigma:M.t positive) : freshM exp :=
  match e with
  | Econstr x t ys e =>
    x' <- get_next x ;;
    let ys' := apply_r_list sigma ys in
    e' <- freshen_term e (M.set x x' sigma) ;; 
    ret (Econstr x' t ys' e')
  | Ecase v cl =>
    cl' <- (fix alpha_list (pats: list (cTag*exp)) : freshM (list (cTag*exp)) :=
             match pats with
             | nil => ret nil
             | pat::pats =>
               let '(t, e) := pat in
               e' <- freshen_term e sigma ;;
               pats' <- alpha_list pats ;;
               ret ((t, e')::pats')
             end) cl ;;
     ret (Ecase (apply_r sigma v) cl')    
  | Eproj x t n y e =>
    x' <- get_next x ;;
    let y' := apply_r sigma y in
    e' <- freshen_term e (M.set x x' sigma) ;; 
    ret (Eproj x' t n y' e')
  | Efun fds e =>
    let f_names := all_fun_name fds in
    f_names' <- get_next_lst f_names ;;
    (match @setlist var f_names f_names' sigma with
     | Some sigma' =>
       fds' <- freshen_fun fds sigma' ;;
       e' <- freshen_term e sigma' ;;
       ret (Efun fds' e')
     | None => (* unreachable *)
       ret (Efun Fnil e)
     end)
  | Eapp f t ys =>
    let f' := apply_r sigma f  in
    let ys' := apply_r_list sigma ys in    
    ret (Eapp f' t ys')
  | Eprim x t ys e =>
    x' <- get_next x ;;
    let ys' := apply_r_list sigma ys in
    e' <- freshen_term e (M.set x x' sigma) ;; 
    ret (Eprim x' t ys' e')
  | Ehalt x =>
    let x' := apply_r sigma x in
    ret (Ehalt x')
  end
with freshen_fun (fds:fundefs) (sigma:M.t positive) : freshM fundefs :=
       match fds with
       | Fcons f t xs e fds =>
         let f' := apply_r sigma f in
         xs' <- get_next_lst xs ;;
         (match @setlist var xs xs' sigma with
          | Some sigma' =>
            e' <- freshen_term e sigma' ;;
            fds' <- freshen_fun fds sigma ;;
            ret (Fcons f' t xs' e' fds')
          | None => (* unreachable *)
            ret Fnil
          end)
       | Fnil => ret Fnil
       end.


Definition freshen_subexp (e: exp) (next : var) (names: nEnv) : exp * var * nEnv :=
  let st := (next, names, []) in
  let '(e', (next', names', _)) := runState (freshen_term e (M.empty _)) st in
  (e', next', names').

Definition freshen_top (e: exp) (names: nEnv) : exp * nEnv :=
  let next := ((identifiers.max_var e 1) + 1)%positive in
  let st := (next, names, []) in
  let '(e', (next', names', _)) := runState (freshen_term e (M.empty _)) st in
  (e', names').


(* Some unit tests *)
Definition test :=
  (Efun (Fcons 1 2 [3] (Ehalt 3) Fnil)
  (Efun (Fcons 1 2 [3] (Ehalt 3) Fnil) (Ehalt 1)))%positive.

Definition testf := Eval native_compute in (freshen_top test (M.empty _)).

Definition test2 :=
  (Econstr 1 2 [3; 4] (Econstr 1 2 [3; 4] (Ehalt 1)))%positive.

Definition testf2 := Eval native_compute in (freshen_top test2 (M.empty _)).
