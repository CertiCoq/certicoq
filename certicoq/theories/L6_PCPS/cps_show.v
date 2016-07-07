(** Pretty printer for L6 CPS language.  

    [show_exp e] constructs a string representing the term that has some 
    minimal formatting so that it's much more readable.
*)
Require Import List.
Require Import String.
Require Import cps.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.

(* Convert various numbers to strings *)
Definition show_nat := nat2string10.
Definition show_pos x := nat2string10 (Pos.to_nat x).
Definition show_binnat x := nat2string10 (BinNat.N.to_nat x).

(* Add a separator [s] inbetween each element of a list [xs] *)
Fixpoint sep {A} (s:A) (xs:list A) : list A :=
  match xs with
  | nil => nil
  | h::nil => h::nil
  | h::t => h :: s :: (sep s t)
  end.

(* It's too expensive to append strings everywhere, so we 
   accumulate a tree and then flatten it once to avoid this
   quadratic overhead. *)
Inductive string_tree :=
| Emp : string_tree
| Str : string -> string_tree
| App : string_tree -> string_tree -> string_tree.

Local Coercion Str : string >-> string_tree.

Infix "+++" := App (at level 100).

Fixpoint show_tree_c (t : string_tree) (acc : string) : string :=
  match t with
  | Emp => acc
  | App t1 t2 => show_tree_c t1 (show_tree_c t2 acc)
  | Str s => (s ++ acc)
  end.

Definition show_tree t := (show_tree_c t "")%string.

(* Variables are shown using "x" as a prefix *)
Definition show_var (x:positive) := ("x" +++ (show_pos x))%string.

(* Show a list of variables as comma separated and wrapped in parens. *)
Definition show_vars (xs:list positive) :=
  ("(" +++ (List.fold_right (fun x y => x +++ y) ""
                            (sep (",":string_tree) (List.map show_var xs))) +++ ")")%string.

(* We accumulate a string_tree as we convert the expressions to strings. *)
Definition M := state string_tree.
Import MonadNotation.

Definition emit (s:string_tree) : M unit :=
  st <- get ;;
  put (App st s).

Fixpoint tab (n:nat) : M unit :=
  match n with
  | 0 => ret tt
  | S n => emit " "%string ;; tab n
  end.

(* Might need to add linefeed for windows? *)
Definition chr_newline : ascii := Eval compute in ascii_of_nat 10.

Definition newline : M unit := emit (String chr_newline EmptyString).

(* We assume each expression starts on a fresh newline, and that it
   should be indented by [indent] characters. *)
Fixpoint emit_exp (indent:nat) (e:exp) : M unit :=
  tab indent ;; 
  match e with
  | Econstr x ty tg xs e =>
    emit "let " ;; emit (show_var x) ;;
    emit " := con_" ;; emit (show_pos tg) ;;
    emit (show_vars xs) ;; emit " in " ;; newline ;; 
    emit_exp indent e
  | Eproj x ty n y e =>
    emit "let " ;; emit (show_var x) ;;
    emit ":= proj_" ;; emit (show_binnat n) ;; emit " " ;;
    emit (show_var y) ;; emit" in " ;; newline ;; 
    emit_exp indent e
  | Eprim x ty p ys e =>
    emit "let " ;; emit (show_var x) ;;
    emit ":= prim_" ;; emit (show_pos p) ;; emit (show_vars ys) ;;
    emit " in " ;; newline ;; 
    emit_exp indent e
  | Ecase x arms =>
    emit "case " ;; emit (show_var x) ;; emit " of {" ;; newline ;;
         (fix iter (xs : list (tag*exp)) : M unit :=
            match xs with
            | nil => ret tt
            | p::tail =>
              let (tg,e) := p in
              tab indent ;; emit "| con_" ;; emit (show_pos tg) ;;
                  emit " => " ;; newline ;; 
                  emit_exp (2 + indent) e ;; 
                  iter tail
            end) arms ;;
         tab indent ;; emit "}" ;; newline 
  | Efun fds e =>
    emit "letrec [" ;; newline ;; 
         (fix iter (fds : fundefs) : M unit :=
            match fds with
            | Fnil => ret tt
            | Fcons x _ xs e fds' =>
              tab (2 + indent) ;;
              emit "fun " ;; emit (show_var x) ;;
                   emit (show_vars xs) ;; emit " := " ;; newline ;;
                   emit_exp (4 + indent) e ;;
                   iter fds'
            end) fds ;;
         tab indent ;; emit "] in" ;; newline ;; emit_exp indent e
  | Eapp x ys => emit (show_var x) ;; emit (show_vars ys) ;; newline
  end%string.

(* We add an extra newline at the front so that Coq will display the
   whole program correctly when we evaluate. *)
Definition show_exp (x:exp) : string := 
  String chr_newline
          (show_tree (snd (runState (emit_exp 0 x) Emp))).

(*  Some tests -- commented out for now. *)
(*
Require Import L5_to_L6.

Let P1 := 
  (Efun
     (Fcons 10 L5_to_L6.ty_con (13 :: nil)
        (Efun
           (Fcons 5 L5_to_L6.ty_con
              (11 :: 12 :: nil)
              (Eapp 15 (11 :: 12 :: nil)) Fnil)
           (Eapp 13 (14 :: nil)))
        (Fcons 15 L5_to_L6.ty_con (6 :: 7 :: nil)
           (Eapp 6 nil) Fnil))
     (Eapp 2 (10 :: nil)))%positive.

Eval vm_compute in show_exp P1.

Let P2 := 
(Efun
     (Fcons 32 L5_to_L6.ty_con (3 :: nil)
        (Efun
           (Fcons 10 L5_to_L6.ty_con (4 :: nil)
              (Efun
                 (Fcons 9 L5_to_L6.ty_fun
                    (5 :: 6 :: nil)
                    (Efun
                       (Fcons 8 L5_to_L6.ty_con 
                          (7 :: nil)
                          (Eapp 7 (5 :: nil)) Fnil)
                       (Eapp 8 (6 :: nil))) Fnil)
                 (Eapp 4 (9 :: nil))) Fnil)
           (Efun
              (Fcons 31 L5_to_L6.ty_con (11 :: nil)
                 (Efun
                    (Fcons 28 L5_to_L6.ty_con 
                       (12 :: nil)
                       (Efun
                          (Fcons 27 L5_to_L6.ty_fun
                             (13 :: 14 :: nil)
                             (Efun
                                (Fcons 26 L5_to_L6.ty_con
                                   (15 :: nil)
                                   (Efun
                                      (Fcons 17 L5_to_L6.ty_con
                                         (16 :: nil)
                                         (Eapp 16
                                            (13 :: nil)) Fnil)
                                      (Efun
                                         (Fcons 25 L5_to_L6.ty_con
                                            (18 :: nil)
                                            (Ecase 18
                                               ((1,
                                                Efun
                                                 (Fcons 24
                                                 L5_to_L6.ty_con
                                                 (23 :: nil)
                                                 (Eapp 23
                                                 (1 :: nil)) Fnil)
                                                 (Eapp 24
                                                 (15 :: nil)))
                                                :: 
                                                (2,
                                                Eproj 19 L5_to_L6.ty
                                                 0 18
                                                 (Efun
                                                 (Fcons 22
                                                 L5_to_L6.ty_con
                                                 (20 :: nil)
                                                 (Econstr 21
                                                 L5_to_L6.ty 1 nil
                                                 (Eapp 20
                                                 (21 :: nil))) Fnil)
                                                 (Eapp 22
                                                 (15 :: nil))))
                                                :: nil)) Fnil)
                                         (Eapp 17
                                            (25 :: nil)))) Fnil)
                                (Eapp 26 (14 :: nil))) Fnil)
                          (Eapp 12 (27 :: nil))) Fnil)
                    (Efun
                       (Fcons 30 L5_to_L6.ty_con
                          (29 :: nil)
                          (Eapp 1 (1 :: 3 :: nil))
                          Fnil) (Eapp 28 (30 :: nil))))
                 Fnil) (Eapp 10 (31 :: nil)))) Fnil)
     (Eapp 2 (32 :: nil)))%positive.

Eval vm_compute in show_exp P2.
*)