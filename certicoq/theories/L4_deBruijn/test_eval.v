
Require Import Template.Template.
Require Import Common.Common.
Require L3.L3.         (* whole L3 library is exported by L3.L3 *)
Require Import L3_to_L4.        
Require Import expression.

Local Open Scope bool.
Local Open Scope list.
Local Open Scope string_scope.
Set Template Cast Propositions.

(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0%nat => 0
    | S m => match m with
               | 0%nat => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
  Eval cbv in (program_exp cbv_slowFib3).
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval cbv in (program_exp p_slowFib3).
Definition eval_P_slowFib3 := Eval cbv in (eval_n 100 P_slowFib3).
Goal
  (eval_n 100 P_slowFib3) = Some ans_slowFib3.
  vm_compute. reflexivity.
Qed.

(* fast Fib *) 
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0%nat => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0%nat 1%nat).
Definition fib9 := fib 9%nat.
Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Definition ans_fib9 :=
  Eval cbv in (program_exp cbv_fib9).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_exp p_fib9).
Goal
  eval_n 1000%nat P_fib9 = Some ans_fib9.
  vm_compute. reflexivity.
Qed.

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.
Local Open Scope nat.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus _ v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
(* [Term] of Coq's answer *)
Definition ans_vplus0123 :=
  Eval cbv in (program_exp cbv_vplus0123).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_exp p_vplus0123).
Goal
  eval_n 100%nat P_vplus0123 = Some ans_vplus0123.
  reflexivity.
Qed.


(** mutual recursion **)
Set Implicit Arguments.
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.
Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in (program_exp cbv_arden_size).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Definition P_arden_size := Eval cbv in (program_exp p_arden_size).
Goal
  eval_n 100%nat P_arden_size = Some ans_arden_size.
  reflexivity.
Qed.


(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).
Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv in ack35) in exact t).
Definition ans_ack35 :=
  Eval cbv in (program_exp cbv_ack35).
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Definition P_ack35 := Eval cbv in (program_exp p_ack35).
Goal
  eval_n 2000%nat P_ack35 = Some ans_ack35.
  vm_compute. reflexivity.
Qed.

(** SASL tautology function: variable arity **)
Fixpoint tautArg (n:nat) : Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat) : tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).
Print cbv_pierce.
Definition ans_pierce :=
  Eval cbv in (program_exp cbv_pierce).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Definition P_pierce := Eval cbv in (program_exp p_pierce).
Goal
  eval_n 2000%nat P_pierce = Some ans_pierce.
  vm_compute. reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).
Definition ans_Scomb :=
  Eval cbv in (program_exp cbv_Scomb).
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Definition P_Scomb := Eval cbv in (program_exp p_Scomb).
Goal
  eval_n 2000%nat P_Scomb = Some ans_pierce.
  vm_compute. reflexivity.
Qed.

Require Import omega.Omega.
(** well founded definition **)
Function Gcd (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (Nat.modulo b (S k))  (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    omega.
  - exact lt_wf.
Defined.

Definition Gcdx := (Gcd 4 2).
Eval cbv in Gcdx.
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx := Eval cbv in (program_exp pGcdx).
Time Definition ans_Gcdx := Eval cbv in (eval_n 5000%nat PGcdx).
Print ans_Gcdx.


Require Import Benchmarks.vs.

(***  this works in my version ***
Time Quote Recursively Definition p_ce_example_myfail := vs.ce_example_myfail.
Time Definition P_ce_example_myfail :=
  Eval vm_compute in (program_exp p_ce_example_myfail).
Time Definition eval_ce_example_myfail :=
  Eval vm_compute in (expression.eval_n 5000 P_ce_example_myfail).
Print eval_ce_example_myfail.
 ***)

Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_exp p_ce_example_ent).

Time Definition eval_ce_example_ent :=
  Eval vm_compute in (expression.eval_n 5000 P_ce_example_ent).
Print eval_ce_example_ent.

