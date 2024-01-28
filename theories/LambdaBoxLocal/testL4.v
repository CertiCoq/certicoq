
Require Import Recdef.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Common.Common.
Require Import LambdaBoxLocal.expression LambdaBoxMut_to_LambdaBoxLocal.

Require Import TemplateExtraction.EAst Template.kernel.univ.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Set Printing Width 80.
Set Printing Depth 1000.

#[global] Instance fuel : utils.Fuel := { fuel := 2 ^ 14 }.

Quote Recursively Definition p_Type := Type.
Print p_Type.
Definition P_Type := Eval cbv in (program_exp p_Type).
Print P_Type.

(** test eta expansion: constructor expecting 1 arg and 0 params **)
Inductive etaC01 := EtaC01 : forall b:bool, etaC01.
Quote Recursively Definition p_etaC01 := EtaC01.
Definition P_etaC01 := Eval cbv in (program_exp p_etaC01).
Print P_etaC01.

Inductive DD := D2: bool -> bool -> DD.
Quote Recursively Definition p_etaTst := (D2 true false).
Print p_etaTst.
Definition P_etaTst := Eval cbv in (program_exp p_etaTst).
Print P_etaTst.
Compute eval_n 10 P_etaTst.
Quote Recursively Definition p_LetaTst := (fun (x:bool) => (D2 true x)).
Print p_LetaTst.
Definition P_LetaTst := Eval cbv in (program_exp p_LetaTst).
Print P_LetaTst.
Compute eval_n 10 P_LetaTst.


(** trivial example **)
Definition one := 1.
Quote Recursively Definition cbv_one := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (one)) in exact t).
Print cbv_one.
(* [Term] of Coq's answer *)
Definition ans_one := Eval cbv in (program_exp cbv_one).
Print ans_one.
(* [program] of the program *)
Quote Recursively Definition p_one := one.
Print p_one.
Definition P_one := Eval cbv in (program_exp p_one).
Print P_one.
Goal
  eval_n 100 P_one = Some ans_one.
  vm_compute. reflexivity.
Qed.

Definition ten := 10.
Quote Recursively Definition cbv_ten := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (ten)) in exact t).
Print cbv_ten.
(* [Term] of Coq's answer *)
Definition ans_ten := Eval cbv in ( (program_exp cbv_ten)).
Print ans_ten.
(* [program] of the program *)
Quote Recursively Definition p_ten := ten.
Print p_ten.
Definition P_ten := Eval cbv in (program_exp p_ten).
Print P_ten.
Goal
  eval_n 20 P_ten = Some ans_ten.
  vm_compute. reflexivity.
Qed.

Definition plus01 := (plus 0 1).
Quote Recursively Definition cbv_plus01 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus01)) in exact t).
Print cbv_plus01.
(* [Term] of Coq's answer *)
Definition ans_plus01 := Eval cbv in (program_exp cbv_plus01).
Print ans_plus01.
(* [program] of the program *)
Quote Recursively Definition p_plus01 := plus01.
Print p_plus01.
Require Import LambdaBoxMut_to_LambdaBoxMut_eta.
Eval compute in program_LambdaBoxMut_eta p_plus01.

Definition P_plus01 := Eval cbv in (program_exp p_plus01).
Print P_plus01.
Goal
  eval_n 20 P_plus01 = Some ans_plus01.
Proof.
  cbv. reflexivity.
Qed.

Definition plus10 := (plus 1 0).
Quote Recursively Definition cbv_plus10 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus10)) in exact t).
Print cbv_plus10.
(* [Term] of Coq's answer *)
Definition ans_plus10 := Eval cbv in( (program_exp cbv_plus10)).
Print ans_plus10.
(* [program] of the program *)
Quote Recursively Definition p_plus10 := plus10.
Print p_plus10.
Definition P_plus10 := Eval cbv in (program_exp p_plus10).
Print P_plus10.
Goal
  eval_n 20 P_plus10 = Some ans_plus10.
Proof.
  vm_compute. reflexivity.
Qed.

Definition plus98 := (plus 9 8).
Quote Recursively Definition cbv_plus98 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (plus98)) in exact t).
Print cbv_plus98.
(* [Term] of Coq's answer *)
Definition ans_plus98 := Eval cbv in( (program_exp cbv_plus98)).
Print ans_plus98.
(* [program] of the program *)
Quote Recursively Definition p_plus98 := plus98.
Print p_plus98.
Definition P_plus98 := Eval cbv in (program_exp p_plus98).
Print P_plus98.
Goal
  eval_n 100P_plus98 = Some ans_plus98.
Proof.
  vm_compute. reflexivity.
Qed.

(** nested Let **)
Definition nestedLet := let x := 0 in let y := 1 in let z := 2 in y.
Quote Recursively Definition cbv_nestedLet := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in nestedLet) in exact t).
Print cbv_nestedLet.
(* [Term] of Coq's answer *)
Definition ans_nestedLet := Eval cbv in (program_exp cbv_nestedLet).
Print ans_nestedLet.
(* [program] of the program *)
Quote Recursively Definition p_nestedLet := nestedLet.
Print p_nestedLet.
Definition P_nestedLet := Eval cbv in (program_exp p_nestedLet).
Print P_nestedLet.
Goal
  eval_n 100 P_nestedLet = Some ans_nestedLet.
Proof.
  vm_compute. reflexivity.
Qed.

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0%nat 1%nat (Vector.cons nat 1%nat 0%nat (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2%nat 1%nat (Vector.cons nat 3%nat 0%nat (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
Print cbv_vplus0123.
(* [Term] of Coq's answer *)
Definition ans_vplus0123 := Eval cbv in( (program_exp cbv_vplus0123)).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_exp p_vplus0123).
Print P_vplus0123.
Goal
  eval_n 100 P_vplus0123 = Some ans_vplus0123.
  vm_compute. reflexivity.
Qed.

(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0%nat => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0%nat => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3%nat 5%nat).
Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv in ack35) in exact t).
Print cbv_ack35.
Definition ans_ack35 :=
  Eval cbv in( (program_exp cbv_ack35)).
Print ans_ack35.
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Print p_ack35.
Definition P_ack35 := Eval cbv in (program_exp p_ack35).
Print P_ack35.
Goal
  eval_n 2000 P_ack35 = Some ans_ack35.
  vm_compute. reflexivity.
Qed.

(** mutual recursion **)
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.

Definition sf: forest bool := (fcons (node true (leaf false)) (leaf true)).
Quote Recursively Definition p_sf := sf.
Eval cbv in (program_exp p_sf).

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
Quote Recursively Definition p_arden := arden.
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in( (program_exp cbv_arden_size)).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Print p_arden_size.
Definition P_arden_size := Eval cbv in (program_exp p_arden_size).
Print P_arden_size.
Goal
  eval_n 50 P_arden_size = Some ans_arden_size.
  vm_compute. reflexivity.
Qed.

Open Scope nat_scope.
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
  Eval cbv in( (program_exp cbv_pierce)).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Print p_pierce.
Definition P_pierce := Eval cbv in (program_exp p_pierce).
Print P_pierce.
Goal
  eval_n 200 P_pierce = Some ans_pierce.
  vm_compute. reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).
Print cbv_Scomb.
Definition ans_Scomb :=
  Eval cbv in( (program_exp cbv_Scomb)).
Print ans_Scomb.
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Print p_Scomb.
Definition P_Scomb := Eval cbv in (program_exp p_Scomb).
Print P_Scomb.
Goal
  eval_n 200 P_Scomb = Some ans_pierce.
  vm_compute. reflexivity.
Qed.

(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
  Eval cbv in( (program_exp cbv_slowFib3)).
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval cbv in (program_exp p_slowFib3).
Goal
  eval_n 30 P_slowFib3 = Some ans_slowFib3.
  vm_compute. reflexivity.
Qed.

(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Definition ans_fib9 :=
  Eval cbv in( (program_exp cbv_fib9)).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_exp p_fib9).
Goal
  eval_n 1000 P_fib9 = Some ans_fib9.
  vm_compute. reflexivity.
Qed.

(** Heterogenous datatypes, a la Matthes **)
Inductive PList : Set->Type:=  (* powerlists *)
| zero : forall A:Set, A -> PList A
| succ : forall A:Set, PList (A * A)%type -> PList A.

Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).

Fixpoint unzip (A:Set) (l:list (A*A)) {struct l} : list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList (A:Set) (l:PList A) {struct l} : list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Eval compute in PListToList myPList.

Fixpoint gen_sumPList (A:Set) (l:PList A) {struct l} : (A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval cbv in( (program_exp cbv_sumPL_myPL)).
(* [program] of the program *)
Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval cbv in (program_exp p_sumPL_myPL).
Goal
  eval_n 1000 P_sumPL_myPL = Some ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.

Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Fixpoint fold (y : Y) (xs : list X) : Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T : list Tree -> Tree.
Fixpoint size (t : Tree) : nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
Definition myTree :=
  (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).
Eval cbv in size myTree.
Definition size_myTree := size myTree.
Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval cbv in( (program_exp cbv_size_myTree)).
(* [program] of the program *)
Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval cbv in (program_exp p_size_myTree).
Goal
  eval_n 100 P_size_myTree = Some ans_size_myTree.
  vm_compute. reflexivity.
Qed.


Function provedCopy (n:nat) {wf lt n} :=
  match n with 0 => 0 | S k => S (provedCopy k) end.
Proof.
  - intros. constructor.
  - apply lt_wf.
Defined.
Quote Recursively Definition pCopy := provedCopy. (* program *)
Print provedCopy_tcc.
Definition x := 4.
Definition provedCopyx := provedCopy x.
Compute provedCopyx.  (** evals correctly in Coq **)
Quote Recursively Definition cbv_provedCopyx :=
  ltac:(let t:=(eval cbv in provedCopyx) in exact t).
Definition ans_provedCopyx :=
  Eval cbv in( (program_exp cbv_provedCopyx)).
Quote Recursively Definition p_provedCopyx := provedCopyx. (* program *)
Definition P_provedCopyx :=                            (* Program *)
  Eval cbv in (program_exp p_provedCopyx).
Goal
  eval_n 600 P_provedCopyx = Some ans_provedCopyx.
  vm_compute. reflexivity.
Qed.

(****** Binomial ******)
Require Import Benchmarks.Binom.

Quote Recursively Definition binom := Binom.main.
Definition binom_exp := Eval native_compute in (program_exp binom).

Definition eval_c5 := eval_n 2000%nat binom_exp.
Definition value_binom := Eval native_compute in Binom.main.
Quote Recursively Definition reified_value_binom := value_binom.
Definition ans_binom5 := Eval cbv in (eval_n 1000%nat (program_exp reified_value_binom)).
Goal eval_n 1000%nat binom_exp = ans_binom5.
Proof.
  vm_compute. reflexivity.
Qed.

(****** veriStar benchmark **************)
Require Import Benchmarks.vs.
Quote Recursively Definition p_Valid := vs.VeriStar.Valid.
Definition valid : option exp :=
  Eval vm_compute in (eval_n 100 (program_exp p_Valid)).
Print valid.

(* Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent. *)
(* Time Definition P_ce_example_myent := *)
(*   Eval vm_compute in (program_exp p_ce_example_myent). *)
(* Time Definition eval_ce_example_myent := *)
(*   Eval native_compute in (eval_n 1000 P_ce_example_myent). *)
(* Goal eval_ce_example_myent = valid. *)
(*   vm_compute. reflexivity.  *)
(* Qed. *)

Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_exp p_ce_example_ent).
Time Definition eval_ce_example_ent :=
  Eval vm_compute in (eval_n 2000 P_ce_example_ent).
Goal eval_ce_example_ent = valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example1_myent := vs.ce_example1_myent.
Time Definition P_ce_example1_myent :=
  Eval vm_compute in (program_exp p_ce_example1_myent).
Time Definition eval_ce_example1_myent :=
  Eval vm_compute in (eval_n 1000 P_ce_example1_myent).
Goal eval_ce_example1_myent =  valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example2_myent := vs.ce_example2_myent.
Time Definition P_ce_example2_myent :=
  Eval vm_compute in (program_exp p_ce_example2_myent).
Time Definition eval_ce_example2_myent :=
  Eval vm_compute in (eval_n 2000 P_ce_example2_myent).
Goal eval_ce_example2_myent = valid.
  vm_compute. reflexivity. 
Qed.

Time Quote Recursively Definition p_ce_example1_myfail := vs.ce_example1_myfail.
Time Definition P_ce_example1_myfail :=
  Eval vm_compute in (program_exp p_ce_example1_myfail).
Time Definition eval_ce_example1_myfail :=
  Eval vm_compute in (eval_n 2000 P_ce_example1_myfail).
Print eval_ce_example1_myfail.

Time Quote Recursively Definition p_ce_example2_myfail := vs.ce_example2_myfail.
Time Definition P_ce_example2_myfail :=
  Eval vm_compute in (program_exp p_ce_example2_myfail).
Time Definition eval_ce_example2_myfail :=
  Eval vm_compute in (eval_n 2000 P_ce_example2_myfail).
Print eval_ce_example1_myfail.
