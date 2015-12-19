Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "." as L2.

Require Import Template.Template.
Require Import Common.RandyPrelude.
Require Import L1.L1.  (* whole L1 library is exported by L1.L1 *)
Require Import L2.L2.  (* whole L2 library is exported by L2.L2 *)

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** a tool for testing **)
Definition exc_wcbvEval (tmr:nat) (pgm:program): option Term :=
  match program_Program pgm with
    | None => None
    | Some pgm => wcbvEval tmr (L2.program.env pgm) (L2.program.main pgm)
  end.

Inductive foo (A:Set) : Set :=
| nilf: foo A
| consf: (fun (Y W:Set) => Y -> foo Y -> foo ((fun X Z => X) A nat)) A bool.
Quote Recursively Definition foo_nat_cons := (@consf nat 0 (nilf nat)).
Print foo_nat_cons.

Fixpoint foo_list (A:Set) (fs:foo A) : list A :=
  match fs with
    | nilf _ => nil
    | consf b bs => cons b (foo_list bs)
  end.
Fixpoint list_foo (A:Set) (fs:list A) : foo A :=
  match fs with
    | nil => nilf A
    | cons b bs => consf b (list_foo bs)
  end.
Goal forall (A:Set) (fs:list A), foo_list (list_foo fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.
Goal forall (A:Set) (fs:foo A), list_foo (foo_list fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.

(** Abishek's example **)
Axiom feq1 : (fun x:nat => x) = (fun x:nat => x+x-x).

Definition zero :nat :=
  match feq1 with
    | eq_refl => 0
  end.

Quote Recursively Definition p_zero := zero.
Quote Definition q_zero := Eval compute in zero.
Goal (exc_wcbvEval 40 p_zero) = term_Term q_zero.
compute. reflexivity.
Qed.


(** type casting ? **)
Check (cons: forall (A:Set), A -> list A -> list A).
Check ((fun A : Set => cons (A:=A)) : forall (A:Set), A -> list A -> list A).
Quote Definition qconsa := (cons: forall (A:Set), A -> list A -> list A).
Print qconsa.
(**
Goal True.   -- Not equal
constr_eq (cons: forall (A:Set), A -> list A -> list A) cons.
**)
Goal (cons: forall (A:Set), A -> list A -> list A) =
     (cons: forall (A:Set), A -> list A -> list A).
cbv beta.
Abort.

Goal (cons: forall (A:Set), A -> list A -> list A) = cons.
reflexivity.
Qed.

Check cons.
Check (cons: forall (A:Set), A -> list A -> list A).
Check (cons Type).
(* fails
Check ((cons: forall (A:Set), A -> list A -> list A) Type).
*)

Goal (cons: forall (A:Set), A -> list A -> list A) = cons.
simpl. reflexivity.
Qed.
Quote Definition qconsA := (cons: forall (A:Set), (A:Set) -> list A -> list A).
Print qconsA.
Quote Definition qconsb :=
  (cons: forall (A:Type), (A:Type) -> list A -> list A).
Print qconsb.

Unset Implicit Arguments.
Inductive list2 (A B:Type) : Type :=
| nil2 : list2 A B
| cons2 : A -> B -> list2 A B.

Definition cons2' :=
  (cons2: forall (A:Set) (B:Type), A -> B -> list2 A B).
Print cons2'.
Goal (cons2: forall (A:Set) (B:Type), A -> B -> list2 A B ) = cons2.
Abort.

Definition T0 := Type.
Definition T1 := Type.
Check (T0 : Type).
Check (Type : T0).

Check ((fun (A:Type) (a:A) => a)
         (forall (A:Type), A -> A)
         (fun (A:Type) (a:A) => a)).
(****
Definition qconsA := (cons: forall (A:Set), (A:Set) -> list A -> list A).
Print qconsA.
Quote Definition qconsb :=
  (cons: forall (A:Type), (A:Type) -> list A -> list A).
Print qconsb.
Quote Definition qconsc :=
  (cons: forall (A:Set), (A:Type) -> list A -> list A).
Print qconsc.

Quote Definition AppApp1 := ((@cons nat:nat -> list nat -> list nat) 0).
Print AppApp1.
Quote Definition AppApp2 :=
  Eval compute in ((@cons nat:nat -> list nat -> list nat) 0).
Print AppApp2.
***)

Set Implicit Arguments.
Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Definition q_typedef := Eval compute in typedef.
Quote Recursively Definition p_typedef := typedef.
Goal (exc_wcbvEval 20 p_typedef) = (term_Term q_typedef).
reflexivity.
Qed.

Definition II := fun (A:Type) (a:A) => a.
Quote Definition q_II := Eval compute in II.
Quote Recursively Definition p_II := II.
Goal (exc_wcbvEval 10 p_II) = term_Term q_II.
reflexivity.
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
Eval compute in taut 0 true.
Eval compute in taut 1 (fun x => x).
Eval compute in taut 1 (fun x => x || negb x).
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
Quote Recursively Definition p_pierce := pierce.
Quote Definition q_pierce := Eval compute in pierce.
Goal (exc_wcbvEval 23 p_pierce) = term_Term q_pierce.
reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition p_Scomb := Scomb.
Quote Definition q_Scomb := Eval compute in Scomb.
Goal  (exc_wcbvEval 50 p_Scomb) = term_Term q_Scomb.
vm_compute. reflexivity.
Qed.

(* Must data constructors have fixed arity? It seems the answer is yes. *)
Fixpoint arity (n:nat) (A:Type) : Type :=
  match n with
    | 0 => A
    | S n => A -> arity n A
  end.
Eval compute in arity 2 bool.
Inductive bar : Type :=
| b0: arity 0 bar
| b1: arity 1 bar.
(** this constructor is not accepted:
| bn: forall n:nat, arity n bar.
***)

Inductive baz : Type :=
| baz1: baz
| baz2: arity 5 bool -> baz.


(** playing with arity of constructors **
Fixpoint Arity (n:nat) (A:Prop) : Prop :=
  match n with
    | 0 => A
    | S n => A -> Arity n A
  end.
Definition aaa : Prop := forall (X:Prop) (n:nat), X -> (Arity n X) -> X.
Definition ZZ: aaa := fun (X:Prop) (n:nat) (z:X) (s:Arity n X) => z.

Variable arb:nat.
Inductive vec1 A : nat -> Type :=
  |v1nil : vec1 A 0
  |v1cons : forall (h:A) (n:nat), vec1 A (n + n) -> vec1 A arb.
Inductive vec2 A (n:nat) : Type :=
  |v2nil : vec2 A n
  |v2cons : forall (h:A), vec2 A (n + n) -> vec2 A n.
***)

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

Definition sherwood: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (leaf false).
Quote Recursively Definition p_sherwood_size := (forest_size sherwood).
Quote Definition q_sherwood_size := Eval compute in (forest_size sherwood).
Goal (exc_wcbvEval 40 p_sherwood_size) = term_Term q_sherwood_size.
reflexivity.
Qed.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
Quote Recursively Definition p_arden_size := (forest_size arden).
Quote Definition q_arden_size := Eval compute in (forest_size arden).
Goal (exc_wcbvEval 100 p_arden_size) = term_Term q_arden_size.
vm_compute; reflexivity.
Qed.


Inductive uuyy: Set := uu | yy.
Inductive wwzz: Set := ww (_:uuyy)| zz (_:nat) (_:uuyy) (_:bool).
Definition Foo : nat -> bool -> wwzz -> wwzz := 
  fun (n:nat) (b:bool) (x:wwzz) =>
    match n,x,b with
      | 0, _, true => ww uu
      | 0, _, false => ww yy
      | S m, ww x, b => zz m x b
      | S m, zz n x c, b => zz m x b
    end.
Definition Foo0ty := (Foo 0 true (ww uu)).
Quote Recursively Definition p_Foo0ty := Foo0ty.
Quote Definition q_Foo0ty := Eval compute in Foo0ty.
Goal (exc_wcbvEval 23 p_Foo0ty) = term_Term q_Foo0ty.
reflexivity.
Qed.

(** destructing a parameterised datatype **)
Inductive lst (A:Set) : Set := 
| nl: lst A
| cns: A -> lst A -> lst A.
Definition hd (A:Set) (ls:lst A) (default:A) : A :=
  match ls with
    | nl _ => default
    | cns a _ => a
  end.
Quote Recursively Definition p_hd :=
 (@hd bool (@cns bool true (nl bool)) false).
Quote Definition q_hd :=
  Eval compute in (@hd bool (@cns bool true (nl bool)) false).
Goal exc_wcbvEval 100 p_hd = term_Term q_hd.
reflexivity.
Qed.

(** destructing a parameterised datatype **)
Inductive nelst (A:Set) : Set := 
| nenl: A -> nelst A
| necns: A -> nelst A -> nelst A.
Definition nehd (A:Set) (ls:nelst A) : A :=
  match ls with
    | nenl a => a
    | necns a _ => a
  end.
Quote Recursively Definition p_nehd :=
  (@nehd bool (@necns bool true (@nenl bool false))).
Quote Definition q_nehd :=
  Eval compute in (@nehd bool (@necns bool true (@nenl bool false))).
Goal exc_wcbvEval 100 p_nehd = term_Term q_nehd.
reflexivity.
Qed.


Inductive tm (A:Set) : Set := 
| vv: nat -> tm A 
| cc: A -> tm A.
Definition occIn (A:Set) (t:tm A) : nat :=
  match t with
    | vv _ m => m
    | cc _ => 0
end.
Quote Recursively Definition p_occIn := (occIn (cc true)).
Quote Definition q_occIn := Eval compute in (occIn (cc true)).
Goal exc_wcbvEval 20 p_occIn = term_Term q_occIn.
reflexivity.
Qed.


Require Import Vectors.Vector.
Open Scope vector_scope.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n :=
  Eval cbv delta beta in (map2 plus).

Definition vplus01 :=
  (@vplus 1 (cons nat 0 0 (nil nat)) (cons nat 1 0 (nil nat))).
Quote Recursively Definition p_vplus01 := vplus01.
Quote Definition q_vplus01 := Eval compute in vplus01.
Goal (exc_wcbvEval 40 p_vplus01) = term_Term q_vplus01.
compute. reflexivity.
Qed.

Definition v01 : Vector.t nat 2 := (cons nat 0 1 (cons nat 1 0 (nil nat))).
Definition v23 : Vector.t nat 2 := (cons nat 2 1 (cons nat 3 0 (nil nat))).
Definition vplus0123 := (@vplus 2 v01 v23).
Quote Recursively Definition p_vplus0123 := vplus0123.
Quote Definition q_vplus0123 := Eval compute in vplus0123.
Goal exc_wcbvEval 40 p_vplus0123 = term_Term q_vplus0123.
reflexivity.
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

Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Definition q_slowFib1 := Eval compute in (slowFib 1).
Goal exc_wcbvEval 10 p_slowFib1 = term_Term q_slowFib1.
reflexivity.
Qed.

Quote Recursively Definition p_slowFib3 := (slowFib 3).
Quote Definition q_slowFib3 := Eval compute in (slowFib 3).
Goal exc_wcbvEval 100 p_slowFib3 = term_Term q_slowFib3.
compute; reflexivity.
Qed.

Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).

(*** fails due to wcbv not matching Coq reduction ***
Quote Recursively Definition p_fibrec0 := (fibrec 0).
Quote Definition q_fibrec0 := Eval hnf in (fibrec 0).
Goal exc_wcbvEval 3 p_fibrec0 = term_Term q_fibrec0. simpl. 
reflexivity.
Qed.
***)

Quote Recursively Definition p_fib3 := (fib 3).
Quote Definition q_fib3 := Eval compute in (fib 3).
Goal exc_wcbvEval 100 p_fib3 = term_Term q_fib3.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib5 := (fib 5).
Quote Definition q_fib5 := Eval compute in (fib 5).
Goal exc_wcbvEval 100 p_fib5 = term_Term q_fib5.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib10 := (fib 10).
Quote Definition q_fib10 := Eval compute in (fib 10).
Goal exc_wcbvEval 300 p_fib10 = term_Term q_fib10.
vm_compute; reflexivity.
Qed.


(*** instantiate in a branch of a mutual fixpoint ***)
Section S1.
Variable nn:nat.
Fixpoint tree_size1 (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size1 f)
  end
with forest_size1 (f:forest bool) : nat :=
       match f with
         | leaf b => nn
         | fcons t f1 => (tree_size1 t + forest_size1 f1)
       end.
End S1.

Quote Recursively Definition p_forest_size1 := (forest_size1 1 sherwood).
Quote Definition q_forest_size1 := Eval compute in (forest_size1 1 sherwood).
Goal (exc_wcbvEval 40 p_forest_size1) = term_Term q_forest_size1.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_arden_size1 := (forest_size arden).
Quote Definition q_arden_size1 := Eval compute in (forest_size arden).
Goal (exc_wcbvEval 100 p_arden_size1) = term_Term q_arden_size1.
vm_compute; reflexivity.
Qed.
