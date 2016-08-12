
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
Add LoadPath "." as L1_5.

Require Import Template.Template.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1_5.compile.
Require Import L1_5.wcbvEval.
Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Unset Template Cast Propositions.  (** L1 doesn't strip proofs **)
Set Printing Width 90.
Set Printing Depth 100.


(** Abhishek's example of looping in L1 **)
Inductive lt (n:nat) : nat -> Prop := lt_n: lt n (S n).
Inductive Acc (y: nat) : Prop :=
  Acc_intro : (forall x: nat, lt y x -> Acc x) -> Acc y.
Definition Acc_inv: forall (x:nat) (H:Acc x) (y:nat), lt x y -> Acc y.
  intros. destruct H. apply H. apply H0.
  Defined.
Fixpoint loop (n:nat) (a:Acc n) {struct a} : nat :=
  match n with
    | _ => loop (S n) (Acc_inv _ a (S n) (lt_n n))
  end.
Axiom Acc0Ax : Acc 0.
Eval vm_compute in (loop O Acc0Ax) .
Quote Recursively Definition p_loop0 := (loop 0 Acc0Ax).
Print p_loop0.
(***)

Set Implicit Arguments.


Definition LL := list.
Quote Definition q_LL := LL.
Print  q_LL.
Quote Definition q_eLL := Eval cbv in LL.
Print  q_eLL.


(** non-recursive fixpoint has non-null Defs **)
Fixpoint tst (b:bool) : bool := true.
Print tst.
Quote Recursively Definition p_tst := tst.
Print p_tst.



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

(** indexed datatypes **)
Inductive fin : nat -> Set :=
| f0: fin 0
| fS: forall (n:nat) (f:fin n), fin (S n).

Definition fiszero (n:nat) (f:fin n) : bool :=
  match f with
    | f0 => true
    | fS _ => false
  end.
Quote Recursively Definition p_fiszero := fiszero.
Print p_fiszero.

Definition blist := (@list ((fun x:Set => x) bool)).
Quote Recursively Definition clist := blist.
Print clist.
Quote Recursively Definition bcons := (@cons bool).
Print bcons.

Definition xlist := (@list (list bool)).
Quote Definition qlist := Eval cbv in xlist.
Print qlist.
Quote Recursively Definition qcons :=
  (@cons (list bool): (list bool) -> xlist -> xlist).
Print qcons.

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n :=
  Eval cbv in (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (@vplus 2 v01 v23).
Definition cbv_vplus0123 := Eval cbv in vplus0123.  (* evaluated by Coq *)
Print cbv_vplus0123.
(* program of Coq's result *)
Quote Recursively Definition p_vplus0123 := (@vplus 2 v01 v23).
Quote Definition q_vplus0123 := Eval cbv in (@vplus 2 v01 v23).
Goal
  let pP : Program := program_Program p_vplus0123 in
  let qP : AstCommon.environ L1g.compile.Term :=
      program_datatypeEnv p_vplus0123 nil in.
  wcbvEval (env pP) 100 (main pP) = Ret (term_Term (env qP) q_vplus0123).
  vm_compute. reflexivity.
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
Quote Recursively Definition p_arden_size := (forest_size arden).
Quote Definition q_arden_size := Eval cbv in (forest_size arden).
Goal
  let pP := program_Program p_arden_size in
  wcbvEval (env pP) 100 (main pP) = Ret (term_Term (env pP) q_arden_size).
vm_compute; reflexivity.
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
Quote Recursively Definition p_ack35 := ack35.
Quote Definition q_ack35 := Eval cbv in ack35.
Goal
  let pP := program_Program p_ack35 in
  wcbvEval (env pP) 15000 (main pP) = Ret (term_Term (env pP) q_ack35).
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
Quote Recursively Definition p_pierce := pierce.
Quote Definition q_pierce := Eval cbv in pierce.
Goal
  let pP := program_Program p_pierce in
  wcbvEval (env pP) 15000 (main pP) = Ret (term_Term (env pP) q_pierce).
vm_compute. reflexivity.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition p_Scomb := Scomb.
Quote Definition q_Scomb := Eval cbv in Scomb.
Goal
  let pP := program_Program p_pierce in
  wcbvEval (env pP) 15000 (main pP) = Ret (term_Term (env pP) q_Scomb).
vm_compute. reflexivity.
Qed.

(********
(** match with no branches **)
Definition Fdemo (f:False) : False := match f with end.
Print Fdemo.
Quote Recursively Definition p_Fdemo := Fdemo.
Print p_Fdemo.

Axiom FF : False.
Eval compute in (Fdemo FF).


(** match: eval type parts of Defs **)
Definition bb := bool.
Definition demo (t:True) : bb := match t with I => true end.
Print demo.
Eval cbv in demo.
Quote Recursively Definition p_demo := demo.
Print p_demo.
Quote Definition qcbv_demo := Eval native_compute in demo.
Print qcbv_demo.
(*** fails **
Goal exc_wcbvEval 40 p_demo = term_Term qcbv_demo.
native_compute. reflexivity.
Qed.
***)

Definition bb1 := fun (t:True) => bool.
Definition demo1 (t:True) : (bb1 t) := match t with I => true end.
Print demo1.
Eval cbv in demo1.
Quote Recursively Definition p_demo1 := demo1.
Print p_demo1.
Quote Definition qcbv_demo1 := Eval cbv in demo1.
Print qcbv_demo1.


(** Abhishek's example **)
Definition xx := (fun x:nat => x) = (fun x:nat => x+x-x).
Print xx.
Eval cbv in xx.

Print eq.

Inductive mleq (A:Type) : A -> A-> Prop := mleqrfl:forall x:A, mleq x x.
Print mleq.

Axiom mlfeq : mleq 0 0.
Print mlfeq.
Quote Definition q_mlfeq := mlfeq.
Print q_mlfeq.
Eval cbv in (term_Term q_mlfeq).
Quote Recursively Definition p_mlfeq := mlfeq.
Print p_mlfeq.

(*** not accepted because mleqrfl has a non-Prop argument
Definition mlzero : nat :=
  match mlfeq with
    | mleqrfl x => 0
  end.
****)

Inductive NN : Prop := ZZ:NN | SS:NN->NN.
Inductive BB : Prop := tt:BB | ff:BB.

Definition mlbb : BB :=
  match mlfeq with
    | mleqrfl x => match x with O => tt | S _ => ff  end
  end.
Quote Definition q_mlbb := mlbb.
Print q_mlbb.

Axiom feq : 0 = 0.
Definition zero : nat :=
  match feq with
    | eq_refl => 0
  end.
Quote Definition q_0 := Eval cbv in 0.
Quote Recursively Definition p_zero := zero.
Print p_zero.
Eval cbv in program_Program p_zero (ret nil).
Goal exc_wcbvEval 40 p_zero = term_Term q_0.
compute. 
Abort.  (* axiom feq doesn't expand: blocks eval *)

Print and.
Inductive pack (A:Prop) : Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A) : nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Goal exc_wcbvEval 40 p_pack_nat = term_Term q_0.
compute. 
Abort.
  
Axiom andax: forall A, A /\ A -> A /\ A.
Definition and_nat (A:Prop) (a:A /\ A) : nat :=
  match andax a with
    | conj b1 b2 => 0
  end.
Quote Recursively Definition p_and_nat := (and_nat (conj I I)).
Print p_and_nat.
Eval cbv in (program_Program p_and_nat (ret nil)).
Goal exc_wcbvEval 40 p_and_nat = term_Term q_0.
compute. 
Abort.


Axiom feq1 : forall (y:bool), (fun x:nat => x) = (fun x:nat => x+2).
Print feq1.
Eval cbv in feq1.
Definition zero1 : nat :=
  match feq1 true with
    | eq_refl => 0
  end.
Eval cbv in zero1.
Quote Definition q_zero1 := Eval cbv in zero1.
Print q_zero1.
Quote Recursively Definition p_zero1 := zero1.
Print p_zero1.
Goal exc_wcbvEval 40 p_zero1 = term_Term q_zero1.
compute. 
Abort.

(** fails because Coq cbv is not weak ***
Axiom feq2 : 0 = 0.
Print feq2.
Eval cbv in feq2.
Definition zero2: nat :=
  match feq2 with
    | eq_refl => 0
  end.
Print zero2.
Eval cbv in zero2.
Quote Definition q_zero2 := Eval cbv in zero2.
Print Template.Ast.
Print q_zero2.
Print IDProp.
Eval cbv in (term_Term, q_zero2).
Quote Recursively Definition p_zero2 := zero2.
Print p_zero2.
Print IDProp.
Goal exc_wcbvEval 40 p_zero2 = term_Term q_zero2.
compute. reflexivity.
***)

Definition Lb (b:bool) : (b = b) := eq_refl b. 
Definition testLb := Lb (orb true true).
Quote Recursively Definition p_testLb := testLb.
Print p_testLb.
Eval cbv in testLb.
Quote Definition q_testLb := Eval cbv in testLb.
Print q_testLb.
Goal exc_wcbvEval 40 p_testLb = term_Term q_testLb.
compute. reflexivity.
Qed.

Definition trivadd := (1 + 0).
Quote Definition q_trivadd := Eval cbv in trivadd.
Print q_trivadd.
Quote Recursively Definition p_trivadd := trivadd.
Print p_trivadd.
Goal exc_wcbvEval 100 p_trivadd = term_Term q_trivadd.
compute. reflexivity.
Qed.

Axiom ax : forall x:nat, x = x.
Definition testAx := ax (1 + 0).
Print testAx.
Eval cbv in testAx.
Quote Definition q_testAx := Eval cbv in testAx.
Print q_testAx.
Quote Recursively Definition p_testAx := testAx.
Print p_testAx.

Eval cbv in (program_Program p_testAx (Ret nil)).
Definition pgm :=
  match  (program_Program p_testAx (Ret nil)) with
    | Ret pgm => env pgm
    | x => nil
  end.
Eval compute in pgm.
Definition main :=
  match  (program_Program p_testAx (Ret nil)) with
    | Ret pgm => main pgm
    | x => prop
  end.
Eval compute in main.

Goal exc_wcbvEval 40 p_testAx = term_Term q_testAx.
compute. reflexivity.
Qed.

Goal exc_wcbvEval 40 p_testAx = term_Term q_testAx.
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
  Eval cbv in ((@cons nat:nat -> list nat -> list nat) 0).
Print AppApp2.
***)

Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Definition q_typedef := Eval cbv in typedef.
Quote Recursively Definition p_typedef := typedef.
Goal
  (exc_wcbvEval 200 p_typedef) = term_Term q_typedef.
compute. reflexivity.
Qed.

Definition II := fun (A:Type) (a:A) => a.
Quote Definition q_II := Eval cbv in II.
Quote Recursively Definition p_II := II.
Goal
  (exc_wcbvEval 10 p_II) = term_Term q_II.
reflexivity.
Qed.


(* Must data constructors have fixed arity? It seems the answer is yes. *)
Fixpoint arity (n:nat) (A:Type) : Type :=
  match n with
    | 0 => A
    | S n => A -> arity n A
  end.
Eval cbv in arity 2 bool.
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
Quote Definition q_Foo0ty := Eval cbv in Foo0ty.
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
  Eval cbv in (@hd bool (@cns bool true (nl bool)) false).
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
  Eval cbv in (@nehd bool (@necns bool true (@nenl bool false))).
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
Quote Definition q_occIn := Eval cbv in (occIn (cc true)).
Goal exc_wcbvEval 20 p_occIn = term_Term q_occIn.
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
Quote Definition q_slowFib1 := Eval cbv in (slowFib 1).
Goal exc_wcbvEval 10 p_slowFib1 = term_Term q_slowFib1.
reflexivity.
Qed.

Quote Recursively Definition p_slowFib3 := (slowFib 3).
Quote Definition q_slowFib3 := Eval cbv in (slowFib 3).
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
Quote Definition q_fib3 := Eval cbv in (fib 3).
Goal exc_wcbvEval 100 p_fib3 = term_Term q_fib3.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib5 := (fib 5).
Quote Definition q_fib5 := Eval cbv in (fib 5).
Goal exc_wcbvEval 100 p_fib5 = term_Term q_fib5.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_fib10 := (fib 10).
Quote Definition q_fib10 := Eval cbv in (fib 10).
Goal exc_wcbvEval 400 p_fib10 = term_Term q_fib10.
vm_compute. reflexivity.
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
Quote Definition q_forest_size1 := Eval cbv in (forest_size1 1 sherwood).
Goal (exc_wcbvEval 100 p_forest_size1) = term_Term q_forest_size1.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_arden_size1 := (forest_size arden).
Quote Definition q_arden_size1 := Eval cbv in (forest_size arden).
Goal (exc_wcbvEval 100 p_arden_size1) = term_Term q_arden_size1.
vm_compute; reflexivity.
Qed.
 ************)