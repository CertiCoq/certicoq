(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
(******)

Require Import ExtLib.Data.String.
Require Import Template.Template.
Require Import Common.Common.
Require L2.L2.         (* whole L2 library is exported by L2.L2 *)
Require Import L3.compile. 
Require Import L3.term.
Require Import L3.program.
Require Import L3.wcbvEval.

Local Open Scope bool.
Local Open Scope list.
Local Open Scope string_scope.

Variable (y:nat).
Quote Recursively Definition p_mbt := 
  match y with
    | 0 => (fun x:nat => x) 1
    | S n => (fun x:nat => x) 0
  end.
Definition L1g_mbt := Eval cbv in (program_Program p_mbt).
Definition mbt_env := env L1g_mbt.  (* L1g environ *)
Definition mbt_main := main L1g_mbt. (* L1g main function *)
Eval cbv in (wcbvEval 10 mbt_env mbt_main).


(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus _ v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
Print cbv_vplus0123.
(* [Term] of Coq's answer *)
Definition ans_vplus0123 := Eval cbv in (main (program_Program cbv_vplus0123)).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_Program p_vplus0123).
Print P_vplus0123.
Goal
  let env := (env P_vplus0123) in
  let main := (main P_vplus0123) in
  wcbvEval 100 (env) (main) = Some ans_vplus0123.
  vm_compute. reflexivity.
Qed.



Inductive List (A:Set) :=
  Nil: List A | Cons: forall (a:A) (bs:List A), List A.
Definition tl (A:Set) (ls:List A) : List A :=
  match ls with Nil _ => Nil A | Cons _ x bs => Cons _ x bs end.
Quote Recursively Definition p_tl := tl.
Print p_tl.


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
Print p_vplus0123.
Quote Definition q_vplus0123 := Eval cbv in (@vplus 2 v01 v23).
Print q_vplus0123.
Definition pP := Eval cbv in program_Program p_vplus0123.
Print pP.
(**
Definition cbv_q_vplus0123 := Eval cbv in (term_Term (env pP) q_vplus0123).
Print cbv_q_vplus0123.
**)
Definition cbv_env_pP := Eval cbv in (env pP).
Print cbv_env_pP.
Definition cbv_main_pP := Eval cbv in (main pP).
Print cbv_main_pP.
Eval cbv in (wcbvEval 100 cbv_env_pP cbv_main_pP).
Goal
  wcbvEval (env pP) 1000 (main pP) = Ret cbv_q_vplus0123.
  vm_compute. reflexivity.
Qed.



Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n :=
  Eval cbv in (Vector.map2 plus).

Definition vplus01 :=
  (@vplus 1 (Vector.cons nat 0 0 (Vector.nil nat))
          (Vector.cons nat 1 0 (Vector.nil nat))).
Definition cbv_vplus01 := Eval cbv in vplus01.
Print cbv_vplus01.
Quote Recursively Definition q_vplus01 := vplus01.
Print q_vplus01.
Quote Recursively Definition q_cbv_vplus01 := cbv_vplus01.
Print q_cbv_vplus01.
Definition p_vplus01 := Eval cbv in program_Program q_vplus01.
Print p_vplus01.
Definition ans_vplus01 := Eval cbv in main (program_Program q_vplus01).
Print ans_vplus01.
Print p_vplus01.



(** Olivier's example **)
Definition olivier := (Some 0).
Quote Recursively Definition p_olivier := olivier.
Quote Definition q_olivier := Eval cbv in olivier.
Print p_olivier.
Print q_olivier.
Goal
  let ew := (exc_wcbvEval 40 p_olivier q_olivier) in
  fst ew = snd ew.
compute. reflexivity.
Qed.

Quote Recursively Definition p_0 := 0.
Quote Definition q_0 := Eval compute in 0.
Goal
  let ew := (exc_wcbvEval 40 p_0 q_0) in
  fst ew = snd ew.
compute. reflexivity.
Qed.

(** Abishek's example **)
Axiom feq1 : (fun x:nat => x) = (fun x:nat => x+x-x).
Definition zero :nat :=
  match feq1 with
    | eq_refl => 0
  end.

(***)
Quote Recursively Definition p_zero := zero.
Quote Definition q_zero := Eval compute in zero.
Print p_zero.
Print q_zero.
Goal
  let ew := (exc_wcbvEval 40 p_zero q_zero) in
  fst ew = snd ew.
compute. reflexivity.
Qed.

Set Implicit Arguments.

Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Definition q_typedef := Eval compute in typedef.
Quote Recursively Definition p_typedef := typedef.
Eval compute in (L2.compile.program_Program p_typedef).
Definition e2 :=
  match (L2.compile.program_Program p_typedef) with
    | Exc _ => nil
    | Ret p => AstCommon.env p 
  end.
Eval compute in e2.
Eval compute in (term_Term e2 q_typedef).
Eval compute in (exc_wcbvEval 20 p_typedef q_typedef).
Goal 
  let ew := (exc_wcbvEval 20 p_typedef q_typedef) in
  fst ew = snd ew.
reflexivity.
Qed.

Definition II := fun (A:Type) (a:A) => a.
Quote Definition q_II := Eval compute in II.
Quote Recursively Definition p_II := II.
Goal
  let ew := (exc_wcbvEval 10 p_II q_II) in
  fst ew = snd ew.
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
Print p_pierce.
Quote Definition q_pierce := Eval compute in pierce.
Goal
  let ew := (exc_wcbvEval 23 p_pierce q_pierce) in
  fst ew = snd ew.
reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition p_Scomb := Scomb.
Quote Definition q_Scomb := Eval compute in Scomb.
Goal
  let ew := (exc_wcbvEval 50 p_Scomb q_Scomb) in
  fst ew = snd ew.
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

Quote Recursively Definition p_fcons := fcons.
Print p_fcons.
Quote Definition q_fcons := Eval compute in (fcons).
Goal
  let ew := (exc_wcbvEval 10 p_fcons q_fcons) in
  fst ew = snd ew.
compute. reflexivity.
Qed.

Definition e3 :=
  match (L2.compile.program_Program p_fcons) with
    | Exc _ => nil
    | Ret p => AstCommon.env p 
  end.
Eval compute in e3.
Eval compute in (term_Term e3 q_fcons).
Eval compute in (L2.compile.term_Term q_fcons).
Eval compute in (cnstrArity e3 (mkInd "Top.tree" 1) 1).
Eval compute in (etaExp_cnstr e3 (mkInd "Top.tree" 1) 1 tnil).


Quote Recursively Definition p_fconsBool := (@fcons bool).
Quote Definition q_fconsBool := Eval compute in (@fcons bool).
Goal
  let ew := (exc_wcbvEval 10 p_fconsBool q_fconsBool) in
  fst ew = snd ew.
compute. reflexivity.
Qed.

Quote Recursively Definition p_fconsTrue := (fcons (node true (leaf false))).
Quote Definition q_fconsTrue :=
  Eval compute in (fcons (node true (leaf false))).
Goal
  let ew := (exc_wcbvEval 10 p_fconsTrue q_fconsTrue) in
  fst ew = snd ew.
compute. reflexivity.
Qed.


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
Goal
  let ew := (exc_wcbvEval 40 p_sherwood_size q_sherwood_size) in
  fst ew = snd ew.
vm_compute. reflexivity.
Qed.

Definition arden: forest bool :=
  fcons (node true (fcons (node true (leaf false)) (leaf true)))
        (fcons (node true (fcons (node true (leaf false)) (leaf true)))
               (leaf false)).
Quote Recursively Definition p_arden_size := (forest_size arden).
Quote Definition q_arden_size := Eval compute in (forest_size arden).
Goal
  let ew := (exc_wcbvEval 100 p_arden_size q_arden_size) in
  fst ew = snd ew.
vm_compute. reflexivity.
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
Goal
  let ew := (exc_wcbvEval 23 p_Foo0ty q_Foo0ty) in
  fst ew = snd ew.
vm_compute. reflexivity.
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
Goal
  let ew := (exc_wcbvEval 100 p_hd q_hd) in
  fst ew = snd ew.
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
Goal
  let ew := (exc_wcbvEval 100 p_nehd q_nehd) in
  fst ew = snd ew.
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
Goal
  let ew := (exc_wcbvEval 20 p_occIn q_occIn) in
  fst ew = snd ew.
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
Goal
  let ew := (exc_wcbvEval 20 p_vplus01 q_vplus01) in
  fst ew = snd ew.
vm_compute. reflexivity.
Qed.

Definition v01 : Vector.t nat 2 := (cons nat 0 1 (cons nat 1 0 (nil nat))).
Definition v23 : Vector.t nat 2 := (cons nat 2 1 (cons nat 3 0 (nil nat))).
Definition vplus0123 := (@vplus 2 v01 v23).
Quote Recursively Definition p_vplus0123 := vplus0123.
Quote Definition q_vplus0123 := Eval compute in vplus0123.
Goal
  let ew := (exc_wcbvEval 40 p_vplus0123 q_vplus0123) in
  fst ew = snd ew.
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

Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Definition q_slowFib1 := Eval compute in (slowFib 1).
Goal
  let ew := (exc_wcbvEval 10 p_slowFib1 q_slowFib1) in
  fst ew = snd ew.
reflexivity.
Qed.

Quote Recursively Definition p_slowFib4 := (slowFib 4).
Quote Definition q_slowFib4 := Eval compute in (slowFib 4).
Goal
  let ew := (exc_wcbvEval 100 p_slowFib4 q_slowFib4) in
  fst ew = snd ew.
compute. reflexivity.
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
Goal
  let ew := (exc_wcbvEval 100 p_fib3 q_fib3) in
  fst ew = snd ew.
vm_compute. reflexivity.
Qed.

Quote Recursively Definition p_fib10 := (fib 10).
Quote Definition q_fib10 := Eval compute in (fib 10).
Goal
  let ew := (exc_wcbvEval 300 p_fib10 q_fib10) in
  fst ew = snd ew.
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
Quote Definition q_forest_size1 := Eval compute in (forest_size1 1 sherwood).
Goal
  let ew := (exc_wcbvEval 40 p_forest_size1 q_forest_size1) in
  fst ew = snd ew.
vm_compute; reflexivity.
Qed.

Quote Recursively Definition p_arden_size1 := (forest_size arden).
Quote Definition q_arden_size1 := Eval compute in (forest_size arden).
Goal
  let ew := (exc_wcbvEval 100 p_arden_size1 q_arden_size1) in
  fst ew = snd ew.
vm_compute; reflexivity.
Qed.
