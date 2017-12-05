
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Recdef.
Require Import omega.Omega.
Require Import Template.Template.
Require Import Common.Common.
Require Import L2.compile.
Require Import L2.term.
Require Import L2.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Set Template Cast Propositions.
Set Printing Width 100.
Set Printing Depth 1000.

Notation NN := (mkInd "Coq.Init.Datatypes.nat" 0).
Notation SS := (TConstruct NN 1 1).
Notation ZZ := (TConstruct NN 0 0).
Notation BB := (mkInd "Coq.Init.Datatypes.bool" 0).
Notation ff := (TConstruct BB 1 0 0).
Notation tt := (TConstruct BB 0 0 0).
Notation LL := (mkInd "Coq.Init.Datatypes.list" 0).
Notation CONS := (TConstruct LL 1 3).
Notation NIL := (TConstruct LL 0 1).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation AND := (mkInd "Coq.Init.Logic.and" 0).
Notation CONJ := (TConstruct AND 0 4).
Notation TRUE := (mkInd "Coq.Init.Logic.True" 0).
Notation II := (TConstruct TRUE 0 0).
Notation EQ := (mkInd "Coq.Init.Logic.eq" 0).
Notation RFL := (TConstruct EQ 0 2).
Notation PROD := (mkInd "Coq.Init.Datatypes.prod" 0).
Notation PAIR := (TConstruct PROD 0 4).
Notation "^ x" := (nNamed x)  (at level 85).
Notation "^" := (nAnon).
Infix ":t:" := tcons  (at level 87, right associativity).

Definition tstx := 1.
Quote Recursively Definition cbv_tstx :=
  ltac:(let t:=(eval cbv in tstx) in exact t).
Definition ans_tstx :=
  Eval cbv in (main (program_Program cbv_tstx)).
(* [program] of the program *)
Quote Recursively Definition p_tstx := tstx.
Definition P_tstx := Eval cbv in (program_Program p_tstx).
Goal
  let env := (env P_tstx) in
  let main := (main P_tstx) in
  wcbvEval (env) 90 (main) = Ret ans_tstx.
  vm_compute. reflexivity.
Qed.
Goal
  let env := (env P_tstx) in
  let main := (main P_tstx) in
  WcbvEval (env) (main) ans_tstx.
Proof.
  intros. unfold main, AstCommon.main, P_tstx, ans_tstx.
  eapply wConst.
  - reflexivity.
  - eapply wAppCong.
    + eapply wConstruct.
    + left. auto.
    + eapply wConstruct.
    + constructor.
Qed.

Section myplus.
  Variables (A:Type).
  Inductive myNat : Type :=
  | myZ: forall a:A, myNat.
  Definition myplus (m: myNat) : A :=
    match m with
    | myZ a => a
    end.
End myplus.
Print myplus.
Definition myplusx := (myplus (myZ true)).
Compute myplusx.
Quote Recursively Definition cbv_myplusx :=
  ltac:(let t:=(eval cbv in myplusx) in exact t).
Definition ans_myplusx :=
  Eval cbv in (main (program_Program cbv_myplusx)).
Print ans_myplusx.
(* [program] of the program *)
Quote Recursively Definition p_myplusx := myplusx.
Definition P_myplusx := Eval cbv in (program_Program p_myplusx).
Goal   (** works in L2 **)
  let env := (env P_myplusx) in
  let main := (main P_myplusx) in
  wcbvEval (env) 90 (main) = Ret ans_myplusx.
Proof.
  vm_compute. reflexivity.
Qed.
Goal
  let env := (env P_myplusx) in
  let main := (main P_myplusx) in
  WcbvEval (env) (main) ans_myplusx.
Proof.
  intros. unfold main, AstCommon.main, P_myplusx, ans_myplusx.
  eapply wConst.
  - reflexivity.
  - eapply wAppLam.
    + eapply wConst.
      * reflexivity.
      * eapply wLam.
    + eapply wDummy.
    + unfold whBetaStep, instantiate. unfold nat_compare. unfold mkApp.
      eapply wAppLam.
      * eapply wLam.
      *{ eapply wAppCong.
         - eapply wConstruct.
         - left. auto.
         - eapply wDummy.
         - eapply wCons.
           + eapply wConstruct.
           + eapply wNil. }
      *{ unfold whBetaStep, instantiate. unfold nat_compare. unfold mkApp.
         eapply wCase.
         - eapply wAppCong.
           + eapply wConstruct.
           + left. auto.
           + eapply wDummy.
           + eapply wCons.
             * eapply wConstruct.
             * eapply wNil.
         - unfold canonicalP. reflexivity.
         - reflexivity.
         - reflexivity.
         - unfold mkApp. eapply wAppLam.
           + eapply wLam.
           + eapply wConstruct.
           + unfold whBetaStep, instantiate. unfold nat_compare.
             eapply wConstruct. }
Qed.

Fixpoint myapp (ls ts: list nat): list nat :=
  match ls with
  | nil => ts
  | cons b bs => cons b (myapp bs ts)
  end.
Definition myappx := (myapp (cons 0 (cons 1 nil)) nil).
Compute myappx.
Quote Recursively Definition cbv_myappx :=
  ltac:(let t:=(eval cbv in myappx) in exact t).
Definition ans_myappx :=
  Eval cbv in (main (program_Program cbv_myappx)).
Print ans_myappx.
(* [program] of the program *)
Quote Recursively Definition p_myappx := myappx.
Definition P_myappx := Eval cbv in (program_Program p_myappx).
Goal
  let env := (env P_myappx) in
  let main := (main P_myappx) in
  wcbvEval (env) 900 (main) = Ret ans_myappx.
  vm_compute. reflexivity.
Qed.


(** list reverse **)
Fixpoint myrev (ls: list nat): list nat :=
  match ls with
  | nil => nil
  | cons b bs => (myrev bs) ++ (cons b nil)
  end.
Definition myrevx := (myrev (cons 0 nil)).
Compute myrevx.
Quote Recursively Definition cbv_myrevx :=
  ltac:(let t:=(eval cbv in myrevx) in exact t).
Definition ans_myrevx :=
  Eval cbv in (main (program_Program cbv_myrevx)).
Print ans_myrevx.
(* [program] of the program *)
Quote Recursively Definition p_myrevx := myrevx.
Definition P_myrevx := Eval cbv in (program_Program p_myrevx).
Goal
  let env := (env P_myrevx) in
  let main := (main P_myrevx) in
  wcbvEval (env) 90 (main) = Ret ans_myrevx.
  vm_compute. reflexivity.
Qed.

(** hetereogenous list: type as non-parametric argument to constructor **)
Inductive hlist : Type :=
| hnil : hlist
| hcons : forall (A:Type), A -> hlist -> hlist.
Print hlist.

Fixpoint hlength (l:hlist) : nat :=
  match l with
  | hnil => 0
  | hcons _ k => S (hlength k)
  end.

Fixpoint hmap (f: forall (A:Type), A -> bool) (l:hlist) : list bool :=
  match l with
  | hnil => nil
  | hcons a k => cons (f _ a) (hmap f k)
  end.

Recursive Extraction hmap.


Function deProof (t:Term) : Term :=
  match t with
    | TRel n => TRel n
    | TProof t => t
    | TLambda nm bod => TLambda nm (deProof bod)
    | TLetIn nm dfn bod => TLetIn nm (deProof dfn) (deProof bod)
    | TApp fn arg args => TApp (deProof fn) (deProof arg) (deProofs args)
    | TConst nm => TConst nm
    | TConstruct i m np na => TConstruct i m np na
    | TCase n mch brs => TCase n (deProof mch) (deProofBs brs)
    | TFix ds n => TFix (deProofDs ds) n
    | TDummy str => TDummy str
    | TWrong str => TWrong str
  end
with deProofs (ts:Terms) : Terms := 
  match ts with
    | tnil => tnil
    | tcons t ts => tcons (deProof t) (deProofs ts)
  end
with deProofBs (bs:Brs) : Brs := 
  match bs with
    | bnil => bnil
    | bcons n t ts => bcons n (deProof t) (deProofBs ts)
  end
with deProofDs (ts:Defs) : Defs := 
  match ts with
    | dnil => dnil
    | dcons nm t m ds => dcons nm (deProof t) m (deProofDs ds)
  end.


Quote Recursively Definition p_Type := Type.
Print p_Type.
Definition P_Type := Eval cbv in (program_Program p_Type).
Print P_Type.


(******
Require Import Benchmarks.vs.

Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (program_Program p_ce_example_myent).
Definition P_env_ce_example_myent :=
  Eval vm_compute in (env P_ce_example_myent).
Definition P_main_ce_example_myent :=
  Eval vm_compute in (AstCommon.main P_ce_example_myent).
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 4000 P_main_ce_example_myent).
Print eval_ce_example_myent.

Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_Program p_ce_example_ent).
Time Definition P_env_ce_example_ent := env P_ce_example_ent.
Time Definition P_main_ce_example_ent := AstCommon.main P_ce_example_ent.
Time Definition eval_ce_example_ent :=
  Eval vm_compute in (wcbvEval P_env_ce_example_ent 1000 P_main_ce_example_ent).
Print eval_ce_example_ent.
****)

Print list.
Inductive mist (A:Type) := mil: mist A | mcons: A -> mist A -> mist A.
Print mist.
Eval cbv in ((fun (x:forall A:Type, mist A) => x Prop) mil).

(**********
Inductive NN: Prop := NN0: NN | NNS: NN -> NN.
Quote Recursively Definition p_NN1:= (NNS NN0).
Eval cbv in (program_Program p_NN1).
Fixpoint NNplus (m n: NN) : NN :=
  match m with
    | NN0 => n
    | NNS u => NNplus u n
  end.
Inductive NNle (n:NN) : NN -> Prop :=
| NNle_n : NNle n n
| NNle_S : forall m:NN, NNle n m -> NNle n (NNS m).
 ******************)

Quote Recursively Definition p_map := List.map.
Eval cbv in (program_Program p_map).
Check cons. Check @nil.
Definition Nil : forall A:Type, list A := @nil.
Eval cbv in ((fun (x:forall A:Type, list A) => x Prop) Nil).


(** Abhishek's example of looping: in L2 we don't test the guard **)
Inductive mlt (n:nat) : nat -> Prop := mlt_n: mlt n (S n).
Inductive Acc (y: nat) : Prop :=
  Acc_intro : (forall x: nat, mlt y x -> Acc x) -> Acc y.
Definition Acc_inv: forall (x:nat) (H:Acc x) (y:nat), mlt x y -> Acc y.
  intros. destruct H. apply H. apply H0.
  Defined.
Fixpoint loop (n:nat) (a:Acc n) {struct a} : nat :=
  match n with
    | _ => @loop (S n) (@Acc_inv _ a (S n) (mlt_n n))
  end.
Axiom Acc0Ax : Acc 0.
Definition loop0 := (@loop O Acc0Ax).
Eval vm_compute in loop0.   (** Coq does not loop **)

Quote Recursively Definition p_loop0 := loop0.
Definition P_loop0 := Eval vm_compute in (program_Program p_loop0).
Definition P_env := Eval vm_compute in (env P_loop0).
Definition P_main := Eval vm_compute in (main P_loop0).
(** wcbvEval raises exception "out of time": non-terminating **)
Eval vm_compute in wcbvEval P_env 1000 P_main.

(***************
Goal
  WcbvEval P_env P_main prop.
Proof.
  unfold P_main. eapply wConst. cbn. reflexivity.
  eapply wAppFix.
  - eapply wConst. cbn. reflexivity. eapply wFix.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - eapply wProof. eapply wAx.
  - cbn. eapply wAppLam.
    + eapply wLam.
    + eapply wConstruct.
    + cbn. eapply wAppLam.
      * eapply wLam.
      * eapply wAx.
      * { cbn. eapply wAppFix.
          - eapply wFix.
          - cbn. reflexivity.
          - cbn. reflexivity.
          - eapply wProof. eapply wAppLam.
            + eapply wConst. cbn. reflexivity. eapply wProof. eapply wLam.
            + eapply wConstruct.
            + cbn. eapply wAppLam.
              * eapply wLam.
              * eapply wAx.
              * { cbn. eapply wAppLam.
                  - eapply wLam.
                  - eapply wAppCong.
                    + eapply wConstruct.
                    + not_isLambda.
                    + not_isFix.
                    + terms.
                    + cbn. reflexivity.
                  - cbn. eapply wAppLam.
                    + eapply wLam.
                    + eapply wAppCong.
                      * eapply wConstruct.
                      * not_isLambda.
                      * not_isFix.
                      * terms.
                      * cbn. reflexivity.
                    + cbn. eapply wCaseCong.
                      * eapply wAx.
                      * cbn. reflexivity.
                      * terms. eapply wLam. }
          - cbn. eapply wAppLam.
            + eapply wLam.
            + eapply wAppCong.
              * eapply wConstruct.
              * not_isLambda.
              * not_isFix.
              * terms.
              * cbn. reflexivity.
            + cbn. eapply wAppLam.
              * eapply wLam.
              * { eapply wCaseCong.
                  - eapply wAx.
                  - cbn. reflexivity.
                  - terms. eapply wLam. }
              * { cbn. eapply wAppFix.
                  - eapply wFix.
                  - cbn. reflexivity.
                  - cbn. reflexivity.
                  - eapply wProof. eapply wAppLam.
                    + eapply wConst. cbn. reflexivity. eapply wProof.
                      eapply wLam.
                    + eapply wAppCong.
                      * eapply wConstruct.
                      * not_isLambda.
                      * not_isFix.
                      * terms.
                      * cbn. reflexivity.
                    + cbn. eapply wAppLam.
                      * eapply wLam.
                      * { eapply wCaseCong.
                          - eapply wAx.
                          - reflexivity.
                          - terms. eapply wLam. }
                      * { cbn. eapply wAppLam.
                          - eapply wLam.
                          - eapply wAppCong.
                            + eapply wConstruct.
                            + not_isLambda.
                            + not_isFix.
                            + terms. cbn. reflexivity.
                            + cbn. reflexivity.
                          - cbn. eapply wAppLam.
                            + eapply wLam.
                            + eapply wAppCong.
                              * eapply wConstruct.
                              * not_isLambda.
                              * not_isFix.
                              * terms. cbn. reflexivity.
                              * cbn. reflexivity.
                            + cbn. eapply wCaseCong.
                              * { eapply wCaseCong.
                                  - eapply wAx.
                                  - cbn. reflexivity.
                                  - terms. eapply wLam. }
                              * cbn. reflexivity.
                              * terms. eapply wLam. }
                  - cbn. eapply wAppLam.
                    + eapply wLam.
                    + eapply wAppCong.
                      * eapply wConstruct.
                      * not_isLambda.
                      * not_isFix.
                      * terms. cbn. reflexivity.
                      * cbn. reflexivity.
                    + cbn. eapply wAppLam.

********************************)
                      

Inductive P0: Prop := p0.
Inductive P1: Prop := p1.
Notation PP0 := (mkInd "P0" 0).
Notation pp0 := (TConstruct PP0 0 0).
Notation PP1 := (mkInd "P1" 0).
Notation pp1 := (TConstruct PP1 0 0).


Print and_rect.
Quote Recursively Definition p_and_rect := and_rect.
Print p_and_rect.
Eval cbv in (program_Program p_and_rect).
Check program_Program.

Definition and_rect_x :=
  (and_rect (fun (a:1=1) (b:True) => conj b a) (conj (eq_refl 1) I)).
Quote Recursively Definition p_and_rect_x := and_rect_x.
Definition P_and_rect_x := Eval cbv in (program_Program p_and_rect_x).
Print P_and_rect_x.
Quote Recursively Definition cbv_and_rect_x :=
  ltac:(let t:=(eval cbv in and_rect_x) in exact t).
Print cbv_and_rect_x.
Definition ans_and_rect_x :=
  Eval cbv in (deProof (main (program_Program cbv_and_rect_x))).
Print ans_and_rect_x.

Goal
  let envx := env P_and_rect_x in
  let mainx := main P_and_rect_x in
  wcbvEval envx 25 mainx = Ret ans_and_rect_x.
  vm_compute. reflexivity.
Qed.

Definition and_rectx :=
  and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1).
Eval cbv in and_rectx.
Quote Recursively Definition ans_and_rectx := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in and_rectx) in exact t).
Definition Ans_and_rectx :=
  Eval cbv in (wcbvEval (env (program_Program ans_and_rectx)) 1000
                        (main (program_Program ans_and_rectx))).
Print Ans_and_rectx.
Quote Recursively Definition p_and_rectx := and_rectx.
Print p_and_rectx.
Definition P_and_rectx := Eval cbv in (program_Program p_and_rectx).
Print P_and_rectx.
Definition P_envx := env P_and_rectx.
Definition P_mainx := main P_and_rectx.
Goal wcbvEval P_envx 100 P_mainx = Ans_and_rectx.
  vm_compute. reflexivity.
Qed.

Set Implicit Arguments.
Definition my_and_rect := 
  fun (A B : Prop) (P : Type) (f : A -> B -> P) (a : A /\ B) =>
    match a with conj x x0 => f x x0 end.
Quote Recursively Definition p_my_and_rect := my_and_rect.
Print p_my_and_rect.
Eval cbv in (program_Program p_my_and_rect).
Quote Recursively Definition p_my_and_rectx :=
  (and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1)).
Definition P_my_and_rectx := Eval cbv in (program_Program p_and_rectx).
Definition P_my_envx := env P_my_and_rectx.
Definition P_my_mainx := main P_my_and_rectx.
Eval cbv in (wcbvEval P_my_envx 100 P_my_mainx).

Definition my_and_rect_x :=
  (my_and_rect (fun (a:1=1) (b:True) => conj b a) (conj (eq_refl 1) I)).
Quote Recursively Definition p_my_and_rect_x := my_and_rect_x.
Definition P_my_and_rect_x := Eval cbv in (program_Program p_my_and_rect_x).
Quote Recursively Definition cbv_my_and_rect_x :=
  ltac:(let t:=(eval cbv in my_and_rect_x) in exact t).
Definition ans_my_and_rect_x :=
  Eval cbv in (main (program_Program cbv_my_and_rect_x)).
Definition my_envx := env P_my_and_rect_x.
Definition my_mainx := main P_my_and_rect_x.
Eval cbv in (wcbvEval my_envx 30 my_mainx).

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
  Eval cbv in (main (program_Program cbv_slowFib3)).
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Print p_slowFib3.
Definition P_slowFib3 := Eval cbv in (program_Program p_slowFib3).
Print P_slowFib3.
Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval (env) 30 (main) = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.

Function Plus1 (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. omega.
- apply lt_wf.
Defined.
Definition x := 1.
Definition Plus1x := Plus1 x.
Eval vm_compute in Plus1x.


(** evaluation of [Function]s defined with measure or wf **
Time Quote Recursively Definition p_Plus1x := Plus1x.
Time Definition P_Plus1x : Program Term :=
  Eval vm_compute in program_Program p_Plus1x.
Time Definition P_ans :=
  Eval vm_compute in match P_Plus1x with
                       | mkPgm P_main P_env => wcbvEval P_env 1000 P_main
                     end.
Print P_ans.
(*********)
Time Definition P_env := Eval vm_compute in (env P_Plus1x).
Time Definition P_main := Eval vm_compute in (main P_Plus1x).
Time Definition P_ans := Eval vm_compute in (wcbvEval P_env 1000 P_main).
*********)
  

Function Gcd (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (b mod S k)  (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    omega.
  - exact lt_wf.
Defined.

(*** out of space ****
Definition Gcdx := (Gcd 4 2).
Eval cbv in Gcdx.
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx := Eval vm_compute in (program_Program pGcdx).
Time Definition Penv_Gcdx := env PGcdx.
Time Definition Pmain_Gcdx := main PGcdx.
Time Definition ans_Gcdx :=
 Eval vm_compute in (wcbvEval Penv_Gcdx 1000 Pmain_Gcdx).
Print ans_Gcdx.
***)


(** Andrew's example **
Function sqrt' (n x0 x diff: Z) {measure Z.to_nat diff} : Z :=
  (if diff =? 0 then x
   else let y := Z.div2 (x + Z.div n x)
        in if y =? x0 then Z.min x0 x
           else sqrt' n x y (y-x0))%Z.
Proof.
Admitted.

Quote Recursively Definition psqrt := sqrt'.
Definition Psqrt := Eval cbv in (program_Program psqrt).
****)

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
Definition vplus0123 := (vplus v01 v23).
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
  wcbvEval (env) 100 (main) = Ret ans_vplus0123.
  vm_compute. reflexivity.
Qed.

Inductive pack (A:Prop) : Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A) : nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Check p_pack_nat.
Definition P_pack_nat := Eval cbv in (program_Program p_pack_nat).
Print P_pack_nat.

Inductive xxxx : Set :=
| xxxxl: forall n:nat, n = 0 -> xxxx
| xxxxr: forall n:nat, n = 1 -> xxxx.
Print xxxx.
Definition Xxxx : xxxx := xxxxl eq_refl.
Definition yyyy (f:xxxx) :=
  match f with xxxxl q => f | xxxxr q => f end.
Definition yyyyX := (yyyy Xxxx).
Print yyyyX.
Quote Recursively Definition cbv_yyyyX := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (yyyyX)) in exact t).
Print cbv_yyyyX.
(* [Term] of Coq's answer *)
Definition ans_yyyyX := Eval cbv in (main (program_Program cbv_yyyyX)).
(* [program] of the program *)
Quote Recursively Definition p_yyyyX := yyyyX.
Print p_yyyyX.
Definition P_yyyyX := Eval cbv in (program_Program p_yyyyX).
Print P_yyyyX.
                       
Goal
    let env := (env P_yyyyX) in
    let main := (main P_yyyyX) in
    let ans :=  deProof ans_yyyyX in
    wcbvEval env 50 main = Ret ans.
Proof.
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
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in (main (program_Program cbv_arden_size)).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Print p_arden_size.
Definition P_arden_size := Eval cbv in (program_Program p_arden_size).
Print P_arden_size.
Goal
  let env := (env P_arden_size) in
  let main := (main P_arden_size) in
  wcbvEval (env) 100 (main) = Ret ans_arden_size.
  vm_compute. reflexivity.
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
Print cbv_ack35.
Definition ans_ack35 :=
  Eval cbv in (main (program_Program cbv_ack35)).
Print ans_ack35.
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Print p_ack35.
Definition P_ack35 := Eval cbv in (program_Program p_ack35).
Print P_ack35.
Goal
  let env := (env P_ack35) in
  let main := (main P_ack35) in
  wcbvEval (env) 2000 (main) = Ret ans_ack35.
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
  Eval cbv in (main (program_Program cbv_pierce)).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Print p_pierce.
Definition P_pierce := Eval cbv in (program_Program p_pierce).
Print P_pierce.
Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
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
  Eval cbv in (main (program_Program cbv_Scomb)).
Print ans_Scomb.
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Print p_Scomb.
Definition P_Scomb := Eval cbv in (program_Program p_Scomb).
Print P_Scomb.
Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
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
Quote Recursively Definition cbv_Foo0ty :=
  ltac:(let t:=(eval cbv in Foo0ty) in exact t).
Definition ans_Foo0ty :=
  Eval cbv in (main (program_Program cbv_Foo0ty)).
(* [program] of the program *)
Quote Recursively Definition p_Foo0ty := Foo0ty.
Definition P_Foo0ty := Eval cbv in (program_Program p_Foo0ty).
Goal
  let env := (env P_Foo0ty) in
  let main := (main P_Foo0ty) in
  wcbvEval (env) 30 (main) = Ret ans_Foo0ty.
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
  Eval cbv in (main (program_Program cbv_fib9)).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_Program p_fib9).
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
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
  Eval cbv in (main (program_Program cbv_sumPL_myPL)).
(* [program] of the program *)
Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval cbv in (program_Program p_sumPL_myPL).
Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
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
Definition myTree := (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).
Eval cbv in size myTree.
Definition size_myTree := size myTree.
Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval cbv in (main (program_Program cbv_size_myTree)).
(* [program] of the program *)
Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval cbv in (program_Program p_size_myTree).
Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 1000 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.

Require Import Benchmarks.vs.

(****** runs out of space **************
Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (L2.compile.program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := AstCommon.main P_myMain.
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 4000 P_main_myMain).
Set Printing Width 80.
Print eval_myMain.
************************)
