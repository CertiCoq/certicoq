
Require Import Recdef.
Require Import omega.Omega.
Require Import Template.Template.
Require Import Common.Common.
Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Set Template Cast Propositions.
Set Printing Width 80.
Set Printing Depth 1000.

Quote Recursively Definition p_Type := Type.
Print p_Type.
Definition P_Type := Eval cbv in (program_Program p_Type).
Print P_Type.

Notation NN := (mkInd "Coq.Init.Datatypes.nat" 0).
Notation SS := (TConstruct NN 1 1).
Notation ZZ := (TConstruct NN 0 0).
Notation LL := (mkInd "Coq.Init.Datatypes.list" 0).
Notation CONS := (TConstruct LL 1 3).
Notation NIL := (TConstruct LL 0 1).
Notation VSR := (mkInd "Benchmarks.vs.VeriStar.veristar_result" 0).
Notation VSR_Val := (TConstruct VSR 0).
Notation VSR_Modl := (TConstruct VSR 1).
Notation VSR_Abrt := (TConstruct VSR 2).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation tPi := (tProd).
Notation tPROP := (tSort sProp).
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
Notation "fn [| arg @ args |]" :=
  (TApp fn arg args)  (at level 90, left associativity).


(** Abhishek's example of looping: in L2 we don't test the guard **)
Require Import Arith.
Axiom AAax: Acc gt 0.
Fixpoint loop (n:nat) (x:nat) (a:Acc gt n) {struct a} : nat :=
  match n with
  | _ => @loop (S n) x (Acc_inv a (S n) (gt_Sn_n n))
  end.
Fixpoint pool (n:nat) (a:Acc gt n) {struct a} : nat -> nat :=
  match n with
  | _ => @pool (S n) (Acc_inv a (S n) (gt_Sn_n n))
  end.
Definition loop02 := @loop O 2.
Eval vm_compute in loop02.    (** Coq does not loop **)
Recursive Extraction loop02.
Definition pool0AAax := @pool O AAax.
Eval vm_compute in pool0AAax.    (** Coq does not loop **)
Recursive Extraction pool0AAax.

Definition loop02AAax := @loop O 2 AAax.
Eval vm_compute in loop02AAax.
Recursive Extraction loop02AAax.
Definition pool0AAax2 := @pool O AAax 2.
Eval vm_compute in pool0AAax2.
Recursive Extraction pool0AAax2.

(***********
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
*****************************)                      

Inductive P0: Prop := p0.
Inductive P1: Prop := p1.
Notation PP0 := (mkInd "P0" 0).
Notation pp0 := (TConstruct PP0 0 0).
Notation PP1 := (mkInd "P1" 0).
Notation pp1 := (TConstruct PP1 0 0).


Quote Recursively Definition p_and_rect := and_rect.
Print p_and_rect.
Eval cbv in (program_Program p_and_rect).

Definition and_rect_x :=
  (and_rect (fun (a:2=2) (b:True) => conj b a) (conj (eq_refl 2) I)).
Quote Recursively Definition p_and_rect_x := and_rect_x.
Definition P_and_rect_x := Eval cbv in (program_Program p_and_rect_x).
Print P_and_rect_x.
Quote Recursively Definition cbv_and_rect_x :=
  ltac:(let t:=(eval cbv in and_rect_x) in exact t).
Definition ans_and_rect_x :=
  Eval cbv in (main (program_Program cbv_and_rect_x)).
Definition envx := env P_and_rect_x.
Definition mainx := main P_and_rect_x.
Goal
  wcbvEval envx 90 mainx = Ret ans_and_rect_x.
  vm_compute. (******** HERE reflexivity.
Qed.
               *****************)
Abort.

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
Goal wcbvEval P_envx 1000 P_mainx = Ans_and_rectx.
vm_compute. reflexivity.
Qed.

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
  (my_and_rect (fun (a:2=2) (b:True) => conj b a) (conj (eq_refl 2) I)).
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
Compute slowFib3.
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Eval cbv in (program_Program cbv_slowFib3).
Definition ans_slowFib3 :=
  Eval cbv in (main (program_Program cbv_slowFib3)).
Print ans_slowFib3.
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Print p_slowFib3.
Definition P_slowFib3 := Eval cbv in (program_Program p_slowFib3).
Print P_slowFib3.
Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval env 30 main = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.

Definition div : forall x y, y > 0 -> { z | z*y <= x < (S z)*y }.
Proof.
  induction x as [x Hrec] using (well_founded_induction lt_wf).
  intros y Hy.
  case_eq (y <=? x); intros.  (* do we have y≤x or x<y ? *)
  (* first case: y≤x *)
  - pose proof (leb_complete _ _ H) as j1.
    assert (Hxy : x-y < x) by omega.
    destruct (Hrec (x-y) Hxy y Hy) as [z Hz]. (* ie: let z = div (x-y) y *)
    exists (S z); simpl in *; omega. (* ie: z+1 fits as (div x y) *)
  (* second case: x<y *)
  - pose proof (leb_complete_conv _ _ H).
    exists 0; omega.
Defined.
Print div.
Extraction div.

Definition funnyDiv: forall x y, { z | z*(S y) <= x < (S z)*(S y) }.
Proof.
  induction x as [x Hrec] using (well_founded_induction lt_wf).
  intros y.
  case_eq (S y <=? x); intros.
  - pose proof (leb_complete _ _ H) as j1.
    assert (Hxy : x-(S y) < x) by omega.
    destruct (Hrec (x- S y) Hxy y) as [z Hz]. (* ie: let z = div (x-y) y *)
    exists (S z); simpl in *; omega. (* ie: z+1 fits as (div x y) *)
  - pose proof (leb_complete_conv _ _ H).
    exists 0. cbn. omega.
Defined.
Print funnyDiv.
Extraction funnyDiv.

  
Function copy (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S p => S (copy p)
  end.
Admitted.
Print Assumptions copy.

Compute (copy 2).
Print copy_terminate.
(* Transparent copy_terminate. *)
(****
- intros. constructor. 
- apply lt_wf.
Defined.  
Print copy_tcc.

Print copy.
Definition x := 2.
Definition copyx := copy x.
Set Printing Width 200.
Compute copyx.
Print copy_terminate.   (* Opaque, but printable *)
Check (forall n:nat, {v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n = v}:Set).

Definition cp_term :=    (* Transparent *)
  (fun h:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt =>
 let H := h:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt in
 (fun _TmpHyp:(forall n p:nat, n = S p -> p < S p) /\ well_founded lt =>
  and_rec
    (fun (H0:forall n p:nat, n = S p -> p < S p) (H1:well_founded lt) (n:nat) =>
     let Acc_n := (let wf_R := H1:well_founded lt in wf_R n):Acc lt n in
     (fix hrec (n0:nat) (Acc_n0:Acc lt n0) {struct Acc_n0}:{v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n0 = v} :=
        match n0 as n1 return (n0 = n1 -> {v:nat | exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def n1 = v}) with
        | 0 =>
            fun _:n0 = 0 =>
            exist (fun v:nat => exists p:nat, forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def 0 = v) 0
              (ex_intro (fun p:nat => forall k:nat, p < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def 0 = 0) 1
                 (fun k:nat =>
                  match k as n1 return (1 < n1 -> forall def:nat -> nat, Recdef.iter (nat -> nat) n1 copy_F def 0 = 0) with
                  | 0 => fun h0:1 < 0 => False_ind (forall def:nat -> nat, Recdef.iter (nat -> nat) 0 copy_F def 0 = 0) (Nat.nlt_0_r 1 h0)
                  | S k0 => fun (_:1 < S k0) (def:nat -> nat) => eq_refl
                  end))
        | S p =>
            fun teq:n0 = S p =>
            sig_rec
              (fun _:{v:nat | exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = v} =>
               {v:nat | exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = v})
              (fun (rec_res:nat) (p2:exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = rec_res) =>
               exist (fun v:nat => exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = v) (S rec_res)
                 (ex_ind
                    (fun (x:nat) (H2:forall k:nat, x < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def p = rec_res) =>
                     max_type_ind 0 x (fun _:max_type 0 x => exists p0:nat, forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = S rec_res)
                       (fun (v:nat) (_:0 <= v) (l0:x <= v) =>
                        ex_intro (fun p0:nat => forall k:nat, p0 < k -> forall def:nat -> nat, Recdef.iter (nat -> nat) k copy_F def (S p) = S rec_res) (S v)
                          (fun k:nat =>
                           match k as n1 return (S v < n1 -> forall def:nat -> nat, Recdef.iter (nat -> nat) n1 copy_F def (S p) = S rec_res) with
                           | 0 => fun h0:S v < 0 => False_ind (forall def:nat -> nat, Recdef.iter (nat -> nat) 0 copy_F def (S p) = S rec_res) (Nat.nlt_0_r (S v) h0)
                           | S k0 => fun (h':S v < S k0) (def:nat -> nat) => eq_ind_r (fun n1:nat => S n1 = S rec_res) eq_refl (H2 k0 (Nat.le_lt_trans x v k0 l0 (lt_S_n v k0 h')) def)
                           end)) (max 0 x)) p2)) (hrec p (Acc_inv Acc_n0 (eq_ind_r (fun n1:nat => p < n1) (H0 n0 p teq) teq)))
        end eq_refl) n Acc_n) _TmpHyp) H) copy_tcc.

Compute (let (x, _) := cp_term 2 in x).

Time Quote Recursively Definition pcopyx := copyx.
Time Definition Pcopyx :=
  Eval vm_compute in (L2k.compile.program_Program pcopyx).
Time Definition Penv_copyx := env Pcopyx.
Time Definition Pmain_copyx := main Pcopyx.
Time Definition ans_copyx :=
 Eval vm_compute in (wcbvEval Penv_copyx 1000 Pmain_copyx).
Print ans_copyx.
*****************)

Function Gcd (a b:nat) {wf lt a}:nat :=
match a with
 | O => b 
 | S k => Gcd (b mod S k) (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    intros h. discriminate.
  - exact lt_wf.
Defined.
Print Gcd_tcc.
Definition Gcdx := (Gcd 4 2).
Eval cbv in Gcdx.
(***** runs out of memory here  ****
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx :=
  Eval vm_compute in (L2k.compile.program_Program pGcdx).
Time Definition Penv_Gcdx := env PGcdx.
Time Definition Pmain_Gcdx := main PGcdx.
Time Definition ans_Gcdx :=
 Eval vm_compute in (wcbvEval Penv_Gcdx 1000 Pmain_Gcdx).
Print ans_Gcdx.
***)



(***
(** Andrew's example **)
Function sqrt' (n x0 x diff: Z) {measure Z.to_nat diff}:Z :=
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
Definition v01:Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23:Vector.t nat 2 :=
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

Inductive pack (A:Prop):Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A):nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Check p_pack_nat.
Definition P_pack_nat := Eval cbv in (program_Program p_pack_nat).
Print P_pack_nat.

Inductive xxxx:Set :=
| xxxxl: forall n:nat, n = 0 -> xxxx
| xxxxr: forall n:nat, n = 1 -> xxxx.
Print xxxx.
Axiom Xxxx:xxxx.
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
    wcbvEval (env) 100 (main) = Ret ans_yyyyX.
  vm_compute. reflexivity.
Qed.

(** mutual recursion **)
Set Implicit Arguments.
Inductive tree (A:Set):Set :=
  node:A -> forest A -> tree A
with forest (A:Set):Set :=
     | leaf:A -> forest A
     | fcons:tree A -> forest A -> forest A.

Fixpoint tree_size (t:tree bool):nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool):nat :=
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
Fixpoint ackn (Ack:nat -> nat) (m:nat) {struct m}:nat :=
  match m with
  | 0 => Ack 1
  | S q => Ack (ackn Ack q)
  end.
Fixpoint Ack (n:nat) {struct n}:nat -> nat :=
  match n with
    | 0 => S
    | S p => ackn (Ack p)
  end.
Quote Recursively Definition p_Ack := Ack.
Print p_Ack.
Definition P_Ack := Eval cbv in (program_Program p_Ack).
Print P_Ack.
Time Compute Ack 3 7.

Fixpoint ACK (n:nat) {struct n}:nat -> nat :=
  match n with
    | 0 => S
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ACK p 1
                   | S q => ACK p (ackn q)
                 end
             in ackn
  end.
Quote Recursively Definition p_ACK := ACK.
Print p_ACK.
Definition P_ACK := Eval cbv in (program_Program p_ACK).
Print P_ACK.
Compute ACK 3 7.


Fixpoint ack (n m:nat) {struct n}:nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Compute ack 3 7.
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
Fixpoint tautArg (n:nat):Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat):tautArg n -> bool :=
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
Definition Foo:nat -> bool -> wwzz -> wwzz := 
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
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n}:nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib:nat -> nat := fun n => fibrec n (pair 0 1).
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
Inductive PList:Set->Type:=  (* powerlists *)
| zero:forall A:Set, A -> PList A
| succ:forall A:Set, PList (A * A)%type -> PList A.

Definition myPList:PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).

Fixpoint unzip (A:Set) (l:list (A*A)) {struct l}:list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList (A:Set) (l:PList A) {struct l}:list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Eval compute in PListToList myPList.

Fixpoint gen_sumPList (A:Set) (l:PList A) {struct l}:(A->nat)->nat :=
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
Variables X Y:Type.
Variable f:X -> Y -> Y.
Fixpoint fold (y:Y) (xs:list X):Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T:list Tree -> Tree.
Fixpoint size (t:Tree):nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
Definition myTree := (T (cons (T (unit (T nil)))
                              (cons (T (unit (T nil))) nil))).
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
Print Assumptions main.

(*** raises exception: out of time *****)
Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (program_Program p_ce_example_myent).
Definition P_env_ce_example_myent := env P_ce_example_myent.
Definition P_main_ce_example_myent := AstCommon.main P_ce_example_myent.
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 4500 P_main_ce_example_myent).
Set Printing Width 100.
Print eval_ce_example_myent.
**********************)

(********************
Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (L2k.compile.program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := AstCommon.main P_myMain.
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 8000 P_main_myMain).
Set Printing Width 100.
Print eval_myMain.
************)

(********************
Print Assumptions vs.main.
Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent :=
  Eval vm_compute in (program_Program p_ce_example_ent).
Time Definition P_env_ce_example_ent := env P_ce_example_ent.
Time Definition P_main_ce_example_ent := AstCommon.main P_ce_example_ent.
Time Definition eval_ce_example_ent :=
  Eval vm_compute in (wcbvEval P_env_ce_example_ent 1000 P_main_ce_example_ent).
Print eval_ce_example_ent.
**********************)
