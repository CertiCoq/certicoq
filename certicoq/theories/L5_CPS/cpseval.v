Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
(** 
Add LoadPath "../common" as Common.
Add LoadPath "./" as CPS.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
Add LoadPath "../L4_deBruijn" as L4. 
**)

Require Import Common.Common.
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Export CPS.cpstrans CPS.k_deBruijn CPS.u_deBruijn.

(** OPTIMISED Big-step evaluation for CPS expressions.
    Notice that only computations
    are evaluated -- values are inert so to speak. *)
Fixpoint find_branch_c (d:dcon) (m:N) (bs:branches_c) : option cps :=
  match bs with
    | brnil_c => None
    | brcons_c d' n e bs =>
      if eq_dec d d' then (if eq_dec n m then Some e else None)
                     else find_branch_c d m bs
  end.
(** Find the nth component in exps **)
Fixpoint cnthopt (n:nat) (xs:fnlst): option cps :=
  match n, xs with 
    | 0%nat, flcons h _ => Some h
    | S n, flcons _ t => cnthopt n t
    | _, _ => None
  end.

Fixpoint fnlength (es : fnlst) : nat :=
  match es with
  | flnil => 0
  | flcons _ l => S (fnlength l)
  end.

Definition sbst_fix (es:fnlst) (e : cps) : cps :=
  let les := fnlength es in
    fold_left
      (fun bod ndx => e{1 ::= Fix_c es (N.of_nat ndx)})
      (list_to_zero les) e.

Inductive eval_c: cps -> val_c -> Prop :=
| eval_Halt_c: forall v, eval_c (Halt_c v) v
| eval_Ret_c: forall c v v',
                 eval_c (c [0 ::= v]) v' -> 
                 eval_c (Ret_c (Cont_c c) v) v'
| eval_Call_c: forall c v1 v2 v',
                  eval_c (c [0::=v1]{0:=v2}) v' -> 
                  eval_c (Call_c (Lam_c c) v1 v2) v'
| eval_Match_c: forall d vs bs (c:cps) v',
                   find_branch_c d (vals_c_length vs) bs = Some c ->
                   eval_c (usubst_list c vs) v' -> 
                   eval_c (Match_c (Con_c d vs) bs) v'
| eval_Call_Fix_c: forall cs i c v1 v2 v',
                  cnthopt (N.to_nat i) cs = Some c -> 
                  eval_c ((sbst_fix cs c) [0::=v1]{0:=v2}) v' ->
                  eval_c (Call_c (Fix_c cs i) v1 v2) v'.
Hint Constructors eval_c.


(** Useful for rewriting. *)
Lemma eval_ret :
  forall c v v', eval_c (Ret_c (Cont_c c) v) v' <-> eval_c (c[0 ::= v]) v'.
Proof.
  intros. split; intro. inversion H. subst; auto. constructor; auto.
Qed.
Lemma eval_call :
  forall c v1 v2 v',
    eval_c (Call_c (Lam_c c) v1 v2) v' <-> eval_c (c[0::=v1]{0:=v2}) v'.
Proof.
  intros; split; intro. inversion H; subst; auto. constructor; auto.
Qed.
Lemma eval_match :
  forall d vs bs v' c,
    find_branch_c d (vals_c_length vs) bs = Some c -> 
    (eval_c (Match_c (Con_c d vs) bs) v' <-> (eval_c (usubst_list c vs) v')).
Proof.
  intros; split; intro. inversion H0; subst. rewrite H in H5. injection H5 ;
    intros; subst. auto.
  econstructor; eauto.
Qed.
Lemma eval_fix :
  forall cs i c v1 v2 v',
    cnthopt (N.to_nat i) cs = Some c ->
    (eval_c (Call_c (Fix_c cs i) v1 v2) v' <->
     eval_c ((sbst_fix cs c) [0::=v1]{0:=v2}) v').
Proof.
  intros; split; intro. inversion H0; subst.
  rewrite H in H6. injection H6; intros; subst.
  auto. econstructor; eauto.
Qed.


(** UNOPTIMISED evaluation **)
Inductive ueval_c: cps -> val_c -> Prop :=
| ueval_Halt_c: forall v, ueval_c (Halt_c v) v
| ueval_Ret_c: forall c v v',
                 ueval_c (c [0 ::= v]) v' -> 
                 ueval_c (Ret_c (Cont_c c) v) v'
| ueval_Call_c: forall c v1 v2 v',
                  ueval_c (c [0::=v1]{0::=v2}) v' -> 
                  ueval_c (Call_c (Lam_c c) v1 v2) v'
| ueval_Match_c: forall d vs bs c v',
                   find_branch_c d (vals_c_length vs) bs = Some c ->
                   ueval_c (usbst_list c vs) v' -> 
                   ueval_c (Match_c (Con_c d vs) bs) v'
| ueval_Fix_c: forall cs i c v1 v2 v',
                  cnthopt (N.to_nat i) cs = Some c -> 
                  ueval_c ((sbst_fix cs c) [0::=v1]{0::=v2}) v' ->
                  ueval_c (Call_c (Fix_c cs i) v1 v2) v'.
Hint Constructors ueval_c.

(** Useful for rewriting. *)
Lemma ueval_ret :
  forall c v v', ueval_c (Ret_c (Cont_c c) v) v' <-> ueval_c (c[0 ::= v]) v'.
Proof.
  intros. split; intro. inversion H. subst; auto. constructor; auto.
Qed.
Lemma ueval_call :
  forall c v1 v2 v',
    ueval_c (Call_c (Lam_c c) v1 v2) v' <-> ueval_c (c[0::=v1]{0::=v2}) v'.
Proof.
  intros; split; intro. inversion H; subst; auto. constructor; auto.
Qed.
Lemma ueval_match :
  forall d vs bs v' c,
    find_branch_c d (vals_c_length vs) bs = Some c -> 
    (ueval_c (Match_c (Con_c d vs) bs) v' <-> (ueval_c (usbst_list c vs) v')).
Proof.
  intros; split; intro. inversion H0; subst. rewrite H in H5. injection H5 ;
    intros; subst. auto.
  econstructor; eauto.
Qed.
Lemma ueval_proj :
  forall cs i c v1 v2 v',
    cnthopt (N.to_nat i) cs = Some c ->
    (ueval_c (Call_c (Fix_c cs i) v1 v2) v' <->
     ueval_c ((sbst_fix cs c) [0::=v1]{0::=v2}) v').
Proof.
  intros; split; intro. inversion H0; subst. rewrite H in H6.
  injection H6; intros; subst.
  auto. econstructor; eauto.
Qed.

(** A fuel-based interpreter. *)
Inductive ans :=
| Value: val_c -> ans
| RetTypeError: val_c -> ans 
| CallTypeError: val_c -> ans
| MatchMissingCaseError: ans
| MatchTypeError: val_c -> ans 
| ProjError
| Fuel: cps -> ans.

(* unoptimised fuel based interpreter *)
Function ueval_c_n (n:nat) (c:cps): ans := 
  match n with
    | 0%nat => Fuel c
    | S n => match c with
               | Halt_c v => Value v
               | Ret_c (Cont_c c) v => ueval_c_n n (c[0 ::= v])
               | Ret_c v _ => RetTypeError v
               | Call_c (Lam_c c) v1 v2 => ueval_c_n n (c[0 ::= v1]{0 ::= v2})
               | Call_c (Fix_c cs i) v1 v2 =>
                 match cnthopt (N.to_nat i) cs with
                   | None => ProjError
                   | Some c => ueval_c_n n ((sbst_fix cs c) [0::=v1]{0 ::= v2})
                 end
               | Match_c (Con_c d vs) bs =>
                 match find_branch_c d (vals_c_length vs) bs with
                   | Some c => ueval_c_n n (usbst_list c vs)
                   | None => MatchMissingCaseError
                 end
               | Match_c v _ => MatchTypeError v
               | Call_c v _ _ => CallTypeError v
             end
  end.

(** sanity checks for evaluation **)
Lemma eval_c_n_Value_Succ:
  forall e (n:nat) v, ueval_c_n n e = Value v -> n = (S (n - 1))%nat.
Proof.
  induction n; intros.
  - simpl in H. discriminate.
  - omega.
Qed.

Lemma ueval_c_n_monotone:
  forall (n:nat) e u, ueval_c_n n e = Value u ->
                forall (m:nat), (n < m)%nat -> ueval_c_n m e = Value u.
Proof.
  intros n e u.
  functional induction (ueval_c_n n e); intros; try discriminate;
  assert (h:m = S (m - 1)); try lia; rewrite h; clear h; simpl.
  - assumption.
  - specialize (IHa H). apply IHa. lia.
  - specialize (IHa H). apply IHa. lia.
  - rewrite e1. specialize (IHa H). apply IHa. lia.
  - rewrite e1. specialize (IHa H). apply IHa. lia.
Qed.

(** evaluation relation and fuel-based interpreter are equivalent **)
Lemma uueval_c_iff_uueval_c_n:
  forall c v, ueval_c c v <-> (exists n, ueval_c_n n c = Value v).
Proof.
  Ltac dex := match goal with | [ H: exists _, _ |- _ ] => destruct H end.
  intros. split; intros h.
  { induction h; simpl; repeat dex. 
    - exists 1%nat. auto.
    - exists (S x); auto. 
    - exists (S x); auto. 
    - exists (S x). simpl. rewrite H. auto.
    - exists (S x); simpl. rewrite H. auto. }
  { destruct h as [n H1]. generalize c v H1. clear c v H1.
    induction n; simpl; intros.
    - discriminate.
    - destruct c. 
      + injection H1. intros; subst. constructor.
      + destruct v0; try discriminate. constructor. auto.
      + destruct v0; try discriminate.
        * constructor. auto.
        * remember (cnthopt (N.to_nat n0) f) as e.
          destruct e; try discriminate.
          econstructor. rewrite <-Heqe. reflexivity.
          eauto. 
      + destruct v0; try discriminate.
        remember (find_branch_c d (vals_c_length v0) b) as e.
        destruct e; try discriminate. specialize (IHn _ _ H1).
        econstructor; eauto. }
Qed.

Lemma ueval_single_valued:
  (forall e v, ueval_c e v -> forall u, ueval_c e u -> v = u).
Proof.
  intros e v h0 u h1. 
  destruct (proj1 (uueval_c_iff_uueval_c_n _ _) h0) as [n0 j0].
  destruct (proj1 (uueval_c_iff_uueval_c_n _ _) h1) as [n1 j1].
  assert (j2:(n0 < n1 \/ n0 = n1 \/ n1 < n0)%nat). omega.
  destruct j2 as [j3|[j3|j3]].
  - rewrite (ueval_c_n_monotone _ _ _ j0) in j1; try assumption.
    injection j1; intros j4. subst. reflexivity.
  - subst. rewrite j0 in j1. injection j1; intros j4. subst. reflexivity.
  - rewrite (ueval_c_n_monotone _ _ _ j1) in j0; try assumption.
    injection j0; intros j4. subst. reflexivity.
Qed.


(*** false because I omitted optimisation in cps_cvt for
**** Con es when [are_values es] 
**** will coe back to this.
Lemma cps_val' :
  (forall e, is_value e ->
             cps_cvt e = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val e))) /\
  (forall es, are_values es ->
        forall d, cps_cvt (Con_e d es) =
        Cont_c (Ret_c (KVar_c 0) (Con_c d (cps_cvt_vals es)))).
Proof.
  apply my_is_value_ind; simpl; intros; auto.
  - 


Lemma cps_val' :
  (forall e, is_value e ->
             cps_cvt e = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val e))) /\
  (forall es, are_values es ->
     forall d es', are_values es' -> 
        cps_cvt (Con_e d (exps_append es' es)) =
        Cont_c (Ret_c (KVar_c 0)
                      (Con_c d (cps_cvt_vals (exps_append es' es))))).
Proof.
  apply my_is_value_ind; simpl; intros; auto.
  - specialize (H d enil). simpl in H. auto. 
  - repeat rewrite exps_append_r. simpl. fold are_valuesb.
    + Check (proj2 (are_valuesb_corr es') H).
    rewrite (are_valuesb_corr es') H). auto.
  simpl. fold are_valuesb.
  rewrite (proj2 (are_valuesb_corr (es' ++ (e::es)))); auto.
  rewrite <- are_values_append. auto.
Qed.

Lemma cps_val :
  forall v, is_value v -> cps_cvt v = Cont_c (Ret_c (KVar_c 0) (cps_cvt_val v)).
Proof.
  intros. apply (proj1 cps_val'). auto.
Qed.
****)


(** tests of translation and evaluation **)
Definition unvalue (x:ans) : val_c := (* for use in examples *)
  match x with 
    | Value v => v
    | _ => Var_c 9999
  end.

(* apply ueval_c directly to exp *)
Definition ueval_ce_n (n:nat) (e:exp) : ans :=
  ueval_c_n n (cps_cvt_prog e).
(* apply eval_c directly to exp *)
Definition ueval_ce (e f:exp) :=
  ueval_c (cps_cvt_prog e) (unvalue (ueval_ce_n 5000 f)).
(* apply eval_c directly to exp *)
Definition eval_ce (e f:exp) :=
  eval_c (cps_cvt_prog e) (unvalue (ueval_ce_n 5000 f)).


Eval compute in
    ueval_c_n 10 (Ret_c (Cont_c (Halt_c (Var_c 0))) (Con_c 9 vcnil)).

Eval cbv in (Var_c 0){0::= Var_c 9}.
Eval cbv in (Halt_c (Var_c 0)){0::= Var_c 9}.

Eval vm_compute in (cps_cvt_prog (App_e (Var_e 0) (Var_e 9))).
Eval vm_compute in ueval_c_n 10 (cps_cvt_prog (App_e (Var_e 0) (Var_e 9))).

Example d1: exp := App_e (Lam_e (Con_e 5 enil)) (Con_e 10 enil).
Eval vm_compute in ueval_c_n 10 (cps_cvt_prog d1).

Example d2: exp := App_e (Lam_e (Var_e 0)) (Con_e 10 enil).
Eval vm_compute in ueval_c_n 10 (cps_cvt_prog d2).

Example e1: exp := Lam_e (Var_e 0).  (* identity *)
Example e1': exp := App_e e1 (Con_e 10 enil).
Eval vm_compute in (ueval_c_n 100 (cps_cvt_prog e1')).

Example e2: exp := App_e e1 e1.  (* (fun x => x) (fun x => x) *)
Example e2': exp := App_e e2 (Con_e 9 enil).
Eval vm_compute in ueval_c_n 100 (cps_cvt_prog e2').

Eval vm_compute in   (** SKKe defined above **)
       ueval_c_n 100 (cps_cvt_prog (App_e SKKe (Con_e 9 enil))).


(** natural numbers in Church representation **)
Section ChurchNaturals.
Notation ZZ := (Lam_e (Lam_e Ve1)).
Notation SS := (Lam_e (Lam_e (Lam_e (Ve0 $ (Ve2 $ Ve1 $ Ve0))))).
Notation one := (SS $ ZZ).
Notation two := (SS $ one).
Notation three := (SS $ two).
Notation four := (SS $ three).
Notation five := (SS $ four).
Notation six := (SS $ five).
Notation add := (Lam_e (Lam_e (Ve1 $ Ve0 $ SS))).
Notation mul := (Lam_e (Lam_e (Ve1 $ ZZ $ (add $ Ve0)))).

Example One := Eval vm_compute in (ueval_ce_n 50 one). 
Example Two := Eval vm_compute in (ueval_ce_n 50 two).
Example Three := Eval vm_compute in (ueval_ce_n 50 three).
Example Four := Eval vm_compute in (ueval_ce_n 50 four).
Example Five := Eval vm_compute in (ueval_ce_n 50 five).
Example Six := Eval vm_compute in (ueval_ce_n 50 six).

Goal (ueval_ce_n 10 (SS $ ZZ)) = One.
vm_compute. reflexivity. Qed.
Goal (eval_ce (SS $ ZZ)) one.
repeat (try (econstructor; vm_compute)). Qed.
Goal (ueval_ce (SS $ ZZ)) one.
repeat (try (econstructor; vm_compute)). Qed.

Goal ueval_ce_n 100 (add $ ZZ $ one) = One.
vm_compute. reflexivity. Qed.
Goal (eval_ce (add $ ZZ $ one)) one.
repeat (try (econstructor; vm_compute)). Qed.
Goal (ueval_ce (add $ ZZ $ one)) one.
repeat (try (econstructor; vm_compute)). Qed.

Goal (ueval_ce_n 100 (add $ two $ one)) = Three.
vm_compute. reflexivity. Qed.
Goal (eval_ce (add $ two $ one)) three.
repeat (try (econstructor; vm_compute)). Qed.
Goal (ueval_ce (add $ two $ one)) three.
repeat (try (econstructor; vm_compute)). Qed.

Goal (ueval_ce_n 100 (add $ two $ three)) = Five.
vm_compute. reflexivity. Qed.
Goal (eval_ce (add $ two $ three)) five.
repeat (try (econstructor; vm_compute)). Qed.
Goal (ueval_ce (add $ two $ three)) five.
repeat (try (econstructor; vm_compute)). Qed.

Goal (ueval_ce_n 500 (mul $ two $ three)) = Six.
vm_compute. reflexivity. Qed.
Goal (eval_ce (mul $ two $ three)) six.
repeat (try (econstructor; vm_compute)). Qed.
Goal (ueval_ce (mul $ two $ three)) six.
repeat (try (econstructor; vm_compute)). Qed.
End ChurchNaturals.

Reset ChurchNaturals.

(** booleans using native data constructors (Notations in "expression.v") **)
Goal (ueval_ce_n 500 (ite $ TTT $ FFF $ TTT)) = (ueval_ce_n 999 FFF).
vm_compute. reflexivity. Qed.
Goal eval_ce (ite $ TTT $ FFF $ TTT) FFF.
repeat (try vm_compute; try econstructor). Qed.
Goal eval_ce (ite $ TTT $ FFF $ TTT) FFF.
repeat (try vm_compute; try econstructor). Qed.

Goal (ueval_ce_n 500 (ite $ FFF $ FFF $ TTT)) = (ueval_ce_n 999 TTT).
vm_compute. reflexivity. Qed.
Goal eval_ce (ite $ TTT $ FFF $ TTT) FFF.
repeat (try vm_compute; try econstructor). Qed.
Goal ueval_ce (ite $ TTT $ FFF $ TTT) FFF.
repeat (try vm_compute; try econstructor). Qed.

(** Natural numbers using native data constructors **)
Notation ZZ := (0:dcon).
Notation ZZZ := (Con_e ZZ enil).
Notation SS := (1:dcon).
Notation SSS := (Lam_e (Con_e SS [|Ve0|])).
Notation one := (SSS $ ZZZ).
Notation two := (SSS $ one).
Notation three := (SSS $ two).
Notation four := (SSS $ three).
Notation five := (SSS $ four).
Notation six := (SSS $ five).

Definition one1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog one).
Goal ueval_c (cps_cvt_prog one) (unvalue one1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.
Goal eval_c (cps_cvt_prog one) (unvalue one1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

Definition two1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog two).
Goal ueval_c (cps_cvt_prog two) (unvalue two1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.
Goal eval_c (cps_cvt_prog two) (unvalue two1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

Definition three1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog three).
Goal ueval_c (cps_cvt_prog three) (unvalue three1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

Definition four1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog four).
Goal ueval_c (cps_cvt_prog four) (unvalue four1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

Definition five1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog five).
Goal ueval_c (cps_cvt_prog five) (unvalue five1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

Definition six1 := Eval vm_compute in ueval_c_n 100 (cps_cvt_prog six).
Goal ueval_c (cps_cvt_prog six) (unvalue six1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.
Goal eval_c (cps_cvt_prog six) (unvalue six1).
unfold cps_cvt_prog. simpl.
repeat (try econstructor; try vm_compute).
Qed.

(** Match **)

Eval vm_compute in ueval_ce_n 100 (cdr $ Nil).
Eval vm_compute in ueval_ce_n 100 (cdr $ (Cons $ TTT $ Nil)).
Eval vm_compute in ueval_ce_n 100 (cdr $ (Cons $ FFF $ (Cons $ TTT $ Nil))).

(** fixpoint **)
Eval vm_compute in ueval_ce_n 100 (copy $ ZZZ).
Eval vm_compute in ueval_ce_n 100 (copy $ one).

Require Import L4.L3_to_L4.

Definition compile (p : program) : exception cps :=
  do e <- program_exp p; Ret (cps_cvt_prog e).

Definition run (p : program) : exception ans :=
  do c <- compile p; Ret (ueval_c_n 1000 c).

(** Testing the compiler *)

(**)
Add LoadPath "../template-coq-coq-8.5/theories" as Template. 
(**)
Require Import Template.Template.
Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1%nat).

Quote Definition q_typedef := Eval compute in typedef.
Quote Recursively Definition p_typedef := typedef.
Eval compute in (malecha_L1.program_Program p_typedef (Ret nil) :
                   exception program.Program).

Definition L1_typedef : exception program.Program :=
  Eval compute in malecha_L1.program_Program p_typedef (Ret nil).

Definition P_typedef := Eval compute in program_exp p_typedef.

Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0%nat => 0
    | S m => match m with
               | 0%nat => 1
               | S p => slowFib p + slowFib m
             end
  end.

Fixpoint idn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => S (idn n) end.

Definition matchn (n : nat) : nat :=
  match n with 0%nat => 0 | S n => n end.




Quote Recursively Definition p_0 := 0.
Quote Recursively Definition p_idn := idn.
Quote Recursively Definition p_idn1 := (idn 1).



Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Recursively Definition p_matchn := (matchn 1).

Quote Recursively Definition p_add := Nat.add.
Quote Recursively Definition p_add01 := (Nat.add 0%nat 1).
Transparent N.add.
Eval compute in program_exp p_add.

Definition paddexp := Eval compute in compile p_add.

Definition padd01 := Eval compute in compile p_add01.


Eval compute in run p_0.

Eval compute in program_exp p_add01.
Eval compute in run p_add01.
Eval compute in program_exp p_matchn.
Eval compute in run p_matchn.

Eval compute in program_exp p_idn.
Eval compute in program_exp p_idn1.
Eval compute in run p_idn1.

Eval compute in run p_add01.
