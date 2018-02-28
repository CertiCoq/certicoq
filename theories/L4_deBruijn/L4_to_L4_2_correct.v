Require Import BinNat.
Require Import BinPos.
Require Import Omega.
Require Import Psatz.
Require Import Arith.
Require Import PArith.
Require Import NArith.
Require Import L4.expression.
Require Import Basics.

Require Import L4.polyEval.
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.

Require Import SquiggleEq.tactics.
Require Import Coq.Unicode.Utf8.
Require Import List.
Require Import SquiggleEq.list.



Open Scope program_scope.


Open Scope N_scope.
Require Import L4.variables.



Require Import SquiggleEq.termsDB.
Require Import Libraries.CpdtTactics.

(* Move to expression.v *)
Lemma EfnListSbst a m e:
  efnlst_as_list (sbst_efnlst a m e)
  = map (fun p => (fst p, sbst a m (snd p))) (efnlst_as_list e).
Proof using.
  induction e; crush.
Qed.

(* Move to expression.v *)
Lemma EfnListLength e:
  efnlst_length e
  = NLength (efnlst_as_list e).
Proof using.
  unfold NLength.
  induction e; auto.
  Local Opaque N.of_nat.
  Local Opaque N.add.
  simpl. lia.
  Local Transparent N.of_nat.
  Local Transparent N.add.
Qed.

Require Import L4.L4_to_L4_1_to_L4_2.


(** Move to L4_to_L4_1_to_L4_2.v *)
Lemma mkNamesLengthNat p : length (mkNames p) = N.to_nat (fst p).
Proof using.
  unfold mkNames. destruct p.
  simpl. unfold NLength. rewrite  listPad_length_eq; [lia | ].
  apply firstn_le_length.
Qed.

(** Move to L4_to_L4_1_to_L4_2.v *)
Lemma mkNamesLength p : NLength (mkNames p) = fst p.
Proof using.
  unfold mkNames. destruct p.
  simpl. unfold NLength. rewrite  listPad_length_eq; [lia | ].
  apply firstn_le_length.
Qed.

Require Import Common.TermAbs.


Lemma  substCommutesL4_to_L4_1 (a:exp) :
  (∀ (e : exp) m, tL4_to_L4_1 (sbst a m e) = subst_aux (tL4_to_L4_1 a) m (tL4_to_L4_1 e))
  /\
  (∀ (es : exps) m, ltL4_to_L4_1 (sbsts a m es)
                    = map (subst_aux (tL4_to_L4_1 a) m) (ltL4_to_L4_1 es))
  /\
  (∀ (es : efnlst) m, ftL4_to_L4_1 (sbst_efnlst a m es)
                      = map (subst_aux (tL4_to_L4_1 a) m) (ftL4_to_L4_1 es))
  /\
  (∀ (es : branches_e) m, btL4_to_L4_1 (sbst_branches a m es)
                          = map (fun b: (@branch L4Opid (TermAbsDBUnstrict Ast.name L4Opid))
                                 => let (d,bt) := b in
                                   (d, subst_aux_bt (tL4_to_L4_1 a) m bt)) (btL4_to_L4_1 es)).
Proof using.
  clear.
  apply my_exp_ind;
    simpl; unfold compose in *; crush;[ | | | | ].
  (* 1 var case. and the remaining ones need another induction *)
- simpl. (* variables *) 
  pose proof (N.compare_spec n m) as Hc. remember (n ?= m) as cmp.
  destruct cmp; inverts Hc; subst; auto; [ | | ];
  cases_ifd Hn; simpl in *; try cases_ifd Hnn; try lia; auto.
- (* data constructor *)
  repeat rewrite map_map. unfold compose. repeat rewrite map_length. refl.
- rewrite <- H0. rewrite <- H. simpl.
  repeat rewrite map_map. unfold compose. repeat rewrite map_length.
  rewrite H0.  repeat rewrite map_map. unfold compose. simpl. clear.
  do 2 f_equal.
  + unfold num_bvars.
    erewrite map_ext;
      [ |
        intros; rewrite rewritePairMatch; simpl;  rewrite get_bcvars_subst_aux_bt; refl]. refl.
  + erewrite map_ext;
      [ |
        intros; rewrite rewritePairMatch; refl]. simpl. refl.
- repeat rewrite map_map. unfold compose. repeat rewrite map_length.
  clear H.
  f_equal.  simpl. unfold fnames.
  rewrite EfnListSbst. rewrite map_map. unfold compose. simpl.
  rewrite EfnListLength. unfold NLength.
  rewrite map_length. refl.
- do 3 f_equal. fold (mkNames (a0,b)).
  rewrite mkNamesLength. refl.
Qed.

Lemma  lsubstCommutesL4_to_L4_1: ∀ (d : exp) (le : list exp),
    tL4_to_L4_1 (sbst_real_list d le)
    = subst_aux_list 0 (tL4_to_L4_1 d) (map tL4_to_L4_1 le).
Proof using.
  intros. unfold sbst_real_list. unfold subst_aux_list. revert d.
  induction le; simpl; auto.
  intros d. rewrite <- IHle. 
  simpl. generalize (fold_right (λ v ee : exp, sbst v 0 ee) d le).
  intros. apply substCommutesL4_to_L4_1.
Qed.


Print Assumptions eval_evaln.

Definition  eval41 := @polyEval.eval_n (TermAbsDBUnstrict Ast.name L4Opid).


(* Move to expression.v *)
Lemma ftL4_to_L4_1_list es:
map (tL4_to_L4_1 ∘ snd) (efnlst_as_list es) =  (ftL4_to_L4_1 es).
Proof using.
  induction es; crush.
Qed.

(* Move to expression.v *)
Lemma ltL4_to_L4_1_list es:
map (tL4_to_L4_1) (exps_as_list es) =  (ltL4_to_L4_1 es).
Proof using.
  induction es; crush.
Qed.

(* Move to expression.v *)
Lemma bL4_to_L4_1_list es:
  map (fun b:(expression.dcon * (N * list Ast.name) * exp) =>
         let (b,e) := b in
         let (d,n) := b in
         (d, bterm (mkNames n) (tL4_to_L4_1 e)))
      (branches_as_list es)
  =  (btL4_to_L4_1 es).
Proof using.
  induction es; crush.
Qed.

(*
Definition find_branch_as_find (lb: list (expression.dcon * (N * list Ast.name) * exp)) d m:=
  find (fun b:(expression.dcon * (N * list Ast.name) * exp) =>
         let (b,_) := b in
         let (db,dn) := b in
         decide ((d,m) = (db, fst dn))) lb.
 *)

Lemma NNateqb (a b:nat):
  Nat.eqb a b = N.eqb (N.of_nat a) (N.of_nat b).
Proof using.
  pose proof (Nat.eqb_spec a b) as H.
  pose proof (N.eqb_spec (N.of_nat a) (N.of_nat b)) as Hh.
  destruct (Nat.eqb a b),(N.of_nat a =? N.of_nat b); inverts H; inverts Hh; try lia; refl.
Qed.  

Definition find_branchb d (b: (expression.dcon * (N * list Ast.name) * exp)) : bool :=
         let (b,_) := b in
         let (db,dn) := b in
         decide ((d) = (db)).

Lemma Nateqb_eqdec {A:Type} (t e : A) n1 n2:
  (if (Nat.eqb n1 n2) then t else e)
  = if (Nat.eq_dec n1 n2) then t else e.
Proof using.
  symmetry.
  cases_if;[subst; rewrite Nat.eqb_refl; refl| ].
  apply Nat.eqb_neq in H.
  rewrite H. refl.
Qed.

Lemma Neqb_eqdec {A:Type} (t e : A) n1 n2:
  (if (N.eqb n1 n2) then t else e)
  = if (N.eq_dec n1 n2) then t else e.
Proof using.
  symmetry.
  cases_if;[subst; rewrite N.eqb_refl; refl| ].
  apply N.eqb_neq in H.
  rewrite H. refl.
Qed.

Lemma find_branch_as_find_correct d l b:
  expression.find_branch d (N.of_nat l) b
  = match (find (find_branchb d) (branches_as_list b)) with
    | Some a => if decide (l = N.to_nat (fst (snd (fst a)))) then Some (snd a) else None
    | None => None
    end.
Proof using.
  induction b;[refl | ].
  Local Opaque classes.eq_dec.
  simpl.
  cases_if; subst;[ rewrite deq_refl | symmetry; rewrite decide_decideP; cases_if; cpx].
  Local Transparent classes.eq_dec.
  simpl.
  rewrite Nat.eqb_sym.
  rewrite NNateqb.
  rewrite N2Nat.id.
  unfold nargs.
  setoid_rewrite <- Neqb_eqdec.
  refl.
Qed.

(* Move to expression.v *)
Lemma ltL4_to_L4_1_from_list es:
map (tL4_to_L4_1) es  = (ltL4_to_L4_1 (exps_from_list es)).
Proof using.
  induction es; crush.
Qed.



(* Move to expression.v *)
Lemma efnlst_as_list_len es:
  length (efnlst_as_list es) =  efnlength es.
Proof using.
  induction es; crush.
Qed.

(* Move to expression.v *)
Lemma exps_as_list_len es:
  NLength (exps_as_list es) =  exps_length es.
Proof using.
  unfold NLength.
  induction es; [refl | ].
  simpl exps_as_list. simpl length.
  Local Opaque N.add.
  simpl exps_length.
  lia.
  Local Transparent N.add.
Qed.

(* Move to expression.v *)
Lemma enthopt_translate n es:
option_map tL4_to_L4_1 (enthopt (N.to_nat n) es) = nth_error (ftL4_to_L4_1 es) (N.to_nat n).
Proof using.
 revert es.
 induction n using N.peano_rect; simpl; destruct es as [ | he es]; simpl;
   try rewrite N2Nat.inj_succ; simpl; eauto.
Qed.

(*
Lemma evals_commute_L4_to_L4_1 m
      (Hind1: ∀ (e : exp), option_map tL4_to_L4_1 (expression.eval_n (pred m) e)
                          =  eval41 (pred m) (tL4_to_L4_1 e))
      (Hind2: ∀ (e : exp), option_map tL4_to_L4_1 (expression.eval_n m e)
                          =  eval41 m (tL4_to_L4_1 e)):
  forall es,
    option_map ltL4_to_L4_1 (eval_ns m es) =
    ExtLibMisc.flatten (map (eval41 (pred m)) (ltL4_to_L4_1 es)).
Proof using.
  revert Hind1 Hind2.
  clear. intros ? ? ?.
  destruct m;[ apply False_rect; omega | ].
  induction es;[ refl| ].
  simpl evals_n at 1. simpl.
  simpl Nat.pred in IHes.
  simpl Nat.pred in Hind1.
  simpl.
  rewrite <- Hind1.
  clear Hind1.
  destruct  (expression.eval_n m e); [ | refl].
  simpl.
  setoid_rewrite <- IHes.
  remember ( S m) as sm.
  
  simpl.
.  
    (* unprovable. fuel needs to go down in polyEval. *)
Abort.
 *)
Local Opaque mkNames.  
Arguments num_bvars {Name} {Opid} / bt.
Hint Rewrite mkNamesLengthNat: list.

Lemma  evalCommLemma m:
  (∀ (e : exp), option_map tL4_to_L4_1 (expression.eval_ns m e) =  eval41 m (tL4_to_L4_1 e))
(*  /\
  (∀ (es : exps), option_map ltL4_to_L4_1 (expression.evals_n m es)
                    = ExtLibMisc.flatten (map (eval41 m) (ltL4_to_L4_1 es)))
  /\
  (∀ (es : efnlst), True)
  /\
  (∀ (es : branches_e), True) *).
Proof using.
  induction m  as [ m Hind] using lt_wf_ind.
  destruct m;[ refl | ].
  pose proof (Hind m ltac:(omega)) as IHm.
  clear Hind.
  destruct e; auto.
- simpl.
  do 2 rewrite <- IHm.
  (*clear IHm. needed one more time *)
  destruct (expression.eval_ns m e1) as [f | ]; simpl; [ | refl].
  destruct f; try refl;[ | | ]; simpl.
  + (* lambda *)
    destruct (expression.eval_ns m e2) as [a | ]; simpl; try refl.
    pose proof (substCommutesL4_to_L4_1 a) as X.
    repnd.
    crush; fail.
  + (* fix *)
    destruct (expression.eval_ns m e2) as [a | ]; simpl; try refl.
    unfold mkBTerm.
    rewrite flatten_map_Some. simpl.
    unfold select.
    rewrite nth_error_map.
    rewrite <- enthopt_translate.
    destruct (enthopt (N.to_nat n) e); simpl; [ | refl].
    unfold num_bvars. simpl.
    autorewrite with list.
    unfold fnames.
    rewrite <- ftL4_to_L4_1_list at 1.
    repeat rewrite map_length.
    rewrite Nat.eqb_refl.
    simpl.
    rewrite IHm. clear IHm. simpl.
    unfold compose. simpl.
    do 4 f_equal.
    rewrite sbst_fix_real.
    rewrite lsubstCommutesL4_to_L4_1.
    f_equal.
    repeat rewrite map_map.
    unfold compose.
    simpl.
    erewrite map_ext;[ | intros; rewrite Nat2N.id; refl].
    symmetry.
    unfold fnames.
    f_equal.
    rewrite <- ftL4_to_L4_1_list.
    autorewrite with list.
    rewrite efnlst_as_list_len. refl.
  +(* Prf_e *)
    destruct (expression.eval_ns m e2); simpl; refl.
- simpl.
  repeat rewrite map_map. unfold compose.
  simpl.
  rewrite  <-  ltL4_to_L4_1_list.
  rewrite map_map. unfold compose.
  symmetry.
  erewrite map_ext;[ | intros; symmetry; apply IHm].
  simpl.
  rewrite <-fold_option_map.
  repeat setoid_rewrite <- opmap_flatten_map2.
  rewrite option_map_map.
  simpl. autorewrite with list.
  remember (ExtLibMisc.flatten (map (eval_ns m) (exps_as_list e))) as fl.
  symmetry in Heqfl.
  destruct fl;[ | refl].
  simpl. rewrite map_map. unfold compose.
  f_equal. rewrite <- ltL4_to_L4_1_from_list.
  rewrite map_map. f_equal.
  f_equal.
  apply flattenSomeImpliesLen in Heqfl.
  autorewrite with list in *. assumption.
- simpl. rewrite <- IHm.
  destruct (eval_ns m e) as [disc | ];[ simpl |  refl].
  destruct disc; try refl;[]. simpl.
  rename e0 into es.
  rewrite map_map. unfold compose. simpl.
  rewrite flatten_map_Some.
  rewrite map_map. unfold compose. simpl.
  rewrite combine_eta.
  autorewrite with list.
  rewrite <- ltL4_to_L4_1_list.
  autorewrite with list.
  rewrite <-  exps_as_list_len.
  rewrite <- bL4_to_L4_1_list.
  unfold find_branch, NLength.
  rewrite find_branch_as_find_correct.
  erewrite find_map_same_compose2 with (f:= find_branchb d);
    [ | intros; repnd; unfold compose; simpl; unfold num_bvars; simpl;
        refl ].
  remember (find (find_branchb d) (branches_as_list b)) as f.
  destruct f; [ | refl].
  simpl.
  repnd. simpl.
  simpl.
  do 1 autorewrite with list. simpl.
  cases_if;[ | refl]. simpl.
  do 1 autorewrite with list. simpl.
  rewrite Nat.eqb_sym.
  rewrite H.
  simpl.
  rewrite sbst_list_real.
  rewrite map_id.
  rewrite <- lsubstCommutesL4_to_L4_1.
  apply IHm.
- simpl. rewrite <- IHm.
  destruct (eval_ns m e1);[ | refl].
  simpl.
  pose proof (substCommutesL4_to_L4_1 e) as X.
  repnd.
  crush; fail.
Qed.


Require Import Common.TermAbs_parametricity.
Parametricity Recursive eval_n qualified.

(* should be automatically provalble for all types with decidable equality.
  However, it cannot be internally stated. *)
Global Instance EqIfRdcon : EqIfR CertiCoq_o_L4_o_polyEval_o_dcon_R.
Proof using.
Admitted.

Global Instance EqIfRstring : EqIfR Coq_o_Strings_o_String_o_string_R.
Proof using.
Admitted.

Let L4Opid_R := CertiCoq_o_L4_o_polyEval_o_L4Opid_R.
Global Instance EqIfRL4Opid : EqIfR L4Opid_R.
Proof using.
  constructor; intros Hyp; subst.
- inverts Hyp; auto; f_equal; try apply eqIfR; auto.
  unfold dcon in *.
Admitted.

Let TermAbs_R_NamedDBUnstrict :=
  (@TermAbs_R_NamedDBUnstrict Ast.name NVar _ L4Opid _ _ _ _  _ _ Ast.nAnon mkNVar getNId getIdMkNVar
     L4Opid_R EqIfRL4Opid).

(* deprecated. delete *)
Let TermAbs_R_NamedDB2 :=
  (@TermAbs_R_NamedDB Ast.name NVar _ L4Opid _ _ _ _  _ _ Ast.nAnon mkNVar getNId getIdMkNVar
     L4Opid_R EqIfRL4Opid).

(* deprecated. delete *)
Lemma L4_1_to_L4_2_free_thm:
  forall (t1 : L4_1_Term) n,
termsDB.fvars_below 0 t1 (* the undelying free thm also implies that eval_n preserves this *)->
(option_R _ _ alpha_eq)
   (option_map tL4_1_to_L4_2 (@eval_n (TermAbsDB Ast.name L4Opid) n t1))
   (@eval_n (Named.TermAbsImpl variables.NVar L4Opid) n (tL4_1_to_L4_2 t1)).
Proof using.
  intros ? ? Hfb.
  pose proof (CertiCoq_o_L4_o_polyEval_o_eval_n_R
    (TermAbsDB Ast.name L4Opid) (Named.TermAbsImpl variables.NVar L4Opid)
    TermAbs_R_NamedDB2 n n ltac:(apply eqIfR; refl) t1) as Hp.
  simpl in Hp.
  unfold Term_R in Hp.
  specialize (Hp _ (conj Hfb (alpha_eq_refl _))).
  simpl in Hp.
  destruct (@eval_n (TermAbsDB Ast.name L4Opid) n t1).
  - invertsna Hp Hp. setoid_rewrite <- Hp0.
    constructor. tauto.
  - invertsna Hp Hp. setoid_rewrite <- Hp.
    constructor.
Qed.

Lemma L4_1_to_L4_2_free_thm_unstrict:
  forall (t1 : L4_1_Term) n,
termsDB.fvars_below 0 t1 (* the undelying free thm also implies that eval_n preserves this *)->
(option_R _ _ alpha_eq)
   (option_map tL4_1_to_L4_2 (@eval_n (TermAbsDBUnstrict Ast.name L4Opid) n t1))
   (@eval_n (Named.TermAbsImplUnstrict variables.NVar L4Opid) n (tL4_1_to_L4_2 t1)).
Proof using.
  intros ? ? Hfb.
  pose proof (CertiCoq_o_L4_o_polyEval_o_eval_n_R
    (TermAbsDBUnstrict Ast.name L4Opid) (Named.TermAbsImplUnstrict variables.NVar L4Opid)
    TermAbs_R_NamedDBUnstrict n n ltac:(apply eqIfR; refl) t1) as Hp.
  simpl in Hp.
  unfold Term_R in Hp.
  specialize (Hp _ (conj Hfb (alpha_eq_refl _))).
  simpl in Hp.
  destruct (@eval_n (TermAbsDBUnstrict Ast.name L4Opid) n t1).
  - invertsna Hp Hp. setoid_rewrite <- Hp0.
    constructor. tauto.
  - invertsna Hp Hp. setoid_rewrite <- Hp.
    constructor.
Qed.

Definition t4_to_t4_2 v := (tL4_1_to_L4_2 (tL4_to_L4_1 v)).

(*
Lemma  maxFreeCommutesL4_to_L4_1 :
  (∀ (e : exp), maxFree (tL4_to_L4_1 e) = expression.maxFree e)
  /\
  (∀ (es : exps), ZLmax (map maxFree (ltL4_to_L4_1 es)) (-1) =
                    maxFreeC es)
  /\
  (∀ (es : efnlst), ZLmax (map maxFree (ftL4_to_L4_1 es)) (-1)
                      = maxFreeF es)
  /\
  (∀ (es : branches_e), ZLmax (map (maxFree_bt∘snd) (btL4_to_L4_1 es)) (-1)
                          = maxFreeB es).
Proof using.
  apply my_exp_ind;
    simpl; unfold compose in *; intros; try rewrite map_map in *; unfold compose;
      simpl in *; auto.
  rewrite H.
Admitted.  
 *)

Lemma expWfCommutesL4_to_L4_1 :
  (forall n (t : exp),
    exp_wf n t
    -> termsDB.fvars_below n (tL4_to_L4_1 t)) /\
  (forall n es, exps_wf n es ->
      lforall (termsDB.fvars_below n) (ltL4_to_L4_1 es)) /\
  (forall n es, efnlst_wf n es ->
      lforall (termsDB.fvars_below n) (ftL4_to_L4_1 es)) /\
  (forall n bs, branches_wf n bs ->
      lforall (fun b => (termsDB.fvars_below_bt n) (snd b)) (btL4_to_L4_1 bs)).
Proof using.
Local Opaque N.add.
  apply my_exp_wf_ind; crush; repeat constructor; crush; repeat constructor; crush; try firstorder.
- apply in_map_iff in H0. exrepnd. subst. constructor. auto.
- apply in_map_iff in H2. exrepnd. subst. auto.
- apply in_map_iff in H0. exrepnd. subst. constructor. unfold fnames, NLength.
  autorewrite with list.
  setoid_rewrite <- EfnListLength.
  auto.
- intros ? Hin. simpl in Hin. dorn Hin; subst; auto.
- intros ? Hin. simpl in Hin. dorn Hin; subst; auto.
- intros ? Hin. simpl in Hin. dorn Hin; subst; auto. simpl. constructor.
  rewrite mkNamesLength.
  assumption.
Qed.

(* MOVE to SquiggleEq.list *)
Lemma lforallCons {A} (P:A->Prop) a l: lforall P l -> P a -> lforall P (a::l).
Proof using.
  intros.
  intros ? Hin.
  dorn Hin; subst; auto.
Qed.
  
Lemma ntWfCommutesL4_to_L4_1 :
  (forall (t : exp),
     termsDB.nt_wf (tL4_to_L4_1 t)) /\
  (forall es, 
      lforall (termsDB.nt_wf) (ltL4_to_L4_1 es)) /\
  (forall es, 
      lforall (termsDB.nt_wf) (ftL4_to_L4_1 es)) /\
  (forall bs, 
      lforall (fun b => (termsDB.bt_wf) (snd b)) (btL4_to_L4_1 bs)).
Proof using.
  apply my_exp_ind; progress crush; repeat constructor;  crush; repeat constructor; crush;
    repeat rewrite map_map; unfold compose; simpl;
      try apply lforallCons; dands; repeat rewrite repeat_map_len; try firstorder.
- apply in_map_iff in H0. exrepnd. subst. constructor. auto.
- apply in_map_iff in H2. exrepnd. subst. auto.
- apply in_map_iff in H0. exrepnd. subst. constructor. unfold fnames, NLength.
  autorewrite with list.
  auto; fail.
- unfold fnames. autorewrite with list. 
  rewrite <- ftL4_to_L4_1_list. autorewrite with list. rewrite efnlst_as_list_len. refl.
- simpl. constructor. assumption.
Qed.

Definition is_lambdab (n:L4_1_Term) :=
decide (getOpid n = Some polyEval.NLambda).

Fixpoint fixwf (e:L4_1_Term) : bool :=
match e with
| vterm _ => true (* closedness is a the concern of this predicate *) 
| oterm o lb => 
    (match o with
    | polyEval.NFix _ _ => ball (map (is_lambdab ∘ get_nt) lb) && ball (map (fixwf ∘ get_nt) lb)
    | polyEval.NBox _ => true
    | _ => ball (map (fixwf ∘ get_nt) lb)
    end)
end.

Lemma fixwfCommutesL4_to_L4_1 :
  (forall n (t : exp),
    exp_wf n t
    -> fixwf (tL4_to_L4_1 t)= true ) /\
  (forall n es, exps_wf n es ->
      lforall (fun t => fixwf t = true) (ltL4_to_L4_1 es)) /\
  (forall n es, efnlst_wf n es ->
      lforall (fun t => fixwf t = true /\ is_lambdab t = true) (ftL4_to_L4_1 es)) /\
  (forall n bs, branches_wf n bs ->
      lforall (fun t => fixwf (get_nt (snd t)) = true) (btL4_to_L4_1 bs)).
Proof using.
Local Opaque N.add.
apply my_exp_wf_ind; crush; try apply andb_eq_true; dands;
  try apply ball_map_true; unfold compose; simpl;
    try firstorder.
- apply in_map_iff in H0. exrepnd. subst. eauto.
- apply in_map_iff in H1. exrepnd. subst. eauto.
- apply in_map_iff in H0. exrepnd. subst. simpl. eauto.
  apply H. assumption.
- apply in_map_iff in H0. exrepnd. subst. simpl. eauto.
  apply H. assumption.
- intros ? Hin. simpl in Hin. dorn Hin; subst; auto.
- intros ? Hin. simpl in Hin. dorn Hin; subst; dands; auto.
  + destruct e; auto.
  + apply H0. auto.
  + apply H0. auto.
- intros ? Hin. simpl in Hin. dorn Hin; subst; auto.
Qed.


(*
Lemma expWfCommutesL4_to_L4_1 :
  forall (t : exp) n,
    exp_wf n t
    -> termsDB.fvars_below n (tL4_to_L4_1 t).
Proof using.
  intros ? ? Hwf.
  apply expression.exp_wf_maxFree in Hwf.
  rewrite <-  (proj1 maxFreeCommutesL4_to_L4_1) in Hwf.
  apply exp_wf_maxFree. assumption.
Qed.
 *)

Lemma L4_to_L4_2_corr:
  forall (t v : exp) n,
    exp_wf 0 t 
    -> eval_ns n t = Some v
    -> exists vt,
        (@eval_n (Named.TermAbsImplUnstrict variables.NVar L4Opid) n (tL4_to_L4_2 t)) = Some vt
        /\ alpha_eq vt (tL4_to_L4_2 v).
Proof using.
  intros ? ? ? Hwf Hev.
  apply expWfCommutesL4_to_L4_1 in Hwf.
  apply L4_1_to_L4_2_free_thm_unstrict with (n:=n) in Hwf; auto.
  pose proof (evalCommLemma n t) as H4l.
  rewrite Hev in H4l.
  simpl in H4l. unfold eval41 in H4l.
  rewrite <- H4l in Hwf.
  inverts Hwf. rename H0 into v2.
  exists v2. symmetry in H2. dands; auto;[].
  symmetry. auto.
Qed. 

Module L42.
Definition is_lambdab (n:L4_2_Term) :=
decide (terms.getOpid n = Some polyEval.NLambda).

Fixpoint fixwf (e:L4_2_Term) : bool :=
match e with
| terms.vterm _ => true (* closedness is a the concern of this predicate *) 
| terms.oterm o lb => 
    (match o with
    | polyEval.NFix _ _ => ball (map (is_lambdab ∘ terms.get_nt) lb) && ball (map (fixwf ∘ terms.get_nt) lb)
    | polyEval.NBox _ => true
    | _ => ball (map (fixwf ∘ terms.get_nt) lb)
    end)
end.
End L42.

Lemma fixwfL41_to_L42:
  (forall (e:L4_1_Term) names n,
      fixwf e = L42.fixwf (fromDB Ast.nAnon mkNVar n names e)).
Proof using.
  induction e using termsDB.NTerm_better_ind2; auto;[]. intros.
  assert ( ball (map (λ x : DBTerm, fixwf (get_nt x)) lbt) =
 ball
   (map
      (λ x : DBTerm,
       L42.fixwf
         (terms.get_nt (fromDB_bt Ast.nAnon mkNVar n names x))) lbt)).
- f_equal. apply eq_maps. intros ?  Hin.
  destruct x. simpl. setoid_rewrite <- H; eauto.

- destruct o; simpl; repeat rewrite map_map; unfold compose; auto;[].
  f_equal; auto;[].
  f_equal. apply eq_maps. intros. destruct x.
  simpl. destruct d; auto.
Qed.

(*
Lemma vcL41_to_L42:
  forall (e:L4_1_Term) names n,
      varsOfClass (all_vars (fromDB Ast.nAnon mkNVar n names e)) true.
Proof using.
  intros. apply termsDB.fromDB_varprop.
  intros. compute. destruct p. refl.
Qed.

Lemma vcL4_to_L42:
  forall (e:exp),
      varsOfClass (all_vars (tL4_to_L4_2 e)) true.
Proof using.
  intros. apply vcL41_to_L42.
Qed.

(** well-formedness lemmas for L4 to L4_2 *)
Lemma ntwfL4_to_L42:
  forall (e:exp),
      terms.nt_wf (tL4_to_L4_2 e).
Proof using.
  intros. apply fromDB_nt_wf. apply ntWfCommutesL4_to_L4_1.
Qed.

Lemma closedL4_to_L42:
  forall (e:exp),
      exp_wf 0 e
      -> closed (tL4_to_L4_2 e).
Proof using.
  intros. eapply fromDB_closed;[ apply getIdMkNVar| ].
  apply expWfCommutesL4_to_L4_1. assumption.
Qed.

Lemma fixwfL4_to_L42:
  forall (e:exp) n,
      exp_wf n e
      -> L42.fixwf (tL4_to_L4_2 e) = true.
Proof using.
  intros. setoid_rewrite <- fixwfL41_to_L42.
  pose proof fixwfCommutesL4_to_L4_1.
  firstorder.
Qed.
*)