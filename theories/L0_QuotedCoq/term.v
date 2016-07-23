
Add LoadPath "../common" as Common.

Require Export Template.Ast.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Common.RandyPrelude.
Require Import Common.exceptionMonad.
Require Import Common.AstCommon.

Open Scope list_scope.
Open Scope bool_scope.
Set Implicit Arguments.


Ltac not_isApp :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.


(** Check applications are (hereditarily) well-formed,
*** and omit unused term forms (tVar, ...) **)
Definition isNotApp (t:term) : bool :=
  match t with
    | tApp _ _ => false
    | _ => true
  end.

Definition isApp (t:term) : Prop :=
  exists fn args, t = tApp fn args.
Lemma IsApp: forall fn args, isApp (tApp fn args).
intros. exists fn, args. reflexivity.
Qed.

Lemma not_isApp_isNotApp:
  forall t, ~ isApp t -> isNotApp t = true.
Proof.
  destruct t; intros h; cbn; try reflexivity.
  destruct h. exists t, l. reflexivity.
Qed.

Lemma isNotApp_not_isApp:
  forall t, isNotApp t = true -> ~ isApp t.
Proof.
  destruct t; intros h0; not_isApp.
Qed.

  
Section termSize_sec.
  Variable A : Set.
  Variable termSize: A -> nat.
  Fixpoint termsSize (ts:list A) : nat :=
    match ts with
      | nil => 1
      | cons r rs => S (termSize r + termsSize rs)
    end.
  Definition defSize (d:def A) : nat :=
    termSize (dtype _ d) + termSize (dbody _ d).
  Fixpoint defsSize (ds: list (def A)) : nat :=
   match ds with
     | nil => 1
     | cons d ds => 2 + (defSize d + defsSize ds)
   end.
End termSize_sec.

Fixpoint termSize (t:term) : nat :=
  match t with
    | tProd _ ty bod => S (termSize bod + termSize ty)
    | tLambda _ ty bod => S (termSize bod + termSize ty)
    | tLetIn _ dfn ty bod => S (termSize dfn + termSize ty + termSize bod)
    | tApp fn args => S (termSize fn + termsSize termSize args)
    | tCase _ ty mch brs =>
      S (termSize ty + termSize mch +
         termsSize (fun x => termSize (snd x)) brs)
    | tFix ds _ => S (defsSize termSize ds)
    | tCast t _ ty => S (termSize t + termSize ty)
    | _ => 1
  end.

Lemma termsSize_map_lem:
  forall (brs:list (nat * term)),
    termsSize termSize (map snd brs) =
    termsSize (fun x : nat * term => termSize (snd x)) brs.
Proof.
  induction brs; cbn. reflexivity.
  rewrite IHbrs. reflexivity.
Qed.


(****** how to do a wf fixpoint ??? ************

Definition wf_terms (wf_term:term -> bool) (bs:list term) : bool :=
  fold_left (fun (b:bool) (t:term) => andb (wf_term t) b) bs true.

Fixpoint wf_term (t:term) : bool.
Proof.
  revert t. apply (wf_rec termSize (fun x:term => bool)). intros t wfih.
  case_eq t; intros; subst.
  - exact true.  (* Rel *)
  - exact false.
  - exact false.
  - exact false.
  - exact true. (* Sort *)
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _ && wfih t2 _); cbn; omega.
  - case_eq l; intros; subst.
    + exact false.  (* App with no argument *)
    + refine (wfih t0 _ && wfih t _ && wf_terms wf_term l0); cbn; omega.
  - exact true.
  - exact true.
  - exact true.
  - refine (wfih t0 _ && wfih t1 _ && wf_terms wf_term (map snd l));
    cbn. omega. rewrite <- termsSize_map_lem. omega.
  - exact false.  (* Fix *)
  - exact false.  (* Unknown *)
Defined.    
**************************)

(**********************
(*** Compute wf_term by well-founded induction on size of terms  ***)
Definition tts_size (x:term * list term) : nat :=
  termSize (fst x) + termsSize termSize (snd x).

Function explode_defs (ds:list (def term)) : list term :=
  match ds with
    | nil => nil
    | cons {| dtype:= dty; dbody:= dtm |} es =>
      dty :: dtm :: (explode_defs es)
  end.

Lemma abcd_lt_lem:
  forall a b c d:nat,
    a < S b -> S (c + S (d + a)) < S (S ( S (c + d + b))).
Proof.
  intros a b c d h. omega.
Qed.

Lemma explode_defs_lt:
  forall (ds:list (def term)) (m:nat),
    termsSize termSize (explode_defs ds) < termSize (tFix ds m).
Proof.
  intros ds m. functional induction (explode_defs ds).
  - cbn. omega.
  - cbn in *. apply abcd_lt_lem. assumption.
Qed.
                                       
Definition bool_list_conjunct (bs:list bool) : bool := fold_left andb bs true.

Definition wf_term : term -> bool.
Proof.
  eapply (wf_rec termSize (fun (x:term) => bool))%type.
  intros t wfih.
  destruct t; intros; subst.
  - exact true.  (* Rel *)
  - exact false.
  - exact false.
  - exact false.
  - exact true. (* Sort *)
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _ && wfih t2 _); cbn; omega.
  - assert (T0:bool).
    { refine (wfih t0 _). cbn. omega. }
    assert (args:bool).
    { match l with
        | nil => exact false
        | _ => induction l
      end.
      + exact true.
      + assert (A:bool).
        { refine (wfih a _). cbn. omega. }
        apply IHl. intros x h. apply (wfih x). cbn in *. omega. } 
    refine (isNotApp t0 && T0 && args). 
  - exact true. (* Const *)
  - exact true. (* Ind *)
  - exact true. (* Construct *)
  - assert (Tp:bool).                                    (* Case *)
    { refine (wfih t0 _). cbn. omega. }
    assert (Mch:bool).
    { refine (wfih t1 _). cbn. omega. }
    assert (Brs:list bool).
    { induction l.
      - exact nil.
      - assert (A:bool).
         { refine (wfih (snd a) _). cbn. omega. }
         apply IHl. intros x h. apply (wfih x). cbn in *. omega. }
    refine (Tp && Mch &&
               match Brs with
                 | nil => false
                 | _ => bool_list_conjunct Brs
               end).
  - assert (Ds:list bool).                      (* Fix *)
    { induction m.        
      - exact nil.
      - assert (D:bool).
        { refine (wfih (dtype term a) _ && wfih (dbody term a) _);
          cbn; omega. }
        apply IHm. intros x h. apply (wfih x). cbn in *. omega. }
      refine (bool_list_conjunct Ds).
  - exact false.
Defined.
Print wf_term.

Require Import Template.Template.
Require Import Template.Ast.

Quote Definition t0 := ((fun x:bool => x) true).
Definition t1 : term :=
  tApp
    (tLambda nAnon
             (tInd (mkInd "Coq.Init.Datatypes.bool" 0)) (tRel 0))
    (cons (tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0) nil).
Eval cbv in (wf_term t1).
Definition t2 :=  (** App with no args **)   (**** FAILS!!!! *****)
  tApp
    (tLambda (nAnon)
             (tInd (mkInd "Coq.Init.Datatypes.bool" 0)) (tApp (tRel 0) nil))
    nil.
Eval cbv in (wf_term t2).
Definition t3 :=  (** nested App **)   (**** FAILS!!!! *****)
  tApp (tApp (tRel 0) nil) nil.
Eval cbv in (wf_term t3).



Definition wf_term : (term * list term) -> (bool * list bool).
Proof.
  eapply (wf_rec tts_size
                 (fun (x:term * list term) => (bool * list bool)))%type.
  intros t wfih.
  assert (wfih': forall (u:term) (us:list term),
                tts_size (u, us) < tts_size t -> bool * list bool).
  { intros u us. apply (wfih (u, us)). }
  clear wfih. destruct t.
  case_eq t; intros; subst; split.
  - exact true.  (* Rel *)
  - exact nil.

  - exact false.
  - exact nil.
  - exact false.
  - exact nil.
  - exact false.
  - exact nil.
  - exact true. (* Sort *)
  - exact nil.
  - assert (T0:bool).
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    assert (T1:bool).
    { refine (fst (wfih' t1 nil _)). cbn. omega. }
    exact (T0 && T1).
  - exact nil.
  - assert (T0:bool).
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    assert (T1:bool).
    { refine (fst (wfih' t1 nil _)). cbn. omega. }
    exact (T0 && T1).
  - exact nil.
  - assert (T0:bool).
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    assert (T1:bool).
    { refine (fst (wfih' t1 l _)). cbn. omega. }
    exact (T0 && T1).
  - exact nil.
  - assert (T0:bool).
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    assert (T1:bool).
    { refine (fst (wfih' t1 nil _)). cbn. omega. }
    assert (T2:bool).
    { refine (fst (wfih' t2 nil _)). cbn. omega. }
    exact (T0 && T1 && T2).
  - exact nil.
  - assert (T0:bool).        (* App *)
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    case_eq l0; intros; subst.
    + exact false.           (* App with nil arg list *)
    + assert (arg:bool).
    { refine (fst (wfih' t nil _)). cbn. omega. }
    assert (args: list bool).
    { refine (snd (wfih' t l1 _)). cbn. omega. }
    exact (isNotApp t0 && T0 && arg && bool_list_conjunct args).
  - exact nil.
  - exact true.
  - exact nil.
  - exact true.
  - exact nil.
  - exact true.
  - exact nil.
  - assert (T0:bool).   (** case **)
    { refine (fst (wfih' t0 nil _)). cbn. omega. }
    assert (T1:bool).
    { refine (fst (wfih' t1 nil _)). cbn. omega. }
    assert (brs: list bool).
    { refine (snd (wfih' t0 (map snd l0) _)). cbn.
      rewrite <- termsSize_map_lem.
      omega. }
    exact (T0 && T1 && bool_list_conjunct brs).
  - exact nil.
  - assert (j:= explode_defs_lt m n). cbn in j.    (* Fix *)
    assert (j0:= (wfih' (tFix m n) (explode_defs m))).
    assert (T:bool). 
    { refine (bool_list_conjunct (snd (wfih' (tFix m n) (explode_defs m) _))).
      cbn in *. apply explode_defs_lt.

    
  - exact true.    (* Fix **)
  - exact nil.
  - exact false.
  - exact nil.
Defined.


Definition wf_term : (term -> bool).
Proof.
  apply (wf_rec termSize (fun x:term => bool)). intros t wfih.
  case_eq t; intros; subst.
  - exact true.  (* Rel *)
  - exact false.
  - exact false.
  - exact false.
  - exact true. (* Sort *)
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _); cbn; omega.
  - refine (wfih t0 _ && wfih t1 _ && wfih t2 _); cbn; omega.
  - destruct l.
    + exact false.  (* App with no argument *)
    +
   
Defined.
 *************************)

(****************  a Prop-valued wf_term  ******)
Inductive wf_term : term -> Prop :=
| wftRel: forall n, wf_term (tRel n)
| wftSort: forall srt, wf_term (tSort srt)
| wftCast: forall tm ck ty,
             wf_term ty -> wf_term tm -> wf_term (tCast tm ck ty)
| wftProd: forall nm ty bod,
            wf_term ty -> wf_term bod -> wf_term (tProd nm ty bod)
| wftLambda: forall nm ty bod,
            wf_term ty -> wf_term bod -> wf_term (tLambda nm ty bod)
| wftLetIn: forall nm dfn ty bod,
              wf_term dfn -> wf_term ty -> wf_term bod ->
              wf_term (tLetIn nm dfn ty bod)
| wftApp: forall fn u us, 
            ~ isApp fn -> wf_term fn -> wf_term u -> wf_terms us ->
            wf_term (tApp fn (cons u us) )
| wftConst: forall nm, wf_term (tConst nm)
| wftInf: forall ind, wf_term (tInd ind)
| wftInd: forall ind m, wf_term (tConstruct ind m)
| wftCase: forall npars ty mch brs,
             wf_term ty -> wf_term mch -> wf_terms (map snd brs) ->
             wf_term (tCase npars ty mch brs)
| wftFix: forall defs m, wf_defs defs -> wf_term (tFix defs m)
with wf_terms: list term -> Prop :=
| wfts_nil: wf_terms nil
| wfts_cons: forall b bs, wf_term b -> wf_terms bs -> wf_terms (cons b bs)
with wf_defs: list (def term) -> Prop :=
| wfds_nil: wf_defs nil
| wfds_cons: forall c cs,
               wf_term (dtype _ c) -> wf_term (dbody _ c) -> wf_defs cs ->
               wf_defs (cons c cs).
Scheme wf_term_ind' := Induction for wf_term Sort Prop
with wf_terms_ind' := Induction for wf_terms Sort Prop
with wf_defs_ind' := Induction for wf_defs Sort Prop.
Combined Scheme wf_term_terms_defs_ind
         from wf_term_ind', wf_terms_ind', wf_defs_ind'.

(**** boolean valued well-formedness ****)
Function WF_term (n:nat) (t:term) : bool :=
  match n with
    | 0 => false
    | S n => match t with
               | tRel n => true
               | tSort srt => true
               | tCast tm ck ty => WF_term n ty && WF_term n tm
               | tProd nm ty bod => WF_term n ty && WF_term n bod
               | tLambda nm ty bod => WF_term n ty && WF_term n bod
               | tLetIn nm dfn ty bod =>
                 WF_term n dfn && WF_term n ty && WF_term n bod
               | tApp fn (cons u us) =>
                 isNotApp fn &&
                 WF_term n fn && WF_term n u && WF_terms n us
               | tConst pth => true
               | tInd ind => true
               | tConstruct ind m => true
               | tCase npars ty mch brs =>
                 WF_term n ty && WF_term n mch && WF_terms n (map snd brs)
               | tFix defs m => WF_defs n defs
               | _ => false
             end
  end
with WF_terms (n:nat) (ts:list term) : bool :=
       match n with
         | 0 => false
         | S n => match ts with
                    | nil => true
                    | cons b bs => WF_term n b && WF_terms n bs
                  end
       end
with WF_defs (n:nat) (ds:list (def term)) : bool :=
       match n with
         | 0 => false
         | S n => match ds with
                    | nil => true
                    | cons c cs =>
                      WF_term n (dtype _ c) && WF_term n (dbody _ c) &&
                              WF_defs n cs
                  end
       end.
Functional Scheme WF_term_ind' := Induction for WF_term Sort Prop
with WF_terms_ind' := Induction for WF_terms Sort Prop
with WF_defs_ind' := Induction for WF_defs Sort Prop.
Combined Scheme WF_term_terms_defs_ind
         from WF_term_ind', WF_terms_ind', WF_defs_ind'.

Lemma pre_WF_term_up:
  forall m,
  (forall t, WF_term m t = true -> WF_term (S m) t = true) /\
  (forall ts, WF_terms m ts = true -> WF_terms (S m) ts = true) /\
  (forall ds, WF_defs m ds = true -> WF_defs (S m) ds = true).
Proof.
  apply (WF_term_terms_defs_ind
           (fun (m:nat) (t:term) (q:bool) =>
              WF_term m t = true -> WF_term (S m) t = true)
           (fun (m:nat) (ts:list term) (q:bool) =>
              WF_terms m ts = true -> WF_terms (S m) ts = true)
           (fun (m:nat) (ds:list (def term)) (q:bool) =>
              WF_defs m ds = true -> WF_defs (S m) ds = true));
  intros; intuition; try contradiction.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2].
    change (WF_term (S n0) ty && WF_term (S n0) tm = true). intuition.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2]. 
    change (WF_term (S n0) ty && WF_term (S n0) bod = true). intuition.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2]. 
    change (WF_term (S n0) ty && WF_term (S n0) bod = true). intuition.
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [z1 k3].
    destruct (proj1 (andb_true_iff _ _) z1) as [k1 k2].
    change
      (WF_term (S n0) dfn && WF_term (S n0) ty && WF_term (S n0) bod = true).
    intuition.
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [z1 k4].
    destruct (proj1 (andb_true_iff _ _) z1) as [z2 k3].
    destruct (proj1 (andb_true_iff _ _) z2) as [k1 k2].
    change (isNotApp fn && WF_term (S n0) fn && WF_term (S n0) u &&
                     WF_terms (S n0) us = true).
    rewrite k1. intuition.
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [z1 k3].
    destruct (proj1 (andb_true_iff _ _) z1) as [k1 k2].
    change (WF_term (S n0) ty && WF_term (S n0) mch &&
            WF_terms (S n0) (map snd brs) = true).
    intuition.
  - subst. destruct _x; try contradiction; cbn in H; try discriminate.
    destruct l. discriminate. contradiction.
  - subst. cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [k2 k1].
    cbn. intuition.
  - subst. cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [z1 k3].
    destruct (proj1 (andb_true_iff _ _) z1) as [k1 k2].
    cbn. intuition.
Qed.

Lemma WF_term_up:
  forall m t,
    WF_term m t = true -> forall n, m <= n -> WF_term n t = true.
Proof.
  intros m t hm n hn. induction hn.
  - assumption.
  - apply (proj1 (pre_WF_term_up m0)). assumption.
Qed.

Lemma WF_terms_up:
  forall m ts,
    WF_terms m ts = true -> forall n, m <= n -> WF_terms n ts = true.
Proof.
  intros m ts hm n hn. induction hn.
  - assumption.
  - apply (proj1 (proj2 (pre_WF_term_up m0))). assumption.
Qed.

Lemma WF_defs_up:
  forall m ds,
    WF_defs m ds = true -> forall n, m <= n -> WF_defs n ds = true.
Proof.
  intros m ds hm n hn. induction hn.
  - assumption.
  - apply (proj2 (proj2 (pre_WF_term_up m0))). assumption.
Qed.


Lemma wf_WF_term:
  (forall t, wf_term t -> exists n, WF_term n t = true) /\
  (forall ts, wf_terms ts -> exists n, WF_terms n ts = true) /\
  (forall ds, wf_defs ds -> exists n, WF_defs n ds = true).
Proof.
  apply wf_term_terms_defs_ind; intros; try (exists 1; reflexivity);
  destruct H as [x0 j0];
  try (destruct H0 as [x1 j1]); try (destruct H1 as [x2 j2]);
  try (exists (S (x0 + x1)); cbn; eapply true_true_andb;
              eapply WF_term_up; try eassumption; try omega);
  try (exists (S (x0 + x1 + x2)); cbn;
    eapply true_true_andb; try eapply true_true_andb;
    try eapply WF_term_up; try eapply WF_terms_up;
    try eassumption; try omega).
  - rewrite not_isApp_isNotApp; try assumption.
    eapply true_true_andb; try reflexivity.
    eapply WF_term_up; try eapply WF_terms_up. eassumption. omega.
  - exists (S x0). cbn. assumption.
  - exists (S (x0 + x1)). cbn. eapply true_true_andb;
      first [eapply WF_term_up | eapply WF_terms_up];
      try eassumption; try omega.
  - eapply WF_defs_up. eassumption. omega.
Qed.

Lemma WF_wf_term:
  forall m,
    (forall t, WF_term m t = true -> wf_term t) /\
    (forall ts, WF_terms m ts = true -> wf_terms ts) /\
    (forall ds, WF_defs m ds = true -> wf_defs ds).
Proof.
  intros m.
  apply (WF_term_terms_defs_ind
           (fun (m:nat) (t:term) (q:bool) =>
              WF_term m t = true -> wf_term t)
           (fun (m:nat) (ts:list term) (q:bool) =>
              WF_terms m ts = true -> wf_terms ts)
           (fun (m:nat) (ds:list (def term)) (q:bool) =>
              WF_defs m ds = true -> wf_defs ds));
    intros; cbn in *; try discriminate; subst; try (solve[constructor]);
    try (solve[constructor; intuition]);
    try (solve[destruct (andb_true_true _ _ H1); constructor; intuition]);
    try (solve
           [destruct (andb_true_true _ _ H2) as [j0 j1];
             destruct (andb_true_true _ _ j0) as [j2 j3];
             constructor; intuition]).
  - destruct (andb_true_true _ _ H2) as [j0 j1].
    destruct (andb_true_true _ _ j0) as [j2 j3].
    destruct (andb_true_true _ _ j2) as [j4 j5].
    constructor; try (solve[intuition]).
    apply isNotApp_not_isApp. assumption.
  - destruct _x; try discriminate; try (solve [constructor]);
    try (solve[constructor; intuition]);
    try (solve[destruct (andb_true_true _ _ H) as [j0 j1];
                constructor; intuition]).
    + destruct l. discriminate. constructor; intuition.
Qed.

      
(********************************
Lemma termSize_enough:
  forall n,
    (forall t,
       WF_term n t = true -> WF_term (termSize t) t = true) /\
    (forall ts,
       WF_terms n ts = true -> WF_terms (termsSize termSize ts) ts = true) /\
    (forall ds,
       WF_defs n ds = true -> WF_defs (defsSize termSize ds) ds = true).   
Proof.
  apply (WF_term_terms_defs_ind
           (fun (m:nat) (t:term) (q:bool) =>
              WF_term m t = true -> WF_term (termSize t) t = true)
           (fun (m:nat) (ts:list term) (q:bool) =>
              WF_terms m ts = true ->
              WF_terms (termsSize termSize ts) ts = true)
           (fun (m:nat) (ds:list (def term)) (q:bool) =>
              WF_defs m ds = true ->
              WF_defs (defsSize termSize ds) ds = true));
  intros; intuition; try contradiction.
  - cbn in *. destruct (andb_true_true _ _ H1).
    apply (true_true_andb). 
    + eapply WF_term_up. eapply H. eassumption. omega.
    + eapply WF_term_up. eapply H0. eassumption. omega.
  - cbn in *. destruct (andb_true_true _ _ H1).
    apply (true_true_andb). 
    + eapply WF_term_up. eapply H. eassumption. omega.
    + eapply WF_term_up. eapply H0. eassumption. omega.
  - cbn in *. destruct (andb_true_true _ _ H1).
    apply (true_true_andb). 
    + eapply WF_term_up. eapply H. eassumption. omega.
    + eapply WF_term_up. eapply H0. eassumption. omega.
  - destruct (andb_true_true _ _ H2). destruct (andb_true_true _ _ H3).
    repeat (apply (true_true_andb)); eapply WF_term_up.
    eapply H. assumption. omega.
    eapply H0. assumption. omega.
    eapply H1. assumption. omega.
  - subst. cbn in *.
    destruct (andb_true_true _ _ H2).
    destruct (andb_true_true _ _ H3).
    destruct (andb_true_true _ _ H5).
    repeat (apply (true_true_andb));
      try (eapply WF_term_up); try (eapply WF_terms_up).
    assumption.
    eapply H. assumption. omega.
    eapply H0. assumption. omega.
    eapply H1. assumption. omega.
  - subst. cbn in *.
    destruct (andb_true_true _ _ H2).
    destruct (andb_true_true _ _ H3).
    repeat (apply (true_true_andb));
      try (eapply WF_term_up); try (eapply WF_terms_up).
    eapply H. assumption. omega.
    eapply H0. assumption. omega.
    eapply H1. assumption. rewrite termsSize_map_lem. omega.
  - subst. cbn in *.
    destruct _x; try discriminate; try (solve [constructor]).
    try (solve[constructor; intuition]);
    try (solve[destruct (andb_true_true _ _ H) as [j0 j1];
                constructor; intuition]).
    destruct _x; try discriminate; cbn; try reflexivity.




    - destruct H1. split.
    * refine (WF_term_up _ _ _). eapply H. assumption. omega.
    * refine (WF_term_up _ _ _). eapply H0. assumption. omega.
  - destruct H1. split.
    * refine (WF_term_up _ _ _). eapply H. assumption. omega.
    * refine (WF_term_up _ _ _). eapply H0. assumption. omega.
  - destruct H2 as [j1 [j2 j3]]. repeat split.
    * refine (WF_term_up _ _ _). eapply H. assumption. omega.
    * refine (WF_term_up _ _ _). eapply H0. assumption. omega.
    * refine (WF_term_up _ _ _). eapply H1. assumption. omega.
  - destruct H2 as [j1 [j2 [j3 j4]]]. repeat split. assumption.
    * refine (WF_term_up _ _ _). eapply H. assumption. omega.
    * cbn. refine (WF_term_up _ _ _). eapply H0. assumption. omega.
    * cbn. refine (WF_terms_up _ _ _). eapply H1. assumption. omega.
  - destruct H2 as [j1 [j2 j3]]. repeat split.
    * refine (WF_term_up _ _ _). eapply H. assumption. omega.
    * refine (WF_term_up _ _ _). eapply H0. assumption. omega.
    * refine (WF_terms_up _ _ _). eapply H1. assumption. induction brs.
      + cbn. omega.
      + cbn. rewrite termsSize_map_lem. omega.
  - subst. destruct _x; try contradiction.
    destruct l; try contradiction.
  - subst. destruct H1. cbn. intuition.
    + refine (WF_term_up _ _ _). eassumption. omega.
    + refine (WF_terms_up _ _ _). eassumption. omega.
  - subst. destruct H2 as [j1 [j2 j3]]. cbn. repeat split.
    + refine (WF_term_up _ _ _). apply H. eassumption. omega.
    + refine (WF_term_up _ _ _). apply H0. eassumption. omega.
    + refine (WF_defs_up _ _ _). apply H1. eassumption. omega.
Qed.
 *******************************)
