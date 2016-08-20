
Require Import bin_rels.
Require Import eq_rel.
Require Import universe.
Require Import LibTactics.
Require Import tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Notations.
Require Import UsefulTypes.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.Morphisms.
Require Import list.

Require Import Recdef.
Require Import Eqdep_dec.
Require Import varInterface.
Require Import terms.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)


(** Here are some handy definitions that will
    reduce the verbosity of some of our later definitions
*)

Generalizable Variable Opid.

Section terms2Generic.

Context {NVar VarClass} {deqnvar : Deq NVar} {varclass: @VarType NVar VarClass deqnvar} 
`{hdeq: Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).

Definition nobnd (f:NTerm) : BTerm := bterm [] f.


(** %\noindent \\*% We define similar abstractions for other [Opid]s.
    This document does not show them. As mentioned before, one can click
    at the hyperlinked filename that is closest above to open a
    webpage that shows complete contents of this file.
*)


Lemma fold_nobnd :
  forall t, bterm [] t = nobnd t.
Proof using.
  unfold nobnd; auto.
Qed.


(*
Definition mk_esquash (R : NTerm) :=
  oterm (Can NEsquash) [nobnd R].
*)



(* Picks a variable that is not in the set of free variables of a given term *)
Definition newvar (t : NTerm) := fresh_var (free_vars t).

(* Delete. use flat_map instead *)
Fixpoint free_vars_list (terms : list NTerm) :=
  match terms with
    | [] => []
    | t :: ts => free_vars t ++ free_vars_list ts
  end.




(* ------ SIMPLE OPERATORS ON TERMS ------ *)

(*
Fixpoint depth (t : NTerm) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => lsum map depth_bterm bterms
  end
 with depth_bterm (lv : list NVar) (nt : NTerm) :=
  match bt with
  | bterm lv nt => depth nt
  end.
*)

End terms2Generic.


Fixpoint size {NVar:Type} {Opid:Type} (t : @NTerm NVar Opid) : nat :=
  match t with
  | vterm _ => 1
  | oterm op bterms => S (addl (map (@size_bterm NVar _) bterms))
  end
 with size_bterm {NVar:Type} {Opid:Type} (bt: @BTerm NVar Opid) :nat :=
  match bt with
  | bterm lv nt => @size NVar Opid nt
  end.

Fixpoint wft {NVar:Type} {Opid:Type} {gts : GenericTermSig Opid} (t : @NTerm NVar Opid) : bool :=
  match t with
    | vterm _ => true
    | oterm o bts =>
      andb (beq_list deq_nat (map (@num_bvars NVar _) bts) (OpBindings o))
           (ball (map wftb bts))
  end
with wftb {NVar:Type} {Opid:Type} {gts : GenericTermSig Opid} (bt : @BTerm NVar Opid) : bool :=
  match bt with
    | bterm vars t => wft t
  end.

Section terms3Generic.

Context {NVar VarClass} {deqnvar : Deq NVar} {varclass: @VarType NVar VarClass deqnvar} 
  `{hdeq: Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).

(* ------ INDUCTION ON TERMS ------ *)


Lemma size_subterm2 :
  forall (o:Opid) (lb : list BTerm) (b : BTerm) ,
    LIn b lb
    ->  size_bterm b <  size (oterm o lb).
Proof using.
  simpl. induction lb; intros ? Hin; inverts Hin as; simpl; try omega.
  intros Hin. apply IHlb in Hin; omega.
Qed.

Lemma size_subterm3 :
  forall (o:Opid) (lb : list BTerm) (nt : NTerm) (lv : list NVar) ,
    LIn (bterm lv nt) lb
    ->  size nt <  size (oterm o lb).
Proof using.
 introv X.
 apply size_subterm2 with (o:=o) in X. auto.
Qed.

Lemma NTerm_better_ind3 :
  forall P : NTerm -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt: NTerm),
              size nt < size (oterm o lbt)
              -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof using.
 intros P Hvar Hbt.
 assert (forall n t, size t = n -> P t) as Hass.
 Focus 2. intros. apply Hass with (n := size t) ; eauto; fail.
 
 induction n as [n Hind] using comp_ind_type.
 intros t Hsz.
 destruct t.
 apply Hvar.
 apply Hbt. introv Hs.
 apply Hind with (m := size nt) ; auto.
 subst.
 assert(size nt < size (oterm o l)); auto.
Qed.


Lemma NTerm_better_ind2 :
  forall P : NTerm -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt nt': NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt)
              -> size nt' <= size nt
              -> P nt'
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof using.
 intros P Hvar Hbt.
 apply  NTerm_better_ind3; eauto.
 intros ? ? H.
 apply Hbt.
 intros ? ? ? Hin Hs. apply H.
 eapply le_lt_trans;[apply Hs|].
 eapply size_subterm3; eauto.
Qed.

Lemma NTerm_BTerm_ind :
  forall (PN : NTerm -> Type) (PB : BTerm -> Type),
    (forall n : NVar, PN (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall b,
             (LIn b lbt) -> PB b
          )
          -> PN (oterm o lbt)
       )
    -> (forall (lv: list NVar) (nt : NTerm),
          PN nt -> PB (bterm lv nt)
       )
    -> ((forall t : NTerm, PN t) *  (forall t : BTerm, PB t)).
Proof using.
   introv Hv Hind Hb.
   assert (forall A B, A -> (A -> B) -> (A*B)) as H by tauto.
   apply H; clear H.
- apply  NTerm_better_ind2; auto. 
   introv Hx. apply Hind. introv Hin. destruct b. eauto.
- intro Hnt. intro b. destruct b. eauto.  
Qed.

Lemma NTerm_better_ind :
  forall P : NTerm -> Type,
    (forall n : NVar, P (vterm n))
    -> (forall (o : Opid) (lbt : list BTerm),
          (forall (nt : NTerm) (lv: list NVar),
             (LIn (bterm lv nt) lbt) -> P nt
          )
          -> P (oterm o lbt)
       )
    -> forall t : NTerm, P t.
Proof using.
 introv Hv Hind. apply  NTerm_better_ind2; auto. 
 introv Hx. apply Hind. introv Hin. eapply Hx in Hin; eauto. 
Qed.


Tactic Notation "nterm_ind" ident(h) ident(c) :=
  induction h using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].


Lemma num_bvars_on_bterm :
  forall (l:list NVar) (n : NTerm),
    num_bvars (@bterm NVar Opid l n) = length l.
Proof using.
  unfold num_bvars; simpl; sp.
Qed.



Definition wf_term (t : NTerm) := wft t = true.

Definition wf_bterm (bt : BTerm) := wftb bt = true.

Lemma wf_term_proof_irrelevance :
  forall t,
  forall x y : wf_term t,
    x = y.
Proof using.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Definition wf_term_extract :=
  fun (t : NTerm) (x : wf_term t) =>
    match x return (x = match x with
                          | eq_refl => eq_refl (wft t)
                        end)
    with
      | eq_refl => eq_refl eq_refl
    end.

(*
Definition wf_term_extract1 :=
  fun (t : NTerm) (x : wf_term t) =>
    match x in _ = b return match b with
                     | true => x = eq_refl (wft t)
                   end
    with
      | eq_refl => eq_refl eq_refl
    end.

Lemma wf_term_extract2 :
  forall t : NTerm,
  forall x : wf_term t,
    x = eq_refl (wft t).
*)

(*Lemma yyy : forall A (x : A) (pf : x = x), pf = eq_refl x.
Lemma xxx : forall t (x : wft t = true), x = eq_refl (wft t).*)

Lemma nt_wf_eq :
  forall t,
    nt_wf t <=> wf_term t.
Proof using.
  unfold wf_term.
  nterm_ind t as [|o lbt ind] Case; simpl; intros.

  - Case "vterm".
    split; sp.

  - Case "oterm".
    split_iff SCase.

    + SCase "->"; intro w.
      inversion w; subst.
      allrw.
      rewrite beq_list_refl; simpl.
      trw ball_true; sp.
      alltrewrite in_map_iff; sp; subst.
      apply_in_hyp wf; destruct wf; allsimpl.
      discover; sp. firstorder.

    + SCase "<-"; sp.
      remember (beq_list deq_nat (map num_bvars lbt) (OpBindings o)).
      destruct b; allsimpl; sp.
      alltrewrite ball_true.
      constructor; sp.
      destruct l.
      apply_in_hyp e.
      constructor.
      apply e.
      apply_hyp.
      alltrewrite in_map_iff.
      exists (bterm l n); simpl; sp.

      remember (OpBindings o).
      clear Heql.
      revert l Heqb.
Local Opaque deq_nat.
      induction lbt; allsimpl.
      destruct l; allsimpl; sp.
      destruct l; allsimpl; sp.
      rewrite decide_decideP in Heqb.
      destruct (decideP (num_bvars a = n)); subst; sp.
      apply cons_eq.
      apply IHlbt; sp.
      apply ind with (lv := lv); sp.
Qed.

Lemma nt_wf_implies :
  forall t, nt_wf t -> wf_term t.
Proof using.
  sp; apply nt_wf_eq; sp.
Qed.

Lemma wf_term_eq :
  forall t, wf_term t <=> nt_wf t.
Proof using.
  intro; generalize (nt_wf_eq t); sp.
  symm; auto.
Qed.

Lemma bt_wf_eq :
  forall bt, bt_wf bt <=> wf_bterm bt.
Proof using.
  sp; split; intro w.
  inversion w; subst; unfold wf_bterm; simpl.
  fold (wf_term nt).
  apply wf_term_eq; auto.
  destruct bt; allunfold wf_bterm; allsimpl.
  fold (wf_term n) in w.
  constructor.
  apply nt_wf_eq; auto.
Qed.

(*
Inductive nt_wfb (t:NTerm) : bool :=
 match t with
 | vterm _ => true
 | bterm _ rt => nt_wfb rt
 | oterm o lnt : (eq map (num_bvars) lnt  OpBindings o).
*)

Definition closedb (t : NTerm) := nullb (free_vars(t)).
Definition closed_bt (bt : BTerm) := free_vars_bterm bt = [].


Definition isprogram_bt (bt : BTerm) := closed_bt bt # bt_wf bt.

(** Our definition [isprog] below is is logically equivalent to [isprogram],
    but unlike [isprogram], it is easy to prove that
    for any [t], all members(proofs) of [isprog t] are equal.
    An interested reader can look at the lemma
    %\coqexternalref{UIP\_dec}
    {http://coq.inria.fr/distrib/8.4pl2/stdlib/Coq.Logic.Eqdep\_dec}
    {\coqdocdefinition{UIP\_dec}}% from that standard library.
    As mentioned before, clicking on the lemma name in 
    the previous sentence should open
    the corresponding webpage of the Coq standard library.
    Instead, one can also look at the lemma [isprog_eq] below and
    safely ignore these technicalites.

*)
Definition isprog (t : NTerm) := (nullb (free_vars t) && wft t) = true.

Definition isprog_bt (bt : BTerm) :=
  (nullb (free_vars_bterm bt) && wftb bt) = true.

Definition isprog_vars (vs : list NVar) (t : NTerm) :=
  (sub_vars (free_vars t) vs && wft t) = true.

Lemma closed_nt :
  forall op bts,
    closed (oterm op bts)
    <=>
    forall bt, LIn bt bts -> closed_bt bt.
Proof using.
  sp; unfold closed, closed_bt; simpl; trw flat_map_empty; split; sp.
Qed.

Lemma closed_nt0 : forall o (nt:NTerm), closed (oterm o [bterm [] nt]) -> closed nt.
Proof using.
  intros. unfold closed in H. simpl in H. apply app_eq_nil in H. repnd.
  clears_last. unfold closed. assumption.
Qed.

Lemma closed_null_free_vars :
  forall (t:NTerm),
    closed t <=> null (free_vars t).
Proof using.
  unfold closed; sp.
  trw null_iff_nil; sp.
Qed.

Lemma isprog_proof_irrelevance :
  forall t,
  forall x y : isprog t,
    x = y.
Proof using.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma isprog_vars_proof_irrelevance :
  forall t vs,
  forall x y : isprog_vars vs t,
    x = y.
Proof using.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.


Require Import tactics.
Lemma isprogram_eq :
  forall t,
    isprogram t <=> isprog t.
Proof using.
  unfold isprog, isprogram.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    split; sp. unfold closed in *; allsimpl; sp.

  - Case "oterm".
    split_iff SCase.

    + SCase "->".
      intros i; destruct i as [ cl wf ].
      inversion cl; subst.
      inversion wf; subst.
      repeat (rw andb_eq_true).
      rewrite fold_assert.
      allrw <- null_iff_nil.
      rw ball_map_true.
      rw assert_nullb; sp.

      rewrite fold_assert.
      rw assert_beq_list; auto.

      destruct x; allsimpl.
      fold (wf_term n).
      apply wf_term_eq.
      apply_in_hyp p; inversion p; subst; sp.

    + SCase "<-"; intros.
      repeat (allrewrite andb_true); repd.
      allrw fold_assert.
      allrw assert_nullb.
      allrw null_iff_nil.
      allrw assert_beq_list.
      allrw ball_map_true; sp.
      constructor; sp.
      apply_in_hyp p.
      destruct l; allsimpl.
      constructor.
      allfold (wf_term n).
      apply wf_term_eq; auto.
Qed.

Lemma isprogram_implies :
  forall t, isprogram t -> isprog t.
Proof using.
  sp; apply isprogram_eq; sp.
Qed.

Lemma isprog_implies :
  forall t : NTerm, isprog t -> isprogram t.
Proof using.
  sp; apply isprogram_eq; sp.
Qed.

Lemma isprog_eq :
  forall t, isprog t <=> isprogram t.
Proof using.
  intro; symm; apply isprogram_eq; auto.
Qed.

Lemma isprogram_bt_eq :
  forall bt,
    isprogram_bt bt <=> isprog_bt bt.
Proof using.
  intro; unfold isprogram_bt, isprog_bt, closed_bt; split; sp.
  allrw; simpl.
  fold (wf_bterm bt).
  apply bt_wf_eq; auto.
  alltrewrite andb_eq_true; sp.
  allrewrite fold_assert.
  alltrewrite assert_nullb.
  alltrewrite null_iff_nil; sp.
  destruct bt; constructor.
  alltrewrite andb_eq_true; sp; allsimpl.
  allfold (wf_term n).
  apply nt_wf_eq; auto.
Qed.

Lemma isprog_vars_eq :
  forall t vs,
    isprog_vars vs t <=> subsetv (free_vars t) vs # nt_wf t.
Proof using.
  unfold isprog_vars; sp.
  rw andb_eq_true.
  rewrite fold_assert.
  rewrite assert_sub_vars.
  rw nt_wf_eq; sp.
Qed.

Lemma isprog_vars_if_isprog :
  forall vs t, isprog t -> isprog_vars vs t.
Proof using.
  introv ip.
  rw isprog_vars_eq.
  rw isprog_eq in ip.
  destruct ip; sp.
  unfold closed in *; allrw; sp.
Qed.

Lemma isprog_vars_app_l :
  forall t vs1 vs2,
    isprog_vars vs2 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof using.
  sp; alltrewrite isprog_vars_eq; sp.
  unfold subset in *.
  apply subset_app_l; sp.
Qed.

Definition areprograms ts := forall t, LIn t ts -> isprogram t.

Lemma areprograms_nil : areprograms [].
Proof using.
  unfold areprograms; simpl; sp.
Qed.

Lemma areprograms_snoc :
  forall t ts,
    areprograms (snoc ts t) <=> areprograms ts # isprogram t.
Proof using.
  unfold areprograms; sp; split; sp; try (apply_hyp; rw in_snoc; sp).
  alltrewrite in_snoc; sp; subst; sp.
Qed.

Lemma areprograms_cons :
  forall t ts, areprograms (t :: ts) <=> isprogram t # areprograms ts.
Proof using.
  unfold areprograms; sp; simpl; split; sp; subst; sp.
Qed.

Lemma areprograms_app :
  forall ts1 ts2,
    areprograms (ts1 ++ ts2) <=> areprograms ts1 # areprograms ts2.
Proof using.
  unfold areprograms; sp; split; sp.
  apply_hyp; rw in_app_iff; sp.
  apply_hyp; rw in_app_iff; sp.
  alltrewrite in_app_iff; sp.
Qed.

Lemma isprogram_vterm :
  forall v, isprogram (vterm v) <=> False.
Proof using.
  unfold isprogram, closed; simpl; sp; split; sp.
Qed.

(*
Ltac repnd :=
  repeat match goal with
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
           | [ H : _ # _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
         end.
*)

Theorem isprogram_ot_iff :
  forall o bts,
    isprogram (oterm o bts)
    <=>
    (map num_bvars bts = OpBindings o
     # forall bt, LIn bt bts -> isprogram_bt bt).
Proof using.
  intros. sp_iff Case.

  - Case "->".
    intros Hisp.
    unfold isprogram in Hisp. repnd.
    inverts Hisp0 as Hflat. inverts Hisp.
    split;auto. intros bt Hin.
    unfold isprogram_bt.
    rw flat_map_empty in Hflat.
    apply_in_hyp p; sp.

  - Case "<-".
    intros eq; destruct eq as [Hmap Hstclose].
    unfold isprogram, closed.

    split; try (constructor); auto;
    try (simpl; apply flat_map_empty);
    intros a ain;
    apply Hstclose in ain; inversion ain; sp.
Qed.

Theorem nt_wf_ot_implies :
  forall lv o (nt1 : NTerm) bts,
    nt_wf (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof using. intros ? ? ? ? Hwf Hin. inverts Hwf as Hwf Hmap.
  assert (bt_wf (bterm lv nt1)) as Hbf by (apply Hwf; auto).
  inverts Hbf. auto.
Qed.


Lemma newvar_prop :
  forall (t: NTerm), ! LIn (newvar t) (free_vars t).
Proof using.
  unfold newvar; sp.
  allapply fresh_var_not_in; sp.
Qed.


(*
Lemma newvar_not_in_free_vars :
  forall (t: NTerm),
    ! LIn nvarx (free_vars t)
    -> newvar t = nvarx.
Proof using.
  sp.
  unfold newvar.
  apply fresh_var_nvarx; sp.
Qed.

Lemma newvar_prog :
  forall t,
    isprog t
    -> newvar t = nvarx.
Proof using.
  sp.
  unfold newvar.
  apply isprog_eq in H.
  inversion H.
  unfold closed in H0.
  rewrite H0; sp.
Qed.
*)


(*
(** A value is a program with a canonical operator *)
Inductive isvalue : NTerm -> [univ] :=
  | isvl : forall (c : CanonicalOp) (bts : list BTerm ),
           isprogram (oterm (Can c) bts)
           -> isvalue (oterm (Can c) bts).


Inductive isovalue : NTerm -> Prop :=
  | isovl : forall (c : CanonicalOp) (bts : list BTerm),
              nt_wf (oterm (Can c) bts)
              -> isovalue (oterm (Can c) bts).

Lemma isvalue_closed :
  forall t, isvalue t -> closed t.
Proof using.
  introv isv; inversion isv.
  allunfold isprogram; sp.
  unfold isprogram in *.
  tauto.
Qed.

Lemma isvalue_program :
  forall t, isvalue t -> isprogram t.
Proof using.
  introv isv; inversion isv; sp.
Qed.
*)

(* ------ programs ------ *)

Definition WTerm  := { t : NTerm  | wf_term t }.
Definition WBTerm := { bt : BTerm | wf_bterm bt }.


(*
  (* first of all, isprog is NOT a boolean. also, the reader will
    be left wondering what UIP_dec is*)

  where [isprog] is the Boolean version of [isprogram]
  (using a Boolean version of [isprogram] makes it easy to prove that
  closed terms are equal by proving that the underlying [NTerm]s are
  equals using [UIP_dec]).  

*)

(**

  The [CTerm] type below is useful in compactly stating definitions
  that are only meaningful for closed terms. A [CTerm] is a pair
  of an [NTerm] [t] and a proof that [t] is closed.
  This [CTerm] type will be handy in compactly 
  defining the Nuprl type system where types are defined as partial
  equivalence relations on closed terms.
  
*)

Definition CTerm  := { t : NTerm  | isprog t }.
Definition get_cterm (t : CTerm) := let (a,_) := t in a.


Definition BCTerm := { bt : BTerm | isprog_bt bt }.


(**

  We also define a type of terms that specifies what are the possible
  free variables of its inhabitants.  A term is a [(CVTerm vs)] term
  if the set of its free variables is a subset of [vs].  This type is
  also useful to define the Nuprl type system.  For example, to define
  a closed family of types such as a closed function type of the form
  $\NUPRLfunction{x}{A}{\NUPRLsuba{B}{z}{x}}$, $A$ has to be closed
  and the free variables of $B$ can only be $z$.

*)

Definition CVTerm (vs : list NVar) := { t : NTerm | isprog_vars vs t }.


Definition CVTerm3 := forall a b c, CVTerm [a;b;c].


Definition mk_cvterm (vs : list NVar) (t : NTerm) (p : isprog_vars vs t) :=
  exist (isprog_vars vs) t p.



Definition get_wterm (t : WTerm) := let (a,_) := t in a.
Definition get_cvterm (vs : list NVar) (t : CVTerm vs) := let (a,_) := t in a.
Definition get_bcterm (bt : BCTerm) := let (a,_) := bt in a.

Print BTerm.
Definition selectbt (bts: list BTerm) (n:nat) : BTerm :=
  nth n bts (bterm [] (vterm nvarx)).

(*
Definition isnoncan (t: NTerm):=
match t with
| vterm _ => False
| oterm o _ => match o with
               | Can _ => False
               | NCan _ => True
               end
end.
*)
Lemma wf_cterm :
  forall t, wf_term (get_cterm t).
Proof using.
  introv; (  repeat match goal with
           | [ H : CTerm |- _ ] => destruct H
           | [ H : CVTerm _ |- _ ] => destruct H
         end
); simpl.
  allrw isprog_eq; unfold isprogram in *; repnd; allrw nt_wf_eq; sp.
Qed.


End terms3Generic.

Ltac irr_step :=
  match goal with
    | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_proof_irrelevance; subst
    | [ H1 : isprog_vars ?vs ?a, H2 : isprog_vars ?vs ?a |- _ ] =>
        assert (H2 = H1) by apply isprog_vars_proof_irrelevance; subst
  end.

Ltac irr := repeat irr_step.

Ltac destruct_cterms :=
  repeat match goal with
           | [ H : CTerm |- _ ] => destruct H
           | [ H : CVTerm _ |- _ ] => destruct H
         end.

Ltac dest_cterm H :=
  let t := type of H in
  match goal with
    | [ x : CTerm |- _ ] =>
      match t with
        | context[x] => destruct x
      end
    | [ x : CVTerm _ |- _ ] =>
      match t with
        | context[x] => destruct x
      end
  end.

(** A faster version of destruct_cterms.  We avoid destructing all of them. *)
Ltac dest_cterms H := repeat (dest_cterm H).

Ltac clear_deps h :=
  repeat match goal with
           | [ H : context[h] |- _ ] => clear H
         end.
Tactic Notation "nterm_ind" ident(h) ident(c) :=
  induction h using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "nterm_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using NTerm_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].


Ltac fold_terms_step :=
  match goal with
    | [ |- context[bterm [] ?x] ] => fold (nobnd x)
    | [ |- context[vterm ?v] ] => fold (mk_var v)
  end.

Ltac fold_terms := repeat fold_terms_step.




Ltac boolvar_step :=
  match goal with
    | [ |- context[beq_var ?v ?v] ] => rw <- beq_var_refl
    | [ |- context[memvar ?v ?s] ] =>
        let name := fresh "b" in
          remember (memvar v s) as name;
        match goal with
          | [ H : name = memvar v s |- _ ] =>
              symmetry in H;
              destruct name;
              [ rewrite fold_assert in H;
                  trw_h assert_memvar H;
                  simpl in H
              | trw_h not_of_assert H;
                  trw_h assert_memvar H;
                  simpl in H
              ]
        end
    | [ |- context[beq_var ?v1 ?v2] ] =>
        let name := fresh "b" in
          remember (beq_var v1 v2) as name;
        match goal with
          | [ H : name = beq_var v1 v2 |- _ ] =>
            destruct name;
              [ apply beq_var_true in H; subst
              | apply beq_var_false in H
              ]
        end
    | [ H : context[beq_var ?v ?v] |- _ ] => rw <- beq_var_refl in H
  end.

Ltac boolvar := repeat boolvar_step.
Ltac unfold_all_mk :=
       allunfold mk_var
       ;allunfold nobnd.


Hint Immediate wf_cterm : wf.
(* Hint Constructors isvalue. *)
Hint Constructors nt_wf bt_wf.

Ltac rwselectbt :=
match goal with
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite <- H1 in H2
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  , H2 : context [selectbt ?lbt ?n] |- _ ] => rewrite H1 in H2
|[ H1: bterm ?lv ?nt = selectbt ?lbt ?n  |-  context [selectbt ?lbt ?n] ] => rewrite <- H1
|[ H1: selectbt ?lbt ?n = bterm ?lv ?nt  |-  context [selectbt ?lbt ?n] ] => rewrite H1
end.

Tactic Notation "ntermd" ident(h) "as" simple_intropattern(I)  ident(c) :=
  destruct h as I;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].
Ltac prove_or := 
  try (left;cpx;fail);
  try (right;cpx;fail);
  try (left;left;cpx;fail);
  try (left;right;cpx;fail);
  try (right;left;cpx;fail);
  try (right;right;cpx;fail).

Ltac fold_selectbt :=
match goal with
[ |- context [nth ?n ?lbt (bterm [] (vterm nvarx))] ] =>
  fold (selectbt lbt n)
end.

(*
Ltac d_isnoncan H := 
  match type of H with
    isnoncan ?t => let tlbt := fresh t "lbt" in let tnc := fresh t "nc" in
              let tt := fresh "temp" in 
              destruct t as [tt|tt tlbt];[inverts H as H; fail|];
              destruct tt as [tt|tnc]; [inverts H as H; fail|]
  end.
*)

Section terms4Generic.

Context {NVar VarClass} {deqnvar : Deq NVar} {varclass: @VarType NVar VarClass deqnvar} 
  `{hdeq : Deq Opid} {gts : GenericTermSig Opid}.
Notation NTerm := (@NTerm NVar Opid).
Notation BTerm := (@BTerm NVar Opid).

Lemma cterm_eq :
  forall t u,
    get_cterm t = get_cterm u
    -> t = u.
Proof using.
  introv; destruct_cterms; simpl; sp; subst.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma cvterm_eq :
  forall vs t u,
    get_cvterm vs t = get_cvterm vs u
    -> t = u.
Proof using.
  introv; destruct_cterms; simpl; sp; subst.
  rewrite dep_pair_eq
    with (eq0 := eq_refl)
           (pb := i); auto.
  apply UIP_dec.
  apply bool_dec.
Qed.



Lemma free_vars_cterm :
  forall t, free_vars (get_cterm t) = [].
Proof using.
  introv; destruct_cterms; simpl.
  allrw isprog_eq; unfold isprogram in *; repnd; allrw; sp.
Qed.

Definition mk_cterm (t : NTerm) (p : isprogram t) :=
  exist isprog t (isprogram_implies t p).

Definition mk_ct (t : NTerm) (p : isprog t) := exist isprog t p.

Definition mk_wterm (t : NTerm) (p : wf_term t) := exist (@wf_term NVar _ _) t p.

Definition mk_wterm' (t : NTerm) (p : nt_wf t) :=
  exist wf_term t (nt_wf_implies t p).

(* Definition iscvalue (t : CTerm) : Type :=
  isvalue (get_cterm t).
 *)
 
Lemma mk_cv_pf :
  forall (vs : list NVar) (t:CTerm),
    @isprog_vars NVar _ Opid _ vs (@get_cterm NVar _ Opid _ t).
Proof using.
  destruct t; simpl.
  rw @isprog_eq in i; destruct i.
  rw @isprog_vars_eq; simpl; sp.
  unfold closed in *.
  allrw; sp.
Qed.

(** From a closed term, we can always make a term whose variables
 * are contained in vs: *)
Definition mk_cv (vs : list NVar) (t : @CTerm NVar _ Opid _) : @CVTerm NVar _ Opid _ vs :=
  exist (isprog_vars vs) (@get_cterm NVar _ Opid _ t) (mk_cv_pf vs t).


Lemma programs_bt_to_program :
  forall bts : list BCTerm,
  forall op,
    map (fun bt => num_bvars (get_bcterm bt)) bts = OpBindings op
    -> isprogram (oterm op (map get_bcterm bts)).
Proof using.
  sp; unfold isprogram; sp.
  rewrite closed_nt in *; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- @isprogram_bt_eq in i.
  inversion i; sp.
  constructor; sp.
  allrw in_map_iff; sp; subst.
  destruct a; destruct x; allsimpl.
  clear_deps i.
  rw <- @isprogram_bt_eq in i.
  inversion i; sp.
  rewrite <- H.
  rewrite map_map; unfold compose; sp.
Qed.

(* ---------------------------------------------------- *)


Definition list_rel {A} {B} (R : A -> B -> Prop) (ll : list A) (lr : list B) :=
  (length ll = length lr)
  #
  forall p1  p2 , LIn (p1, p2) (combine ll lr)
                  -> R p1 p2.

(** gets the nth element of a list of bterms. if n is out of range, it returns the variable x
*)

(* Howe defines T(L) as B_0(L) (no bterm constructor)
  and T_0(L) as closed terms of T(L)
  so, a term T_0(L) cannot have the vterm constructor
 at the root
 This a superset of T_0(L)
*)
Inductive not_vbterm: NTerm -> Type :=
  | nvbo : forall (op : Opid) (bts : list BTerm ),
           not_vbterm (oterm op bts).

(** this should not be required anymore. a closed NTerm is automatically not_vbterm. Proof below*)
Definition not_vbtermb (t : NTerm) : bool :=
  match t with
  | oterm _ _ => true
  | _ => false
  end.

Theorem closed_notvb : forall t: NTerm , (closed t) -> (not_vbterm t).
Proof using.
  intros ? Hclose. destruct t.
  unfold closed in Hclose. simpl in Hclose.
  inversion Hclose. constructor.
Qed.

Theorem selectbt_in :
  forall n (bts : list BTerm),
    n < length bts -> LIn (selectbt bts n) bts.
Proof using.
  intros. unfold selectbt.
  apply nth_in; auto.
Qed.

Lemma selectbt_cons :
  forall bt (bts : list BTerm) n,
    selectbt (bt :: bts) n = if beq_nat n 0 then bt else selectbt bts (n - 1).
Proof using.
  unfold selectbt; simpl; sp.
  destruct n; simpl; sp.
  destruct n; simpl; sp.
Qed.

(* Lemma isvalue_wf :
  forall c bts,
    isvalue (oterm (Can c) bts)
    -> map num_bvars bts = OpBindings (Can c).
Proof using. intros ? ?  Hval.
 inverts Hval as Hpr. inverts Hpr as Hclose Hwf.
 inverts Hwf; auto.
Qed.
 *)

(* Lemma isvalue_wf2: forall c bts,
  (isvalue (oterm (Can c) bts))
  -> length bts= length(OpBindings (Can c)).
Proof using. intros ? ?  Hval. apply isvalue_wf in Hval.
 (* fequalhyp H length.  why does this fail*)

 assert (length (map num_bvars bts) = length (OpBindings (Can c)))
   as Hlen by (rewrite Hval; reflexivity) .
 rewrite map_length in Hlen. auto.
Qed.
 *)

Notation bterm := (@bterm NVar Opid).
Lemma isprogram_wf3: forall o bts,
  (isprogram (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof using. intros ? ?  Hprog. apply isprogram_ot_iff  in Hprog. repnd.
 intros ? Hlt.
assert(nth n (map num_bvars bts) 0= nth n (OpBindings o) 0)
  as Hnth by (rewrite Hprog0; reflexivity).
 unfold selectbt.
 instlemma (@map_nth BTerm nat num_bvars
  bts (bterm [] (vterm nvarx))) as Hmapn.
 assert((num_bvars (bterm [] (vterm nvarx))) =0).
 compute; auto . rewrite H in Hmapn. rewrite Hmapn in Hnth. auto.
Qed.

(* Lemma isvalue_wf3: forall o bts,
  (isvalue (oterm o bts))
  -> forall n, (n<length bts) -> (num_bvars (selectbt bts n))= nth n (OpBindings o) 0.
Proof using. intros ? ?  Hval ? Hlt.
 inverts Hval as Hprog. apply isprogram_wf3 with (n:=n) in Hprog ; auto.
Qed. *)

Theorem var_not_prog : forall v,  (isprogram (vterm v)) -> void.
Proof using.
  unfold not. intros v Hpr.
  inversion Hpr as [Hclose ?].
  unfold closed in Hclose. simpl in Hclose. inversion Hclose.
Qed.

Lemma implies_isprogram_bt :
  forall bts,
    (forall l : BTerm, LIn l bts -> bt_wf l)
    -> flat_map free_vars_bterm bts = []
    -> forall bt : BTerm, LIn bt bts -> isprogram_bt bt.
Proof using.
  intros bts Hbf Hflat ? Hin.
  unfold isprogram_bt, closed_bt; split; auto.
  rw flat_map_empty in Hflat. apply Hflat; auto.
Qed.

Theorem ntbf_wf :
  forall (nt : NTerm) , (bt_wf (bterm [] nt)) -> nt_wf nt.
Proof using.
  introv Hin. inverts Hin. auto.
Qed.

Lemma implies_isprogram_bt0 :
  forall t ,
    isprogram (t)
    -> isprogram_bt (bterm [] t).
Proof using.
  unfold isprogram_bt, closed_bt, isprogram, closed; simpl; sp.
Qed.

Theorem is_program_ot_bts0 :
  forall o nt,
    isprogram nt
    -> OpBindings o = [0]
    -> isprogram (oterm o [bterm [] nt]).
Proof using.
  introv Hpr Hop. unfold isprogram, closed in *; simpl; repnd.
  split;auto. autorewrite with list. auto.

  constructor; sp; allsimpl; sp; subst; sp.
Qed.

Theorem is_program_ot_nth_nobnd :
  forall o nt1 bts,
    isprogram (oterm o  bts)
    -> LIn (bterm [] nt1) bts
    -> isprogram nt1.
Proof using. intros ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  apply Hisp in Hin. inverts Hin as Hclose Hbf. inverts Hbf.
  unfold closed_bt in Hclose. simpl in Hclose.
  split; auto.
Qed.

Theorem is_program_ot_fst_nobnd :
  forall o nt1 bts,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1.
Proof using.
  intros ? ? ? Hisp.
  apply is_program_ot_nth_nobnd with (nt1:=nt1) in Hisp; sp.
Qed.

Theorem is_program_ot_snd_nobnd :
  forall o bt1 nt2 bts, isprogram (oterm o ((bt1)::(bterm [] nt2):: bts))
   -> isprogram nt2.
Proof using. intros ? ? ? ? Hisp.
  apply is_program_ot_nth_nobnd with (nt1:=nt2) in Hisp; simpl; sp.
Qed.


Theorem is_program_ot_subst1 :
  forall o nt1 bts nt1r,
    isprogram (oterm o ((bterm [] nt1):: bts))
    -> isprogram nt1r
    -> isprogram (oterm o ((bterm [] nt1r):: bts)).
Proof using. intros ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. unfold closed in Hclos. simpl in Hclos.
    apply app_eq_nil in Hclos. repnd. 
    inverts Hispst as Hclosst Hispst. unfold closed in Hclosst.
    rewrite Hclosst. rewrite Hclos. split;auto.
    invertsn Hisp. constructor;auto.
    intros ? Hin. inverts Hin. constructor; auto.
    apply Hisp. right; auto.
Qed.

Theorem is_program_ot_subst2 :
  forall o bt1 nt2 bts nt2r,
    isprogram (oterm o (bt1::(bterm [] nt2):: bts))
    -> isprogram nt2r
    -> isprogram (oterm o (bt1::(bterm [] nt2r):: bts)).
Proof using. intros ? ? ? ?  ? Hisp Hispst. unfold isprogram.
    unfold closed. simpl.
    inverts Hisp as Hclos Hisp. inverts Hispst as Hclosst Hwfst.
    unfold closed in *. simpl.
    unfold closed in Hclos. allsimpl.
   simpl_vlist. rewrite Hclosst. rewrite Hclos0.
   simpl. split;auto.
   inverts Hisp as Hisp Hm. constructor;simpl; auto.
   intros ? Hin. dorn Hin;subst;auto. apply Hisp; auto.
   left; auto.
   dorn Hin; subst; auto.
   apply Hisp. right;right;auto.
Qed.


Theorem is_program_ot_nth_wf :
  forall lv o nt1 bts,
    isprogram (oterm o  bts)
    -> LIn (bterm lv nt1) bts
    -> nt_wf nt1.
Proof using. intros ? ? ? ? Hisp Hin. apply isprogram_ot_iff in Hisp. repnd.
  assert (isprogram_bt (bterm lv nt1)) as Hass by (apply Hisp; auto).
  inverts Hass as Hass Hbt. inversion Hbt; auto.
Qed.

Lemma combine_vars_map_sp :
  forall vars,
    combine vars (map (@vterm NVar Opid) vars) = map (fun v => (v, vterm v)) vars.
Proof using.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.

Lemma combine_vars_map :
  forall A,
  forall f : NVar -> A,
  forall vars,
    combine vars (map f vars) = map (fun v => (v, f v)) vars.
Proof using.
  induction vars; simpl; sp.
  rewrite IHvars; sp.
Qed.


Theorem in_selectbt: forall bt (bts : list BTerm),  LIn bt bts ->
    {n : nat $ n < length bts # selectbt bts n = bt}.
Proof using.
  intros ? ? Hin. induction bts. inverts Hin.
  invertsn Hin.
  - exists 0. split; simpl; auto. omega.
  - destruct IHbts; auto. exists (S x). repnd.
    split; simpl; try omega. auto.
Qed.

(**useful for rewriting in complicated formulae*)
Theorem ntot_wf_iff: forall o bts, nt_wf (oterm o bts)
    <=> map num_bvars bts = OpBindings o # forall n : nat,
     n < length bts -> bt_wf (selectbt bts n).
Proof using. introv. sp_iff Case; introv H.
  Case "->". inverts H as Hbf Hmap. split; auto.
    introv Hlt. apply Hbf. apply selectbt_in; auto.
  Case "<-". repnd. constructor; auto.
    introv Hin. apply in_selectbt in Hin.
    exrepnd. rw <- Hin0;auto.
Qed.

(**useful for rewriting in complicated formulae*)
Theorem bt_wf_iff: forall lv (nt : NTerm), bt_wf (bterm lv nt)
    <=> nt_wf nt.
Proof using. sp_iff Case; introv H.
  Case "->". inverts H as Hwf;  auto.
  Case "<-".  constructor; auto.
Qed.


Definition nvarxbt := bterm [] (vterm nvarx) .


Lemma isprogram_get_cterm :
  forall a, isprogram (get_cterm a).
Proof using.
  destruct a; sp; simpl.
  rw isprogram_eq; sp.
Qed.


Lemma oterm_eq :
  forall o1 o2 l1 l2,
    o1 = o2
    -> l1 = l2
    -> (@oterm NVar Opid) o1 l1 = oterm o2 l2.
Proof using.
  sp; allrw; sp.
Qed.

Notation oterm := (@oterm NVar Opid).
Notation vterm := (@vterm NVar Opid).


Lemma bterm_eq :
  forall l1 l2 n1 n2,
    l1 = l2
    -> n1 = n2
    -> bterm l1 n1 = bterm l2 n2.
Proof using.
  sp; allrw; sp.
Qed.

Theorem selectbt_map {gtsi gtso}: forall lbt n 
  (f: (@terms.BTerm NVar gtsi) -> (@terms.BTerm NVar gtso)) ,
  n<length lbt
  -> selectbt (map f lbt) n = f (selectbt lbt n).
Proof using.
  induction lbt; introv Hlt. inverts Hlt.
  simpl. destruct n; subst. reflexivity.
  unfold selectbt in *. allsimpl.
  assert (n < (length lbt)) by omega.
  auto.
Qed.


Theorem eq_maps_bt: forall (B : Type) (f : BTerm -> B) 
  (g : BTerm -> B) (la lc : list BTerm),
  length la = length lc 
  -> (forall n : nat, n < length la 
       -> f (selectbt la n) = g (selectbt lc n)) 
  -> map f la = map g lc.
Proof using. unfold selectbt. introv H2 H3. apply eq_maps2 in H3; auto. 
Qed.

Lemma vterm_inj: injective_fun vterm.
Proof using.
    introv Hf. inverts Hf. auto.
Qed.

Lemma map_eq_lift_vterm:  forall lvi lvo, 
  map vterm lvi = map vterm lvo -> lvi = lvo.
Proof using.
 intros.
  apply map_eq_injective with (f:=vterm); auto.
  exact vterm_inj.
Qed.

Global Instance deq_nterm : DeqSumbool NTerm.
Proof using deqnvar hdeq.
  intros x.
  nterm_ind1 x as [v1 | o1 lbt1 Hind] Case; intros y.

  - Case "vterm".
    destruct y as [v2 | o lbt2]; [  | right; intro Hc; inverts Hc].
    destruct (decideP (v1=v2)); subst;
    [ left; auto; fail
    | right; intro Hc; inverts Hc; sp
    ].

  - Case "oterm".
    destruct y as [v2 | o2 lbt2]; [ right; intro Hc; inverts Hc | ].
  SearchAbout Deq.
    destruct (decideP (o1=o2)); subst; [  | right; intro Hc; inverts Hc;sp].
    assert ((lbt1=lbt2) + (lbt1 <> lbt2)) as Hbt.
    Focus 2.
    dorn Hbt; subst; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    revert lbt2.
    induction lbt1.
    destruct lbt2; [left; auto | right; intro Hc; inverts Hc;sp ]; fail.
    destruct lbt2;  [ right; intro Hc; inverts Hc; fail | ].
    destruct a as [lv1 nt1]. destruct b as [lv2 nt2].
    lapply (IHlbt1);
      [ | introv Hin; apply Hind with (lv:=lv); eauto; right; auto].
    intro bdec.
    destruct (bdec lbt2); subst; [  | right; intro Hc; inverts Hc;sp;fail ].
    destruct (decideP (lv1=lv2));
      subst; [ | right; intro Hc; inverts Hc;sp;fail ].
    destruct (Hind nt1 lv2 (injL(eq_refl _) ) nt2); subst;
    [left; auto |  right; intro Hc; inverts Hc;sp ].
Defined.

Lemma lin_lift_vterm :
  forall v lv,
    LIn v lv <=> LIn (vterm v) (map vterm lv).
Proof using.
  induction lv; [sp | ]. simpl.
  rw <- IHlv; split; intros hp; try (dorn hp); sp; subst; sp.
  inverts hp. sp.
Qed.


Lemma map_removevars:
forall lvi lvr,
  map vterm (remove_nvars lvi lvr)
  = @lremove _ _ (map vterm lvi) (map vterm lvr).
Proof using.
  clear gts.
  intros. apply map_diff_commute.
  introv Hc. inverts Hc. auto.
Qed.

Definition all_vars_bt (bt : BTerm) := free_vars_bterm bt ++ bound_vars_bterm bt.

Lemma all_vars_ot : forall o lbt, 
  eq_set
    (all_vars (oterm o lbt))
    (flat_map all_vars_bt lbt).
Proof using.
  intros. unfold all_vars. simpl. unfold all_vars_bt.
  rewrite <- flat_map_fapp. refl.
Qed.


Theorem nil_remove_nvars_iff: forall l1 l2 : list NVar,
   (remove_nvars l1 l2) = [] <=> (forall x : NVar, LIn x l2 -> LIn x l1).
Proof using.
  intros. rw <- null_iff_nil. apply null_remove_nvars.
Qed.

Theorem nil_rv_single_iff: forall lv v ,
   (remove_nvars lv [v]) = [] <=> (LIn v lv).
Proof using.
  intros. rw <- null_iff_nil. rw null_remove_nvars.
  split; intro Hyp.
  apply Hyp. left. auto.
  introv Hin. apply in_list1 in Hin; subst; auto.
Qed.

Theorem selectbt_eq_in:  forall lv nt lbt n,
  bterm lv nt = selectbt lbt n
  -> n < length lbt
  -> LIn (bterm lv nt) lbt.
Proof using.
  introv Heq Hlt. rw Heq.
  apply selectbt_in; trivial.
Qed.

Lemma flat_map_closed_terms:
  forall (lnt : list NTerm), lforall closed lnt
    -> flat_map free_vars lnt = [].
Proof using.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. trivial.
Qed.

Lemma flat_map_progs:
  forall lnt, lforall isprogram lnt
    -> flat_map free_vars lnt = [].
Proof using.
  unfold lforall, closed. introv Hfr.
  apply flat_map_empty. introv Hin.
  apply Hfr in Hin. inverts Hin. auto.
Qed.

Theorem disjoint_lbt_bt :
  forall vs lbt lv nt,
    disjoint vs (flat_map bound_vars_bterm lbt)
    -> LIn (bterm lv nt) lbt
    -> disjoint vs lv.
Proof using.
  introv Hink1 Hin.
  apply disjoint_sym in Hink1; rw disjoint_flat_map_l in Hink1.
  apply Hink1 in Hin.
  simpl in Hin. rw disjoint_app_l in Hin.
  repnd; apply disjoint_sym. trivial.
Qed.



Definition selectnt (n:nat) (lnt : list NTerm): NTerm :=
  nth n lnt (vterm nvarx).

Lemma deq_bterm : DeqSumbool BTerm.
Proof using deqnvar hdeq.
  intros btx bty. destruct btx as [lvx ntx].
  destruct bty as [lvy nty].
  destruct (deq_nterm ntx nty);
  destruct (decideP (lvx=lvy)); subst;sp;
  right; introv Heq;
  inverts Heq; cpx.
Qed. (*FIX *)


Inductive nt_wf2 : NTerm -> [univ] :=
  | wfvt2 : forall nv : NVar, nt_wf2 (vterm nv)
  | wfot2 : forall (o : Opid) (lnt : list BTerm),
            length lnt = length (OpBindings o)
           -> (forall n, n < (length lnt) ->
                num_bvars (selectbt lnt n) = nth n (OpBindings o) 0
                # bt_wf2 (selectbt lnt n))
           -> nt_wf2 (oterm o lnt)
  with bt_wf2 : BTerm -> [univ] :=
    wfbt2 : forall (lnv : list NVar) (nt : NTerm),
           nt_wf2 nt -> bt_wf2 (bterm lnv nt).

(** mainly for convenience in proofs *)
Theorem  selectbt_in2:  forall (n : nat) (bts : list BTerm),
  n < length bts -> { bt : BTerm & (LIn bt bts # (selectbt bts n)=bt) }.
Proof using.
  intros. exists (selectbt bts n).
  split;auto. apply selectbt_in; trivial.
Defined.

Lemma nt_wf_nt_wf2 : forall t, (nt_wf t) <=> (nt_wf2 t).
Proof using.
    assert (0= num_bvars (bterm [] (vterm nvarx))) as XX by auto.
  nterm_ind1 t as [?| o lbt Hind] Case; split; introv Hyp; sp.
  - inverts Hyp as Hl Hyp. constructor. apply_length Hyp;sp.
    introv hlt. unfold selectbt. rw <- Hyp.
    rw XX. rw  map_nth; sp;[].
    fold (selectbt lbt n).
    pose proof (selectbt_in2 n lbt hlt) as Hbt.
    exrepnd. destruct bt as [lv nt].
    applydup Hind in Hbt1.
    rw Hbt0. constructor.
    apply Hl in Hbt1. inverts Hbt1.
    sp3.
  - inverts Hyp as Hl Hyp. constructor.
    + introv Hin. apply in_selectbt in Hin; auto;[].
      exrepnd. applydup Hyp in Hin1.
      rw Hin0 in Hin2. destruct l as [lv nt].
      constructor. exrepnd. invertsn Hin2.
      applysym selectbt_in in Hin1. rw Hin0 in Hin1.
      apply Hind in Hin1. sp3.
    + eapply (tiff_snd (eq_list2 _ 0 _ _)). rw map_length.
      split; auto;[]. introv Hlt. apply Hyp in Hlt.
      repnd. rw <- Hlt0.
      rw XX. rw  map_nth. sp.
Qed.



Definition bin_rel_nterm :=
  binrel_list  (vterm nvarx).

Theorem isprogram_ot_implies_eauto2 :
  forall o bts,
    isprogram (oterm o bts)
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n)).
Proof using.
  introv Hp Hlt. apply isprogram_ot_iff in Hp.
  apply selectbt_in in Hlt. exrepnd.
  eauto with slow.
Qed.


Lemma isprogram_bt_nobnd :
  forall t ,
    isprogram_bt (bterm [] t)
    -> isprogram (t).
Proof using.
  unfold isprogram_bt, closed_bt, isprogram, closed; intros ?  Hxx;  spc; allsimpl.
  match goal with
  [H: (bt_wf _) |- _ ] => inverts H
  end.
  assumption.
Qed.


Lemma free_vars_list_app :
  forall (ts1 ts2 : list NTerm),
    free_vars_list (ts1 ++ ts2)
    = free_vars_list ts1 ++ free_vars_list ts2.
Proof using.
  induction ts1; simpl; sp.
  rw IHts1; simpl.
  rw app_assoc; sp.
Qed.



Lemma isprog_ntwf_eauto : forall t, isprogram t -> nt_wf t.
Proof using. unfold isprogram. spc.
Qed.

Theorem isprogram_ot_if_eauto :
  forall o bts,
    map num_bvars bts = OpBindings o
    -> (forall bt, LIn bt bts -> isprogram_bt bt)
    -> isprogram (oterm o bts).
Proof using.
 intros. apply isprogram_ot_iff;spc.
Qed.


Lemma isprogramd :
  forall v, isprogram v
  -> {o : Opid $ {lbt : list BTerm $ v = oterm o lbt}}.
Proof using.
  introv Hpr.
  invertsn Hpr.
  destruct v; inverts Hpr.
  eexists; eexists ; eauto.
Qed.


(* Move *)
Lemma fold_combine : forall {A B} (v:A) (t:B), 
  [(v,t)] = (combine [v] [t]).
Proof using.
  intros. simpl. auto.
Qed.



(* Lemma noncan_not_value : forall e,
  isnoncan e
  -> isvalue e
  -> False.
Proof using.
  introv Hisnc Hisv.
  destruct e as [?| o lbt]; allsimpl; cpx.
  destruct o; cpx.
  inverts Hisv.
Qed. *)

Theorem isprogram_ot_if_eauto2 :
  forall o bts,
    map num_bvars bts = OpBindings o
    -> (forall n, n< length bts -> isprogram_bt (selectbt bts n))
    -> isprogram (oterm o bts).
Proof using.
  introv Hn Hp. apply isprogram_ot_iff; dands; spcf.
  introv Hin. apply in_selectbt in Hin. exrepnd.
  eauto with slow.
  rw <- Hin0.
  eauto with slow.  
Qed.



Lemma closed_implies:
  forall (t : NTerm),
    closed t -> (forall x, !LIn x (free_vars t)).
Proof using.
  introv cl.
  unfold closed in cl.
  allrw; simpl; try (complete sp).
Qed.




Lemma list_nil_btwf: forall es,
(forall l : BTerm, LIn l (map (bterm []) es) -> bt_wf l)
<->
(forall l : NTerm, LIn l es -> nt_wf l).
Proof using.
  intros ?.
  split; intros H  ? Hin.
- apply (bt_wf_iff []).
  apply H. apply in_map; auto. 
- apply in_map_iff in Hin. exrepnd. subst.
  constructor; auto. 
Qed.

Require Import Coq.Program.Basics.

Open Scope program_scope.

Lemma flat_map_bterm_nil : forall gts lnt,
flat_map free_vars_bterm
  (map ((@terms.bterm NVar gts) []) lnt) = 
flat_map free_vars lnt.
Proof.
  induction lnt; auto.
  simpl. f_equal; auto.
Qed.

Lemma flat_map_vterm : forall gts (lv: list NVar),
flat_map free_vars_bterm
  (map ((@terms.bterm NVar gts) [] ∘ terms.vterm) lv) = lv.
Proof using.
  induction lv; auto.
  simpl. f_equal; auto.
Qed.


Lemma subset_flat_map_lbt:
forall lbt (l lv : list NVar) (n : NTerm),
LIn (bterm l n) lbt ->
subsetv (flat_map free_vars_bterm lbt) lv 
-> subsetv (free_vars n) (l ++ lv).
Proof using.
  intros ? ? ? ? Hin Hs.
  rewrite subset_flat_map in Hs.
  rewrite subsetv_prop.
  apply_clear Hs in Hin.
  simpl in Hin.
  rewrite subsetv_prop in Hin.
  intros x Hn. specialize (Hin x).
  rewrite in_remove_nvars in Hin.
  rewrite in_app_iff; destruct (dmemvar x l); cpx.
Qed.

Lemma select_selectbt : forall n lbt (b:BTerm),
select n lbt = Some b
<-> (selectbt lbt n = b /\ n < length lbt).
Proof using.
  intros ? ? ?.
  split; intros Hin.
- pose proof Hin.
  apply select_lt in Hin. split;[|assumption].
  apply nth_select1 with (def:= bterm [] (vterm nvarx))in Hin.
  unfold selectbt.
  congruence.
- repnd. eapply nth_select3; auto.
  apply Hin0.
Qed.


Lemma size_pos : forall (t:NTerm), 
  0<(size t).
Proof.
  intros. destruct t; simpl; omega.
Qed.

Definition preservesVarclass (ta tb : NTerm) :Prop :=
forall vc,
varsOfClass (all_vars ta) vc
-> varsOfClass (all_vars tb) vc.

Definition preservesVarclassBT (ta tb : BTerm) :Prop :=
forall vc,
varsOfClass (all_vars_bt ta) vc
-> varsOfClass (all_vars_bt tb) vc.

Lemma subsetAllVarsLbt : forall o lbt bt, 
  LIn bt lbt -> subset (all_vars_bt bt) (all_vars (oterm o lbt)).
Proof.
  intros ? ? ? Hin.
  rewrite all_vars_ot.
  unfold all_vars_bt.
  eapply subset_trans;
    [|apply subset_flat_map_r; apply Hin].
  apply subset_refl.
Qed.

Lemma varsOfClassOT : forall o lbt c,
  varsOfClass (all_vars (oterm o lbt)) c
  -> forall bt, LIn bt lbt -> varsOfClass (all_vars_bt bt) c.
Proof using.
  intros ? ? ? Hv ? Hin ? Hinn.
  apply Hv. revert Hinn.
  apply subsetAllVarsLbt.
  assumption.
Qed.

Definition allvars_bterm : forall lv nt,
  eq_set 
    (all_vars_bt (bterm lv nt))
    (lv ++ all_vars nt).
Proof using.
  clear.
  intros ? ?. apply eqsetv_prop.
  intro. unfold all_vars, all_vars_bt.
  simpl.
  repeat rewrite in_app_iff.
  repeat rewrite in_remove_nvars.
  destruct (decideP (LIn x lv)); (* firstorder does not know about decidability *)
  firstorder.
Qed.


Lemma flat_map_free_var_vterm: forall lv:list NVar, flat_map free_vars (map vterm lv)=lv.
Proof using.
  induction lv;sp;simpl;f_equal;sp.
Qed.

Lemma flat_map_bound_var_vterm: forall lv:list NVar, flat_map bound_vars (map vterm lv)=[].
Proof using.
  induction lv;sp;simpl;f_equal;sp.
Qed.

Lemma size_subterm4 :
     forall  (lb : list (BTerm)) (nt : NTerm) (lv : list NVar),
       LIn (bterm lv nt) lb -> size nt < S (addl (map size_bterm lb)).
Proof using.
  induction lb; auto; simpl; try tauto;[].
  intros ? ? Hin. dorn Hin.
- subst. simpl. omega.
- apply IHlb in Hin. omega.
Qed.


Lemma subsetAllVarsLbt2 : forall lbt lv (nt : NTerm), 
  LIn (bterm lv nt) lbt -> subset (all_vars nt) (flat_map all_vars_bt lbt).
Proof using.
  clear.
  intros.
  eapply subset_trans;
    [|eapply subset_flat_map_r; eauto].
  rewrite allvars_bterm.
  apply subset_app_l.
  refl.
Qed.

Lemma subsetBoundVarsLbt3 : forall (lbt : list BTerm) (lv : list NVar) (nt : NTerm), 
  LIn (bterm lv nt) lbt -> subset lv (flat_map bound_vars_bterm lbt).
Proof using.
  intros.
  eapply subset_trans;
    [|eapply subset_flat_map_r; eauto].
  apply subset_app_r.
  refl.
Qed.


Lemma flat_map_bterm_nil_allvars:
  forall  (lnt : list NTerm),
   flat_map all_vars_bt (map (terms.bterm []) lnt) = flat_map all_vars lnt.
Proof using.
  intros. rewrite flat_map_map.
  apply eq_flat_maps.
  intros ? Hin.
  unfold compose, all_vars_bt.
  simpl.
  refl.
Qed.

Lemma subsetAllVarsLbt3
     : forall (lbt : list BTerm) (lv : list NVar) (nt : terms.NTerm),
       LIn (bterm lv nt) lbt -> subset lv (flat_map all_vars_bt lbt).
Proof.
  introv Hin.
   eapply transitivity;
    [|apply subset_flat_map_r; eauto].
  rewrite allvars_bterm.
  apply subset_app_r. refl.       
Qed.

End terms4Generic.

Ltac  varsOfClassSimpl :=
repeat match goal with
[ H: varsOfClass (all_vars (oterm ?o ?lbt)) true |- _ ] =>
  specialize (varsOfClassOT _ _ _ H); clear H; intro H;
  repeat match goal with
  | [HH : LIn _ lbt |- _] => apply (fun lin => (conj lin (H _ lin))) in HH
  end; repnd;
repeat match goal with
[H:context [varsOfClass (all_vars_bt (bterm _ _)) true] |- _]
  => setoid_rewrite allvars_bterm in H (* if it fails, continuing may cause a loop *)
end;
repeat rewrite @varsOfClassApp in *
end.




(* Move *)
Hint Rewrite @flat_map_bterm_nil @flat_map_free_var_vterm
  remove_nvars_eq : SquiggleEq.


Hint Rewrite @all_vars_ot @allvars_bterm : allvarsSimpl.

Hint Rewrite @all_vars_ot @allvars_bterm @varsOfClassApp : SquiggleEq.


Hint Resolve isprogram_ot_if_eauto : slow.
Hint Immediate isprogram_get_cterm.
Hint Resolve isprog_implies : isprog.
Hint Extern 100 (LIn _ _) => complete (simpl; sp) : isprog.
Hint Resolve nt_wf_implies : slow.
Hint Resolve nt_wf_eq: slow.
Hint Resolve is_program_ot_nth_nobnd : slow.
Hint Resolve deq_bterm.
Hint Immediate deq_nterm.
Hint Immediate isprogram_get_cterm.
Hint Resolve isprog_ntwf_eauto : slow.
Tactic Notation "disjoint_reasoningv" :=
  (allunfold all_vars); repeat( progress disjoint_reasoning).
Ltac destruct_bterms:=
repeat match goal with
[bt : BTerm |- _] =>
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  destruct bt as [btlv btnt]
end.

Ltac noRepDis :=
(repeat match goal with
[H: no_repeats [] |- _] => clear H
|[H: no_repeats (_::_) |- _] =>
  let Hnrd := fresh "Hnrd" in
  apply no_repeats_as_disjoint in H;
  destruct H as [Hnrd H]
end); disjoint_reasoningv; 
rewrite in_single_iff in *; subst; tauto; try tauto.

(* try to move to list.v  . disjoint_reasoningv performs 
  some non-list-based unfolding which may
  be done using a database *)
Ltac inauto:=
(repeat match goal with
[H: no_repeats [] |- _] => clear H
|[H: no_repeats (_::_) |- _] =>
  let Hnrd := fresh "Hnrd" in
  apply no_repeats_as_disjoint in H;
  destruct H as [Hnrd H]
end); disjoint_reasoningv; 
unfold subset in *;
unfold disjoint in *;
repeat match goal with 
| [H:context[LIn _ (_::_) ] |- _] => simpl in H; try setoid_rewrite or_false_r in H
| [|- context[LIn _ (_::_)]] => simpl; try setoid_rewrite or_false_r
| [H:context[LIn _ (flat_map _ _) ] |- _] => setoid_rewrite in_flat_map in H
| [|- context[LIn _ (flat_map _ _)]] => setoid_rewrite in_flat_map
| [H:context[LIn  _ (map _ _)]|- _] => setoid_rewrite in_map_iff in H
| [|- context[LIn  _ (map _ _)]] => setoid_rewrite in_map_iff
| [H:context[LIn  _ (remove_nvars _ _)]|- _] => setoid_rewrite in_remove_nvars in H; simpl in H
| [|- context[LIn  _ (remove_nvars _ _)]] => setoid_rewrite in_remove_nvars; simpl
| [H: _ = []|- _] => apply null_iff_nil in H; unfold null in H; simpl in H
| [|- _ = []] => apply null_iff_nil; unfold null; simpl
| [|- context[LIn  _ (map _ _)]] => setoid_rewrite in_map_iff
end;
subst.





Local Ltac 
illFormedCase :=
 (try reflexivity; try (simpl;rewrite flat_map_vterm; reflexivity)).




(* Move *)
Ltac destructbtdeep2 bt tac :=
  let btlv := fresh bt "lv" in
  let btnt := fresh bt "nt" in
  let btlv1 := fresh btlv "1" in
  let btlv2 := fresh btlv "2" in
  let btlv3 := fresh btlv "3" in
  destruct bt as [btlv btnt];
  destruct btlv as [| btlv1]; tac;
  try(destruct btlv as [| btlv2]; tac);
  try(destruct btlv as [| btlv3]; tac).

Ltac destructlbt lbt tac :=
  repeat (
  let b := fresh "b" in
  destruct lbt as [| b lbt];tac; []).

Hint Rewrite memvar_singleton : SquiggleEq.

Hint Rewrite remove_nvars_cons_r : SquiggleEq2.

Hint Rewrite
  <- beq_var_refl : SquiggleEq.

Ltac disjoint_flat_allv :=
repeat match goal with
[ Hdis : disjoint ?lv (flat_map all_vars_bt ?lbt) ,
  Hin : LIn _ ?lbt |- _]
  => rewrite disjoint_flat_map_r in Hdis; specialize (Hdis _ Hin); unfold all_vars_bt in Hdis;
  simpl in Hdis
end.


Ltac disjoint_reasoning2 :=
match goal with
| [  |- disjoint _ (_ ++ _) ] => apply disjoint_app_r;split
| [  |- disjoint (_ ++ _) _ ] => apply disjoint_app_l;split
| [  |- disjoint _ (_ :: (_ :: _)) ] => apply disjoint_cons_r;split
| [  |- disjoint (_ :: (_ :: _)) _ ] => apply disjoint_cons_l;split
| [  |- disjoint _ (_ :: ?v) ] => notNil v;apply disjoint_cons_r;split
| [  |- disjoint (_ :: ?v) _ ] => notNil v;apply disjoint_cons_l;split
| [  |- disjoint _ _ ] => (sp;fail  || apply disjoint_sym; sp;fail)
| [  |- _ <> _] => apply disjoint_neq_iff
| [  |- ! (LIn _ _)] => apply disjoint_singleton_l
(** important to leave it the way it was .. so that repeat progress won't loop*)
| [ H: disjoint _ (_ ++ _) |- _ ] => apply disjoint_app_r in H;sp
| [ H: disjoint (_ ++ _) _ |- _ ] => apply disjoint_app_l in H;sp
| [ H: disjoint _ (_ :: (_ :: _)) |- _ ] => apply disjoint_cons_r in H;sp
| [ H: disjoint (_ :: (_ :: _)) _ |- _ ] => apply disjoint_cons_l in H;sp
| [ H: disjoint _ (_ :: ?v) |- _ ] => notNil v;apply disjoint_cons_r in H;sp
| [ H: disjoint (_ :: ?v) _ |- _ ] => notNil v;apply disjoint_cons_l in H;sp
| [ H: !(disjoint  _ []) |- _ ] => provefalse; apply H; apply disjoint_nil_r
| [ H: !(disjoint  [] _) |- _ ] => provefalse; apply H; apply disjoint_nil_l
| [ H: (disjoint  _ []) |- _ ] => clear H
| [ H: (disjoint  [] _) |- _ ] => clear H
| [ H: ! (LIn _ _) |- _] => apply disjoint_singleton_l in H
| [ H: _ <> _  |- _] => apply disjoint_neq_iff in H
end.

Tactic Notation "disjoint_reasoningv2" :=
  (unfold all_vars in *); repeat( progress disjoint_reasoning2).
  
Ltac disjoint_flat2 :=
disjoint_reasoning2; disjoint_flat_allv;disjoint_reasoningv2.


Hint Resolve subsetAllVarsLbt2 : subset. 

Hint Rewrite remove_var_nil remove_nvars_nil_r:  SquiggleEq.

    Ltac rwHyps :=
    unfold closed, closed_bt in *;
    repeat match goal with
    [ H: _ = _ |- _] =>  repeat rewrite H; hide_hyp H
    end; show_hyps.





    Hint Resolve @subsetAllVarsLbt3 @subsetBoundVarsLbt3 : subset.



