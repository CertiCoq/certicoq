Require Import L4.expression.
Require Import L4.variables.
Require Import L4.polyEval.

Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import SquiggleEq.varImplZ.
(*
Require Import SquiggleEq.list.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.lmap.
*)

Require Import Coq.Arith.Arith 
Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega Coq.Program.Program 
Coq.micromega.Psatz.
Require Import SquiggleEq.ExtLibMisc.

Require Import Common.RandyPrelude.
Open Scope N_scope.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_5_to_L5.
Require Import SquiggleEq.list.

Definition L4_5_Term :Type := (@NTerm NVar L4_5Opid).
Definition L4_5_BTerm :Type := (@BTerm NVar L4_5Opid).

Section PolyEval45.


Require Import Common.TermAbs.  
Context {Abs4_4a: @TermAbs (@L4_5Opid)}.

Local Notation AbsTerm := (AbsTerm _ Abs4_4a).
Local Notation absGetOpidBTerms := (absGetOpidBTerms _ Abs4_4a).
Local Notation absApplyBTerm := (absApplyBTerm _ Abs4_4a).
Local Notation absGetTerm := (absGetTerm _ Abs4_4a).
Local Notation absMakeTerm := (absMakeTerm _ Abs4_4a).
Local Notation absMakeBTerm := (absMakeBTerm _ Abs4_4a).


Typeclasses eauto :=4.

Open Scope program_scope.

Require Import List.

Require Import Common.ExtLibMisc.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Import Monad.MonadNotation.
Open Scope monad_scope.

(* modified from L4.polyEval.eval_n to remove the cases for \box *)
Fixpoint eval_n (n:nat) (e:AbsTerm) {struct n} :  option AbsTerm :=
match n with
|0%nat => None
| S n =>  match (absGetOpidBTerms e) with |None => None | Some (o,lbt) =>
  match (o,lbt) with
  (* values *)
  | (NLambda,_)
  | (NFix _ _,_) => Some e

  (* (possibly) non-values *)
  | (NLet, [a;f]) =>
        a <- absGetTerm a;;
        a <- eval_n n a ;;
        s <- (absApplyBTerm f [a]);;
        eval_n n s
  | (NDCon d ne, lb) => 
        vs <- flatten (map (fun b => t <- absGetTerm b ;; eval_n n t)lb) ;;
        (absMakeTerm (map absMakeBTerm vs) o)
  | (NMatch ldn, disc::brs) => 
        disc <- absGetTerm disc;;
        disc <- eval_n n disc;;
        match (absGetOpidBTerms disc) with
        | Some (NDCon d ne, clb) =>
          cvs <- flatten (map absGetTerm clb);;
          b <- polyEval.find_branch _ d (length cvs) (combine (map fst ldn) brs);;
          s <- (absApplyBTerm b cvs);;
          eval_n n s
        | _ => None
        end
  | (NApply, [f;a]) =>
        a <- absGetTerm a;;
        a <- eval_n n a ;;
        f <- absGetTerm f;;
        f <- eval_n n f;;
        match (absGetOpidBTerms f) with
        | Some (NLambda,[b]) =>
            s <- (absApplyBTerm b [a]);;
            eval_n n s
        | Some (NFix nMut i,lm) =>
            let pinds := List.seq 0 (length lm) in
            let ls := map (fun n => absMakeTerm lm (NFix nMut n)) pinds in
            ls <- flatten ls;;
            im <- select i lm;;
            s <- (absApplyBTerm im ls);;
            s_a_pp <- (absMakeTerm (map absMakeBTerm [s;a]) NApply);;
            eval_n n s_a_pp
        | _ => None
        end
    | _ => None
  end
  end
end.
End PolyEval45.

Definition mapOpidL4_to_L4_5 (o: L4Opid) : L4_5Opid :=
  match o with
  | polyEval.NBox _ => NFix 0 0  (* garbage *)
  | polyEval.NLambda   => NLambda
  | polyEval.NFix nMut a => NFix nMut a
  | polyEval.NDCon c nargs    => NDCon c nargs
  | polyEval.NApply => NApply
  | polyEval.NLet => NLet
  | polyEval.NMatch numargsInBranches => NMatch numargsInBranches
  end.
    

Fixpoint L4_2_to_L4_5 (e:L4_2_Term) : L4_5_Term :=
  match e with
  | vterm v => vterm v
  | oterm o lbt =>
    let lbt := map (btMapNt L4_2_to_L4_5) lbt in
    match o with
    | polyEval.NBox _ =>
      let f:= nvarx in
      let arg := nvary in
      Fix_e' [bterm [f] (Lam_e arg (vterm f))] 0
    | _ => oterm (mapOpidL4_to_L4_5 o) lbt
    end
  end.

Require Import Common.TermAbs.
Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.


Require Import SquiggleEq.AssociationList.


Section evaln42_45.

Lemma L4_2_to_L4_5_fvars t:
  nt_wf t ->    
  (free_vars (L4_2_to_L4_5 t)) =  free_vars t.
Proof using.
  induction t as [x | o lbt Hind] using NTerm_better_ind; intros Hwf; auto;[].
  simpl.
  assert (Hb: flat_map free_vars_bterm (map (btMapNt L4_2_to_L4_5) lbt)
          = flat_map free_vars_bterm lbt).
    rewrite flat_map_map. apply eq_flat_maps. unfold compose, btMapNt. simpl.
    intros bt Hin. destruct bt as [lv nt].
    simpl. erewrite Hind; eauto. ntwfauto.

  destruct o; [ | | | | | | ]; auto;[].
  simpl. ntwfauto. simpl in *. destruct lbt; auto;[].
  inverts HntwfSig.
Qed.

Lemma L4_2_to_L4_5_vc s: varsOfClass (all_vars s) true -> varsOfClass (all_vars (L4_2_to_L4_5 s)) true.
Proof using.
  induction s as [x | o lbt Hind] using NTerm_better_ind; intros Hvc; auto;[].
  autorewrite with SquiggleEq in Hvc.
  simpl in *.
  assert (varsOfClass (flat_map all_vars_bt (map (btMapNt L4_2_to_L4_5) lbt)) true).
  - rewrite flat_map_map. intros ? Hin. apply in_flat_map in Hin. exrepnd.
    destruct x as [lv nt].
    unfold compose in *; simpl in *.
    autorewrite with SquiggleEq in Hin0.
    rewrite in_app_iff in Hin0.
    dorn Hin0.
    + apply Hvc. apply in_flat_map. eexists; dands; eauto.
      autorewrite with SquiggleEq. rewrite in_app_iff.
      left; auto.
    + unfold varsOfClass, lforall in Hind.
      eapply Hind; eauto.
      intros aa Hinn.
      apply Hvc. apply in_flat_map. eexists; dands; eauto.
      autorewrite with SquiggleEq. rewrite in_app_iff.
      right; auto.
   
- destruct o; unfold Fix_e'; simpl; autorewrite with SquiggleEq; auto;[].
  simpl. compute. intros. repeat in_reasoning; subst; auto.
Qed.
  

Lemma L4_2_to_L4_5_ntwf t:
  nt_wf t ->    
  nt_wf (L4_2_to_L4_5 t).
Proof using.
  induction t as [x | o lbt Hind] using NTerm_better_ind; intros Hwf;
    [constructor | ].
  simpl.
  invertsn Hwf.

  assert (forall l : BTerm, LIn l (map (btMapNt L4_2_to_L4_5) lbt) -> bt_wf l).
  - intros ? Hin. apply in_map_iff in Hin. exrepnd. subst.
    destruct x as [lv nt]. constructor. eapply Hind; eauto.
    apply Hwf in Hin0. inverts Hin0. assumption.
 - 
  destruct o.
  Focus 7.
  apply wft_ntwf. refl.
  all: constructor; auto; simpl in *; rewrite map_map;
    erewrite map_ext by (intros; rewrite numBvarsBtMapNt; auto); auto.
Qed.


Require Import SquiggleEq.alphaeq.
Require Import SquiggleEq.UsefulTypes.
Require Import DecidableClass.


Lemma ssubst_aux_commute f sub:
  ssubst_aux (L4_2_to_L4_5 f) (map_sub_range L4_2_to_L4_5 sub) =
    L4_2_to_L4_5 (ssubst_aux f sub).
Proof using.
  revert sub.
  induction f as [x | o lbt Hind] using NTerm_better_ind; intros ?;
    [simpl; rewrite sub_find_map; dsub_find s; auto | ].
  simpl.  rewrite map_map.
  assert (
      map (fun x : BTerm => ssubst_bterm_aux (btMapNt L4_2_to_L4_5 x) (map_sub_range L4_2_to_L4_5 sub))
          lbt = map (fun x : BTerm => btMapNt L4_2_to_L4_5 (ssubst_bterm_aux x sub)) lbt).
    apply eq_maps.
    intros bt Hin.
    destruct bt as [lv nt]. simpl.
    f_equal. rewrite sub_filter_map_range_comm. apply (Hind nt lv); auto.
  destruct o; simpl; try rewrite map_map; f_equal; [ | | | | | | ]; auto;[].
  unfold Fix_e', Lam_e. simpl.
  do 6 f_equal.
  rewrite <- sub_filter_app_r.
  rewrite sub_find_sub_filter; [refl | cpx].
Qed.  

Lemma ssubst_commute f sub:
  prog_sub sub
  -> ssubst (L4_2_to_L4_5 f) (map_sub_range L4_2_to_L4_5 sub) =
    L4_2_to_L4_5 (ssubst f sub).
Proof using.
  intros Hs.
  change_to_ssubst_aux8;[ apply ssubst_aux_commute; auto | ].
  unfold range, map_sub_range.
  rewrite map_map, flat_map_map.
  unfold compose. simpl.
  rewrite (proj2 (@flat_map_empty _ _ _ _)); auto.
  intros s Hin. destruct s as [x t]. specialize (Hs _ _ Hin).
  simpl. unfold isprogram, closed in *. rewrite L4_2_to_L4_5_fvars; tauto.
Qed.

Require Import L4_to_L4_2_correct.
Import L42.
Lemma fixwf_commute f:
   L4_5_to_L5.fixwf (L4_2_to_L4_5 f)  = fixwf f.
Proof using.
  induction f using NTerm_better_ind;[refl | ].
  simpl in *.
  assert(
  ball
    (map (fun x : BTerm => L4_5_to_L5.fixwf (get_nt (btMapNt L4_2_to_L4_5 x))) lbt) =
  ball (map (fun x : BTerm => fixwf (terms.get_nt x)) lbt)).
  - f_equal. apply eq_maps. intros ? Hin.
    destruct x as [lv nt]. simpl. eauto.
   - destruct o; simpl in *; repeat rewrite map_map; unfold compose; simpl; auto.
  rewrite H0.
  f_equal.
  f_equal.
  apply eq_maps.
  intros.
  destruct x as [lv nt].
  simpl.
  destruct nt; try refl. destruct l; try refl.
Qed.

Definition eval42 := @polyEval.eval_n (Named.TermAbsImplUnstrict variables.NVar L4Opid).
Definition eval45 := @eval_n (Named.TermAbsImplUnstrict variables.NVar L4_5Opid).


(**  can be obtained for free using a parametricity plugin 
Lemma eval42PreservesGoodness n t:
  isprogram t -> option_rectp (isprogram) True (eval42 n t).
Admitted.
*)

Ltac simplApplyBTerm Hd :=
   unfold Named.applyBTermClosed;
   repeat rewrite map_length; repeat rewrite numBvarsBtMapNt; simpl;
   cases_if as Hd;[apply beq_nat_true in Hd | ].

Hint Constructors eval : certicoq.

(* (evaln n) does not commute with L4_2_to_L4_5 :
box x  evaluates to box
fix (\f\y.f) x evaluates to (\y.fix (\f\y.f)) x, not fix (\f\y.f).
The latter is achieved only after 1 additional step.
*)
Lemma L4_2_to_L4_5_correct t n v:
  isprogram t
  -> (eval42 n t) = Some v
  -> isprogram v /\ eval (L4_2_to_L4_5 t) (L4_2_to_L4_5 v).
Proof using.
  revert t v.
  induction n as [ | n Hind]; intros ? ? Hpr Hev; [invertsn Hev | ].
  destruct t as [x | o lbt]; [ invertsn Hev | ].
  pose proof Hpr as Hprb.
  apply isprogram_ot_iff in Hpr. repnd.
  destruct o; try invertsn Hev.
  (* lambda value *)
- let tac:= invertsn Hpr0 in destructlbt lbt tac.
  let tac:= invertsn H2 in destructlbt lbt tac.
  let tac:= invertsn Hpr0 in destructbtdeep2 b tac.
  simpl. split; [assumption | apply eval_Lam_e ].
  (* fix value *)
- apply (f_equal (@length _ )) in Hpr0.
  simpl in *. autorewrite with list in Hpr0.
  split; [assumption | ].
  apply eval_fix_e2; try rewrite map_length; auto.
  
(* constructor value *)
- clear Hprb. simpl.
  revert Hev.
  unfold L4_5_Term. f_equal. pose proof Hpr0 as Hlen.
  apply map0lbt2 in Hpr0. remember (map get_nt lbt) as lnt.
  clear Heqlnt. subst.
  rewrite map_map. simpl.
  match goal with
    [ |- context[flatten ?l]] =>
    remember (flatten l) as olvt
  end.
  unfold Named.mkBTermSafe.
  destruct olvt as [lvt | ]; intros Hev; invertsn Hev.
  repeat rewrite map_map. simpl.
  repeat rewrite map_map. simpl.
  symmetry in Heqolvt.
  pose proof (flattenSomeImpliesLen _ _ Heqolvt) as Hlenn.
  apply' (@flattenSomeImplies) Heqolvt.
  apply (f_equal (@length _)) in Hlen. simpl in Hlen.
  autorewrite with list in Hlen.
  rewrite map_length in Hlenn.
  split; [ | ].
    apply isprogram_ot_iff. simpl.
    unfold num_bvars. rewrite map_map.
    simpl. rewrite repeat_map_len.
    split;[ f_equal; congruence | ].
    intros ? Hin. apply in_map_iff in Hin.
    exrepnd. subst.
    apply implies_isprogram_bt0.
    eapply combine_in_right in Hin0;[ | rewrite <- Hlenn,
                                        <- (map_length (fun x : NTerm => eval42 n x)); refl ].
    exrepnd. pose proof Hin1 as Hinb.
    rewrite <- (map_id lvt) in Hinb.
    apply lin_combine_map_implies in Hinb. exrepnd. subst.
    apply Heqolvt in Hin1. subst.
    eapply Hind; eauto.
    apply in_combine_l in Hinb0. apply (in_map (bterm [])) in Hinb0.
    apply Hpr in Hinb0. apply isprogram_bt_nobnd in Hinb0. assumption.
    
  rewrite <- map_map.
  rewrite <- (map_map L4_2_to_L4_5). subst.
  apply eval_con_e2; repeat rewrite map_length; auto.
  intros ? ? Hin.
  apply lin_combine_map_implies in Hin. exrepnd. subst.
  pose proof Hin0 as Hint.
  apply in_combine_l in Hint.
  apply (in_map (bterm [])) in Hint.
  specialize (Hpr _ Hint). apply isprogram_bt_nobnd in Hpr.
  apply Hind; auto; [].
  apply Heqolvt.
  rewrite <- (map_id lvt).
  change b with (id b).
  apply lin_combine_map. assumption.
- simpl.
  simpl; destruct lbt as [ | f lbt]; simpl; try invertsn Hev;[].
  simpl. simpl in *. let tac:=(invertsn Hpr0) in destructbtdeep2 f tac.
  simpl in *. pose proof (Hpr _ ltac:(left; refl)) as Hprf.
  apply isprogram_bt_nobnd in Hprf.
  simpl in *.
  simpl; destruct lbt as [ | a lbt]; simpl;  try invertsn Hev ;[].
  simpl. simpl in *. let tac:=(invertsn Hpr0) in destructbtdeep2 a tac.
  simpl; destruct lbt as [ | a lbt]; simpl;  try invertsn Hev ;[].
  simpl in *. pose proof (Hpr _ ltac:(right; left; refl)) as Hpra.
  apply isprogram_bt_nobnd in Hpra.
  pose proof (fun v => Hind _ v Hprf) as Hindf.
  pose proof (fun v => Hind _ v Hpra) as Hinda.
  destruct (eval42 n fnt) as [fv | ]; simpl in *;[ | invertsn Hev; fail].
  specialize (Hindf _ eq_refl).
  destruct fv as [ |fvo fvlbt]; [ invertsn Hev| ].
  destruct Hindf as [Hprfe Hindf].
  simpl in *. destruct fvo;  simpl in *; try  invertsn Hev.
  (* Lambda *)
  +
    simpl; destruct fvlbt as [ | f fvlbt]; simpl; try invertsn Hev;[].
    simpl; destruct fvlbt as [ | ff fvlbt]; simpl; try invertsn Hev ;[].
    destruct (eval42 n ant) as [av | ]; simpl in *;[ | invertsn Hev].
    specialize (Hinda _ eq_refl).
    destruct Hinda as [Hprae Hinda].  
    apply isprogram_ot_iff in Hprfe. repnd.
    revert Hev.
    simplApplyBTerm Hd; intros Hev; [ | invertsn Hev].
    let tac := invertsn Hprfe0 in destructbtdeep2 f tac.
    simpl in *.
    apply Hind in Hev;[ |  apply isprogram_bt_implies; eauto; inreasoning;cpx].
    unfold apply_bterm in *. simpl in *.
    rewrite <- ssubst_commute in Hev;[ | prove_sub_range_sat].
    simpl in *.
    repnd. split; [assumption | ].
    eapply eval_App_e; eauto.

  (* Fix *)
  +
    destruct (eval42 n ant) as [av | ]; simpl in *;[ | invertsn Hev].
    specialize (Hinda _ eq_refl).
    destruct Hinda as [Hprae Hinda].  
    apply isprogram_ot_iff in Hprfe. repnd.

    revert Hev.
    unfold Named.mkBTerm. simpl. repeat rewrite map_map.
    do 1 rewrite flatten_map_Some. intros Hev.
    remember (select index fvlbt) as ofbs.
    destruct ofbs as [fbs | ];[ | invertsn Hev]. symmetry in Heqofbs.
    simpl in *. revert Hev.
    simplApplyBTerm Hd; intros Hev; [ | invertsn Hev].
    apply Hind in Hev ;[
                   | apply isprogram_ot_iff; split; [refl | inreasoning; cpx]
                     ;try apply implies_isprogram_bt0; eauto ].
    * unfold apply_bterm in *.
      destruct fbs as [flv fntt].
      simpl in *.
      apply (select_map (btMapNt L4_2_to_L4_5)) in Heqofbs.
      rewrite <- ssubst_commute in Hev.
      Focus 2.
        intros ? ? Hin. apply in_combine, proj2 in Hin.
        apply in_map_iff in Hin. exrepnd. subst. clear Hin0.
        apply isprogram_ot_iff. eauto; fail.

      rewrite  map_sub_range_combine, map_map in Hev.
      apply (f_equal (@length _)) in Hprfe0. simpl in Hprfe0.
      unfold num_bvars in *. simpl in *. autorewrite with list in Hprfe0.
      autorewrite with list in Hd.
      subst.
      repnd. split; [assumption | ].
      eapply eval_FixApp_e; eauto;
        unfold num_bvars, Fix_e' in *; simpl in *;
          repeat rewrite map_length; try assumption; try congruence.
    * apply nth_error_In in Heqofbs.
      apply isprogram_bt_implies; try rewrite map_length; eauto.
      intros ? Hin.
      apply in_map_iff in Hin. exrepnd. subst. clear Hin0.
      apply isprogram_ot_iff. eauto.
  + destruct fvlbt; invertsn Hev.
    destruct (eval42 n ant) as [av | ]; simpl in *;[ | invertsn Hev].
    specialize (Hinda _ eq_refl).
    destruct Hinda as [Hprae Hinda].  
    apply isprogram_ot_iff in Hprfe. repnd.
    simpl. unfold apply_bterm. simpl. unfold Lam_e. simpl.
    invertsn Hev.
    split; [ apply isprogram_ot_iff; simpl; firstorder; fail | ].

    (* evaluate arg in boxapp case of L4.polyEval *)
    eapply eval_FixApp_e; unfold select; simpl; eauto; simpl; eauto.

    
    simpl. unfold apply_bterm. simpl.
    eapply eval_App_e; eauto;[apply eval_Lam_e | eapply eval_end; eauto| ].
    simpl. unfold subst. clear Hprfe.
    rewrite ssubst_trivial3;[apply eval_Fix_e; fail | ].
    inreasoning. invertsn H. simpl.
    rewrite  L4_2_to_L4_5_fvars;[ | apply Hprae].
    rewrite (proj1 Hprae). unfold disjoint. firstorder.
  
(* let *)
- simpl; destruct lbt as [ | a lbt]; simpl; try invertsn Hev ;[].
  simpl; destruct lbt as [ | f lbt]; simpl; try invertsn Hev ;[].
  simpl; destruct lbt as [ | ]; simpl; try invertsn Hev ;[].
  simpl. destruct a as [la a]; simpl; try invertsn Hev ;[].
  simpl. destruct la; simpl; try invertsn Hev ; [].
  simpl. destruct f as [lf f]; simpl; try invertsn Hev ;[].
  simpl. revert Hev. unfold Named.applyBTermClosed, num_bvars. simpl.
  cases_if; auto; [ | do 1 rewrite matchNoneNone; intros Hev; invertsn Hev].
  destruct lf as [ | x lf]; invertsn H.
  destruct lf as [ | xx lf]; invertsn H.
  pose proof (Hpr (bterm [] a) ltac:(cpx)) as Hw. apply isprogram_bt_nobnd in Hw.
  specialize (Hpr _ ltac:(right;cpx)).
  pose proof (fun v => Hind _ v Hw) as Hinda.
  do 1 rewrite <- fold_option_bind.
  intros Hev.
  destruct (eval42 n a) as [av42 | ]; simpl in *;[ | invertsn Hev].
  specialize (Hinda _ eq_refl).
  apply Hind in Hev;[ | apply isprogram_bt_implies; auto;  inreasoning; cpx ].
  unfold apply_bterm in *. simpl in *. repnd.
  rewrite <- ssubst_commute in Hev; auto; [ | prove_sub_range_sat].
  repnd. split; [assumption | ].
  eapply eval_Let_e; eauto.

  (* match *)
- simpl.
  simpl; destruct lbt as [ | d lbt]; simpl; try invertsn Hev ;[].
  simpl. simpl in *. let tac:=(invertsn Hpr0) in destructbtdeep2 d tac.
  simpl in *. pose proof (Hpr _ ltac:(left; refl)) as Hprd.
  apply isprogram_bt_nobnd in Hprd.
  pose proof (fun v => Hind _ v Hprd) as Hindd.
  destruct (eval42 n dnt) as [vd | ];[ simpl | invertsn Hev].
  specialize (Hindd _ eq_refl).
  destruct Hindd as [Hpre Hindd].
  destruct vd as [ | do dlbt ]; [ invertsn Hev | simpl ].
  destruct do; try  invertsn Hev;[]; simpl in *.
(*  do 1 rewrite map_map in Hev.
  erewrite map_ext;[ | intros; rewrite getNtNamedMapBtCommute; refl].
  setoid_rewrite <- opmap_flatten_map. *)
  apply isprogram_ot_iff in Hpre. repnd; simpl in *.
  erewrite safeGetNTmap in Hev; eauto. simpl.
  rewrite map_length in Hev.
  (*  rewrite findBranchMapBtCommute. *)
  simpl in *.
  match type of Hev with
    context[@polyEval.find_branch ?o ?ta ?d ?na ?b] 
      => remember  (@polyEval.find_branch o ta d na b) as sb; destruct sb as [br | ]
   end;[ | invertsn Hev].
  simpl in *.
  unfold Named.applyBTermClosed in *.
  revert Hev.
  rewrite map_length in *. (* rewrite numBvarsBtMapNt. *)
  cases_if; intros Hev; [ | invertsn Hev].
  revert Hev.
  simpl. destruct br as [brlv br]. simpl.
  apply beq_nat_true in H.
  eapply isProgramLNoBnd in Hpre; eauto.
  pose proof Hpre0 as Hnt.
  apply map0lbt2 in Hnt.
  symmetry in Heqsb.
  simpl in *. pose proof Hpr0 as Hbb.
  apply (f_equal (@length _)) in Hpr0. unfold num_bvars in *.
  pose proof Heqsb as Heqsbb.
  apply find_branch_some in Heqsb.
  rewrite <- combine_map_snd in Heqsb; [ | repeat rewrite map_length in *;  congruence].
  apply proj2, proj1 in Heqsb.
  repnd. specialize (Hpr _ ltac:(right; apply Heqsb)).
  intros Hev.
  apply Hind in Hev;[ | apply isprogram_bt_implies; try rewrite map_length; eauto].
  unfold apply_bterm in *. simpl in *.
  rewrite <- ssubst_commute in Hev;
    [ | intros ? s Hin; apply Hpre; eapply in_combine_r; eauto; fail].
  rewrite  map_sub_range_combine in Hev.
  apply (f_equal (@length _)) in Hpre0. simpl in Hpre0.
  unfold num_bvars in *. simpl in *. autorewrite with list in *.
  subst.
  repnd. split; [assumption | ].
  eapply eval_match_e2; eauto; autorewrite with list; auto.
  + unfold Con_e.
    rewrite Hnt in Hindd. simpl in Hindd.
    match goal with
      [H: eval ?l ?r1  |- eval ?l ?r2 ] => assert (r1=r2);[ | congruence]
    end.
    f_equal; f_equal;[ |   rewrite map_map; simpl;rewrite <- map_map; refl].
    repeat rewrite map_length. refl.
  + rewrite map_length. setoid_rewrite findBranchMapBtCommute.
    rewrite map_length. rewrite Heqsbb. refl.
  + assumption.
  + revert Hbb. clear. rewrite map_map. intro.
    erewrite map_ext;[ | intros; rewrite numBvarsBtMapNt; refl]. assumption.
- simpl.
  split; [assumption | ].
  apply eval_Fix_e.
Qed.

Print Assumptions L4_2_to_L4_5_correct.
(* Closed under the global context *)
Print L4_5Opid.

Section L4_5_postproc.
Fixpoint let_bindn (lv : list NVar) (lbt : list L4_5_Term) (last: L4_5_Term):=
  match lv, lbt with
  | [], [] => last
  | v::lv, bt::lbt =>
    Let_e v bt (let_bindn lv lbt last)
  | _,_ => last
  end.

(* delte? *)
Fixpoint let_bind (lv : list NVar) (lbt : list L4_5_BTerm) (last: L4_5_Term):=
  match lv, lbt with
  | [], [] => last
  | v::lv, bt::lbt =>
    Let_e v (get_nt bt) (let_bind lv lbt last)
  | _,_ => last
  end.

Definition let_bindc o avoid (cargs : list L4_5_Term) :=
      let fv : list NVar := freshVars (length cargs) (Some true) avoid [] in
      let_bindn fv cargs (oterm o (map (fun v => bterm [] (vterm v)) fv)).

(** an additional postproc phase to ensure that the args of constructors are
variables, as needed in L6.
the caller must ensure: subset (all_vars e) avoid
 *)

Definition isConstructor o : bool :=
  match o with
    | NDCon _ _ => true
    | _ => false
  end.
    
Fixpoint L4_5_constr_vars (avoid : list NVar) (e:L4_5_Term) {struct e}: L4_5_Term :=
  match e with
  | vterm v => vterm v
  | oterm o lbt =>
    let lbt := map (btMapNt (L4_5_constr_vars avoid)) lbt in
    if (isConstructor o)
    then let_bindc o avoid (map get_nt lbt)
    else
      oterm o lbt
  end.

(* zetaCLe t1 t2=> t2 is obtained by eta expanding some constructors in t1 *)
Inductive zetaCLe (avoid : list NVar): L4_5_Term -> L4_5_Term -> Prop :=
| zetav : forall v, zetaCLe avoid (vterm v) (vterm v)
| zetao : forall lbt1 lbt2 o,
    (SetoidList.eqlistA (liftRBt (zetaCLe avoid)) lbt1 lbt2)
    -> zetaCLe avoid (oterm o lbt1) (oterm o lbt2)
| zetaoe : forall d n cargs1 cargs2,
    (SetoidList.eqlistA (zetaCLe avoid) cargs1 cargs2)
    -> zetaCLe
        avoid
        (oterm (NDCon d n) (map (bterm []) cargs1))
        (let_bindc (NDCon d n) avoid cargs2).

Lemma sub_letbindng:
   forall (fv : list NVar) (sub : Substitution) ( cargs : list L4_5_Term),
  subset (dom_sub sub) fv ->
  forall t : NTerm,
  forall vn : list NVar,
  NoDup vn ->
  disjoint vn fv ->
  Datatypes.length vn = Datatypes.length cargs ->
  ssubst_aux (let_bindn vn cargs t) sub =
  let_bindn vn (map (fun t0 : NTerm => ssubst_aux t0 sub) cargs) (ssubst_aux t sub).
Proof using.
  intros ? ? ?.
  induction cargs  as [  | carg1 cargs1]; 
  intros Hs t  vn pp0 pp1 pp;
  destruct vn as [ | v vn];
    invertsn pp; auto; simpl.
  autorewrite with SquiggleEq. 
  simpl. unfold Let_e. do 4 f_equal.
  rewrite sub_filter_disjoint1;[ | noRepDis2].
  erewrite  IHcargs1; eauto; try noRepDis2.
Qed.

Lemma sub_letbindn:
   forall (fv : list NVar) (sub : Substitution) ( cargs : list L4_5_Term),
  subset (dom_sub sub) fv ->
  forall t : NTerm,
  disjoint (free_vars t) (dom_sub sub) ->
  forall vn : list NVar,
  NoDup vn ->
  disjoint vn fv ->
  Datatypes.length vn = Datatypes.length cargs ->
  ssubst_aux (let_bindn vn cargs t) sub =
  let_bindn vn (map (fun t0 : NTerm => ssubst_aux t0 sub) cargs) t.
Proof using.
  intros.
  erewrite sub_letbindng; eauto.
  f_equal.
  rewrite ssubst_aux_trivial_disj; auto.
Qed.

Lemma sub_letbindn2:
  forall (fv : list NVar) (sub : Substitution) ( cargs : list L4_5_Term),
    disjoint (flat_map free_vars cargs) (dom_sub sub)
  -> subset (dom_sub sub) fv ->
  forall t : NTerm,
  forall vn : list NVar,
  NoDup vn ->
  disjoint vn fv ->
  Datatypes.length vn = Datatypes.length cargs ->
  ssubst_aux (let_bindn vn cargs t) sub =
  let_bindn vn cargs (ssubst_aux t sub).
Proof using.
  intros.
  erewrite sub_letbindng; eauto.
  f_equal.
  rewrite <- (map_id cargs) at 2.
  apply eq_maps. intros.
  rewrite ssubst_aux_trivial_disj; [ refl | ].
  eapply disjoint_flat_map_l; eauto.
Qed.

Lemma sub_letbindc fv sub o cargs:
   subset (dom_sub sub) fv -> 
  (ssubst_aux (let_bindc o fv cargs) sub)
  = let_bindc o fv (map (fun t => ssubst_aux t sub) cargs).
Proof using.
  intros Hs.
  unfold let_bindc. simpl. autorewrite with list.
  addFreshVarsSpec2 vn pp. simpl.
  setoid_rewrite <- Heqvn.
  clear Heqvn. repnd.
  set (tt:=(oterm o (map (fun v : NVar => bterm [] (vterm v)) vn))).
  assert (disjoint (free_vars tt) (dom_sub sub)) as Has.
    unfold tt. simpl. setoid_rewrite flat_map_vterm.
    apply disjoint_sym.
    eapply subset_disjoint; eauto. disjoint_reasoning; fail.

  remember tt as t.
  clear Heqt. clear tt.
  revert dependent vn. revert_all.
  induction cargs  as [  | carg1 cargs1]; intros;
  destruct vn as [ | v vn];
    invertsn pp; auto; simpl;
      [rewrite ssubst_aux_trivial_disj; autorewrite with SquiggleEq; auto | ].
  autorewrite with SquiggleEq. 
  simpl. unfold Let_e. do 4 f_equal.
  rewrite sub_filter_disjoint1;[ | noRepDis2].
  erewrite  IHcargs1; eauto; try noRepDis2.
Qed.

Lemma ssubst_aux_commute_L4_5_zeta fv:
  (forall f1 f2 sub1 sub2,
      zetaCLe fv f1 f2 ->
      subset (dom_sub sub1) fv->
      sub_range_rel (zetaCLe fv) sub1 sub2 ->
      zetaCLe fv
        (ssubst_aux f1 sub1)
        (ssubst_aux f2 sub2))*
  forall f1 f2 sub1 sub2,
      liftRBt (zetaCLe fv) f1 f2 ->
      subset (dom_sub sub1) fv->
      sub_range_rel (zetaCLe fv) sub1 sub2 ->
      liftRBt (zetaCLe fv)
        (ssubst_bterm_aux f1 sub1)
        (ssubst_bterm_aux f2 sub2).
Proof using.
  apply NTerm_BTerm_ind.
- intros x ? ? ? Hsal Hs Hsub.
  invertsn Hsal. simpl.
  dsub_find ss; symmetry in Heqss;
    [eapply sub_range_rel_sub_find in Heqss |
     eapply sub_range_rel_sub_none in Heqss] ; eauto;
      exrepnd; rwHyps; eauto. constructor.
- intros ? ? Hind ? ? ? Hal Hsub Hsal.
  invertsn Hal.
  + simpl. apply zetao.
    induction Hal; simpl; constructor;
      [ apply Hind; cpx; try ntwfauto; fail| ].
    apply IHHal; firstorder.
  + simpl.
    pose proof Hsal as Hsalb.
    unfold sub_range_rel in Hsalb.
    apply ALRangeRelSameDom in Hsalb.
    rewrite sub_letbindc; [ | setoid_rewrite <- Hsalb]; auto.
    simpl.
    rewrite map_map. simpl.
    rewrite <- map_map.
    autorewrite with SquiggleEq.
    constructor.
    induction Hal; simpl; constructor;[ | apply IHHal; firstorder].
    specialize (Hind (bterm [] x)).
    specialize (Hind ltac:(cpx)). simpl in Hind.
    specialize (Hind (bterm [] x') sub1 sub2). simpl in Hind.
    autorewrite with SquiggleEq in Hind.
    dimp Hind; auto;[constructor; auto | ].
    clear Hind.
    inverts hyp. assumption.
- intros ? ? Hind ? ? ? Hbal Hsal. intros.
  inverts Hbal. simpl. constructor.
  apply Hind; eauto with SquiggleEq.
  + rewrite <- dom_sub_sub_filter.
    apply subset_diff. apply subset_app_r.
    assumption.
  + apply sub_range_rel_sub_filter. assumption.
Qed.


Require Import List.

Lemma fvars_letbindn t cargs2 vn:
  disjoint vn (flat_map free_vars cargs2) ->
  length vn= length cargs2 ->
             free_vars (let_bindn vn cargs2 t) =
             flat_map free_vars cargs2
             ++ (remove_nvars vn (free_vars t)).
Proof using.
  revert vn.
  rename cargs2 into cargs.
  induction cargs; simpl; auto;
  intros ? Hdis Hlen;
  destruct vn as [ | v vn]; inverts Hlen; auto; [].
  simpl. autorewrite with list.
  rewrite IHcargs; auto;[ | noRepDis2].
  rewrite <- app_assoc.
  f_equal.
  rewrite remove_app.
  f_equal;[ | apply (remove_nvars_comm [v] vn); fail].
  rewrite remove_trivial; auto.
  noRepDis2.
Qed.

(* see the failed attempt below to understand why 
all_vars cannot be replaced with free_vars *)
Lemma L4_5_zeta fv:
  (forall t u,  subset (all_vars t) fv -> zetaCLe fv t u
        -> free_vars t = free_vars u)
 * (forall t u,  subset (all_vars_bt t) fv -> liftRBt (zetaCLe fv) t u
        -> free_vars_bterm t = free_vars_bterm u).
Proof using.
  apply NTerm_BTerm_ind.
- intros ? ?  Hsub Hal.
  inverts Hal. refl. 
- intros ? ? Hind ? Hsub Hal. simpl.
  autorewrite with SquiggleEq in Hsub.
  invertsn Hal.
  + simpl.
    do 2 rewrite flat_map_as_appl_map.
    f_equal.
    apply eqListA_eq. revert Hal.
    apply eqListA_map.
    intros. apply Hind; auto.
    rewrite subset_flat_map in Hsub. eauto.
  + rewrite flat_map_map. unfold compose. simpl.
    unfold let_bindc.
    autorewrite with SquiggleEq in Hsub.
    addFreshVarsSpec2 vn pp.
    clear Heqvn. repnd.
    assert (flat_map free_vars cargs1 = flat_map free_vars cargs2) as Hx.
    * do 2 rewrite flat_map_as_appl_map.
      f_equal.
      apply eqListA_eq. revert Hal.
      apply eqListA_map.
      intros.
      specialize (Hind (bterm [] a1)
                       ltac:(apply in_map_iff; eauto)
                       (bterm [] a2)
                 ).
      autorewrite with SquiggleEq in Hind.
      simpl in Hind.
      rewrite subset_flat_map in Hsub.
      apply Hind; auto;[]. constructor; auto; fail.
    * setoid_rewrite flat_map_fapp in Hsub.
      apply subset_app in Hsub. repnd.
      rewrite  Hx in Hsub0.
      apply disjoint_sym in pp1.
      rewrite fvars_letbindn; auto;
        [ | apply disjoint_sym; eapply subset_disjoint; eauto; fail].
      simpl. rewrite flat_map_map. unfold compose.
      simpl. rewrite flat_map_single, map_id.
      autorewrite with SquiggleEq list.
      auto.
- intros ? ? Hind ? Hsub Hal. invertsn Hal.
  simpl. f_equal.
  autorewrite with SquiggleEq in Hsub.
  apply subset_app in Hsub. repnd.
  eapply Hind; eauto.
Qed.

Lemma L4_5_zeta2 fv:
  (forall t u,  subset (free_vars t) fv -> zetaCLe fv t u
        -> free_vars t = free_vars u)
 * (forall t u,  subset (free_vars_bterm t) fv -> liftRBt (zetaCLe fv) t u
        -> free_vars_bterm t = free_vars_bterm u).
Proof using.
  apply NTerm_BTerm_ind.
- admit.
- admit.
- intros ? ? Hind ? Hsub Hal. invertsn Hal.
  simpl. f_equal.
  autorewrite with SquiggleEq in Hsub.
  simpl in Hsub.
  eapply Hind; eauto.
Abort.


Lemma sub_range_rel_zeta_fvars fv sub1 sub2:
      subset ((flat_map all_vars (range sub1))) fv->
      sub_range_rel (zetaCLe fv) sub1 sub2 ->
      flat_map free_vars (range sub1)
      = flat_map free_vars (range sub2).
Proof using.
  intros Hs. revert dependent sub2.
  induction sub1; destruct sub2; intros; repnd; simpl in *; auto; try contradiction.
  repnd. subst.
  apply subset_app in Hs. repnd.
  erewrite (fst (L4_5_zeta fv)); eauto;[ f_equal; eauto].
Qed.

Lemma ssubst_commute_L4_5_zeta fv f1 f2 sub1 sub2:
      sub_range_sat sub1 closed ->
      zetaCLe fv f1 f2 ->
      subset (dom_sub sub1 ++ (flat_map all_vars (range sub1))) fv->
      sub_range_rel (zetaCLe fv) sub1 sub2 ->
      zetaCLe fv
        (ssubst f1 sub1)
        (ssubst f2 sub2).
Proof using.
  intros  Hs Hal Hss Hsr.
  apply subset_app in Hss. repnd.
  change_to_ssubst_aux8;
    [ apply ssubst_aux_commute_L4_5_zeta; auto; fail | ].
  erewrite <- sub_range_rel_zeta_fvars; eauto.
  change_to_ssubst_aux8.
  disjoint_reasoning.
Qed.


Lemma zetaRefl fv:
  (forall f, zetaCLe fv f f) *
  (forall f, liftRBt (zetaCLe fv) f f).
Proof using.
  apply NTerm_BTerm_ind; try constructor; eauto.
  apply eqListA_refl. assumption.
Qed.  


Global Instance ReflZeta lv: RelationClasses.Reflexive (zetaCLe lv).
Proof using.
  intros t. apply zetaRefl.
Qed.  
Ltac dZeta := match goal with
  [H:  SetoidList.eqlistA (liftRBt (zetaCLe _)) (cons _ _) _ |- _ ]
   =>  let Hr := fresh H "r" in inverts H as H Hr
| [H:  SetoidList.eqlistA (liftRBt (zetaCLe _)) [] _ |- _ ]
   =>  invertsn H
| [H:  liftRBt (zetaCLe _) (bterm _ _) _ |- _ ]
   =>  invertsn H
| [H:  zetaCLe _ (oterm _ _) _ |- _ ]
   =>  invertsn H
    end.

    (* Move to L4_5_to_L5.v *)
Lemma unify_Con_e (cargs : list L4_5_Term) len d:
      len= length cargs ->
      oterm (NDCon d len) (map (bterm []) cargs) = Con_e d cargs.
Proof using.
  intros. unfold Con_e. subst. auto.
Qed.

(* Move to SquiggleEq *)
Lemma in_combine_same {A:Type} (e v: A) pvs: LIn (e, v) (combine pvs pvs)
                                             -> e =v /\ In e pvs.
Proof using.
  induction pvs; cpx. simpl. 
  firstorder; inverts H ;auto.
Qed.

Require Import Datatypes.
  Require Import SetoidList.
  Lemma eval_letbindc d lv  v cargs:
    closed v
  ->   flat_map free_vars cargs = []
  -> eval (Con_e d cargs) v
  -> eval (let_bindc (NDCon d (length cargs)) lv cargs) v.
Proof using.
  intros Hcv Hcc Hev. invertsna Hev Hev.
  unfold let_bindc.
  apply (f_equal (map get_nt)) in Hev2.
  repeat rewrite map_map in Hev2. simpl in Hev2.
  repeat rewrite map_id in Hev2.
  repnd. subst. clear Hev1.
  addFreshVarsSpec2 vn pp. simpl. simpl.
  hnf in Hcv. rwsimpl Hcv.
  clear Heqvn. repnd.
  assert (forall pvs, (forall t, In t pvs -> eval t t) -> (flat_map free_vars pvs = []) ->
             eval
    (let_bindn vn cargs
       (Con_e d
          (((pvs ++ (map vterm vn)) )) )) 
    (Con_e d (pvs++vs))) as Hx; [ | specialize (Hx []); unfold Con_e in Hx; simpl in Hx;
  rewrite map_map in *; autorewrite with list in Hx;  
  setoid_rewrite  <-  pp; apply Hx; cpx].
  revert dependent vs.
  revert dependent vn.
  induction cargs; intros; simpl in *;  dlist_len vn; simpl in *; dlist_len vs.
  - autorewrite with list. apply eval_Con_e; auto.
    intros ? ? Hin. apply  in_combine_same in Hin. repnd.  subst. firstorder.
  - simpl. simpl in *. dLin_hyp. eapply eval_Let_e; eauto. simpl.
    unfold subst.
    apply app_eq_nil in Hcv.  apply app_eq_nil in Hcc. repnd.
    rewrite ssubst_ssubst_aux
      by (simpl; autorewrite with list; rwHyps; disjoint_reasoning).
    erewrite sub_letbindn2; simpl; eauto;
      try noRepDis;[ | rwHyps; repeat disjoint_reasoning].
    repeat rewrite map_map. simpl. rewrite map_app. simpl.
    autorewrite with SquiggleEq.
    rewrite map_ssubst_aux; [ | rwHyps; disjoint_reasoning; fail].
    rewrite map_ssubst_aux;[ | simpl; rwsimplC; noRepDis; fail].
    repeat rewrite <- map_cons.
    rewrite <- map_app.
rewrite unify_Con_e; [ | repeat (autorewrite with list; simpl); refl].
    do 2  rewrite <- snoc_append_r.
    rewrite snoc_as_append.
    apply IHcargs; auto; try noRepDis.
    + revert Hyp H. clear.
      setoid_rewrite in_app_iff. firstorder. subst. eapply eval_end; eauto.
    + rewrite flat_map_app. simpl. rwHyps. refl.
Qed.

(* Move to SquiggleEq *)
Tactic Notation "forder" ident_list (idl) :=
  revert idl; clear; firstorder.
  
(* Move to SquiggleEq and heterogenize *)
Lemma liftRBTeqlist (R : L4_5_Term ->  L4_5_Term -> Prop) es lbt:
  eqlistA (liftRBt R) (map (bterm []) es) lbt
  -> exists esp, eqlistA R es esp /\ lbt = map (bterm []) esp.
Proof using.
  revert es lbt.
  induction es; intros ? Heq; inverts Heq.
  + eexists. split. constructor. refl.
  + inverts H1. apply IHes in H3. exrepnd. eexists. split. econstructor; eauto.
      subst. auto.
Qed.

Lemma eval_Con_e_zeta :
  forall (lv : list NVar) (es vs : list NTerm) (esp : list L4_5_Term),
  length vs = length es ->    
  eqlistA (zetaCLe lv) es esp ->
  (forall e v : NTerm,
   LIn (e, v) (combine es vs) ->
   (forall e' : L4_5_Term,
    zetaCLe lv e e' -> exists v', eval e' v' /\ zetaCLe lv v v') /\
   closedSubsetVars lv e /\ closedSubsetVars lv v) ->
  exists vsp,
  eqlistA (zetaCLe lv) vs vsp /\
  length esp = length vsp /\
  (forall e0 v0 : NTerm, LIn (e0, v0) (combine esp vsp) -> eval e0 v0).
Proof using.
  intros ? ? ? ? ? Heq. revert dependent vs. induction Heq;
     [intros; simpl in *; dlist_len vs; eexists []; cpx | ].
  intros ? Hlen Hind. simpl in *. dlist_len vs. symmetry in H1.
  eapply IHHeq in H1; [ | intros; apply Hind; cpx].
  exrepnd. specialize (Hind _ _ ltac:(left; refl)).
  repnd. specialize (Hind0 _ H). exrepnd.
  exists (v'::vsp).  simpl. dands; auto.
  intros. in_reasoning; cpx.
Qed.  
(* Move to SquiggleEq *)
Lemma liftRbt_eqlista   (R : L4_5_Term ->  L4_5_Term -> Prop)  vs vsp:
  eqlistA R vs vsp ->
  eqlistA (liftRBt R) (map (bterm []) vs) (map (bterm []) vsp).
Proof using.
  intros H. induction H; constructor; auto.
  constructor; auto.
Qed.

Lemma zetalFvars fv:
  (forall (t : list NTerm) (u : list L4_5_Term),
      eqlistA (zetaCLe fv) t u -> subset (flat_map all_vars t) fv -> 
      flat_map free_vars t = flat_map free_vars u).
Proof using.
  intros ? ? Heq Hs. induction Heq; auto.
  simpl in *. apply subset_app in Hs. repnd.
  f_equal; eauto;[].
  apply  (fst (L4_5_zeta fv)); auto.
Qed.  

Lemma zetalFvarsNil fv:
  (forall (t : list NTerm) (u : list L4_5_Term),
      eqlistA (zetaCLe fv) t u -> lforall (closedSubsetVars fv) t -> 
      flat_map free_vars u = []).
Proof using.
  intros ? ? Heq Hs. erewrite <- zetalFvars; eauto.
-  apply flat_map_empty. intros ? Hin. apply Hs in Hin. apply Hin.
- apply subset_flat_map.  intros ? Hin. apply Hs in Hin. apply Hin. 
Qed.  

Lemma L4_5_constr_vars_zeta lv (e  v: L4_5_Term):
  closedSubsetVars lv e
  -> eval e v
  -> forall e', zetaCLe lv e e'
  -> exists v', eval e' v'
      /\ (zetaCLe lv v v').
Proof using.
  pose proof
       (eval_ind2  (closedSubsetVars lv) (closedSubsetVars_bt lv)) as Hx.
  unfold L4_5_Term.
  specialize (Hx (fun e v => forall e', zetaCLe lv e e'
  -> exists v', eval e' v'
      /\ (zetaCLe lv v v'))).
  apply Hx; clear Hx.
- simpl. intros ? ? ? ? He. unfold Lam_e in He.
  repeat dZeta.  eexists.
  split; [ apply eval_Lam_e | ].
  do 3 constructor. assumption.
- intros ? ? vfb ? varg ? Hevf Heva Hevs Hindf _ Hpref Hinda _ Hprea Hinds _ _ ? Hz.
  unfold App_e in Hz.
  repeat dZeta.
  rename ntr0 into e1z, ntr into e2z.
  specialize (Hinda _ Hzr).
  specialize (Hindf _ Hz).
  exrepnd.
  unfold Lam_e in *.
  repeat dZeta.
  rename ntr into vfbz, v' into vargz.
  hnf in Hprea, Hpref.
  rwsimpl Hpref.
  repnd. 
  eapply  ssubst_commute_L4_5_zeta with (sub2 := [(x,vargz)])in Hindf0;
    [specialize (Hinds _ Hindf0) | | | ]; simpl; auto;
      [ | prove_sub_range_sat | autorewrite with list; forder Hprea Hpref].
  exrepnd.
  eexists; split; [ eapply eval_App_e ;eauto | ] ; eauto; fail.
- intros ? ? ? Hlen Hsev Hind ? Hz. unfold Con_e in Hz.
  repeat dZeta.
  + (* no expansion *)
    applydup eqlistA_length in Hz. autorewrite with list in Hz0.
    apply liftRBTeqlist in Hz.
    exrepnd. subst. autorewrite with list in Hz0.
    eapply eval_Con_e_zeta in Hind; eauto.
    exrepnd. subst. rewrite Hz0. autorewrite with list.
    unfold  L4_5_Term in *.
    exists (Con_e d vsp). split; [eapply eval_Con_e; eauto | ];[].
    unfold Con_e. replace  (length vs) with  (length vsp) by congruence.
    apply zetao. apply liftRbt_eqlista. assumption.
  + apply (f_equal (map (get_nt))) in H3. repeat rewrite map_map in H3.
    simpl in H3. repeat rewrite map_id in H3. subst.
    applydup eqlistA_length in Hz. setoid_rewrite  Hz0. pose proof Hind as Hindb.
    eapply eval_Con_e_zeta in Hind; eauto.
    exrepnd. subst.  unfold  L4_5_Term in *.
    exists (Con_e d vsp). split;
                       [ |     unfold Con_e; replace  (length vs) with  (length vsp) by congruence;
                               apply zetao; apply liftRbt_eqlista; assumption].
    apply eval_letbindc;[ | | constructor; auto];[ | ]; hnf;[ rwsimplC | ];
      eapply zetalFvarsNil; eauto; intros ? Hin;
        [eapply (combine_in_right _ _ vs es) in Hin
        |eapply (combine_in_left  _ _ es vs) in Hin]; try omega;
    exrepnd; apply Hindb in Hin0; tauto.
Abort.

Lemma L4_5_constr_vars_zeta fv:
  (forall f, nt_wf f -> zetaCLe fv f (L4_5_constr_vars fv f)) *
  (forall f, bt_wf f -> liftRBt (zetaCLe fv) f (btMapNt (L4_5_constr_vars fv) f)).
Proof using.
  apply NTerm_BTerm_ind; [constructor | | ].
- intros ? ? Hind Hwf. simpl.
  cases_if as Hd.
  + ntwfauto. destruct o; inverts Hd.
    simpl in HntwfSig.
    apply map0lbt2 in HntwfSig.
    rewrite HntwfSig.
    remember (map get_nt lbt) as lnt.
    clear Heqlnt. subst.
    constructor.
    repeat rewrite map_map. simpl.
    rewrite <- (map_id lnt) at 1.
    apply eqListA_map with (Ra := eq); [ | reflexivity].
    intros. subst.
    specialize (Hind (bterm [] a2)
                     ltac:(apply in_map_iff; eauto)).
    specialize (Hntwf (bterm [] a2) ltac:(apply in_map_iff; eauto)).
    specialize (Hind Hntwf). inverts Hind. assumption.
  + constructor.
    rewrite <- (map_id lbt) at 1.
    apply eqListA_map with (Ra := eq); [ | reflexivity].
    intros. subst. eapply Hind; eauto.
    ntwfauto.
- intros ? ? Hind Hwf. constructor.
  apply Hind. ntwfauto.
Qed.

End L4_5_postproc.
End evaln42_45.

Ltac dZeta := match goal with
  [H:  SetoidList.eqlistA (liftRBt (zetaCLe _)) (cons _ _) _ |- _ ]
   =>  let Hr := fresh H "r" in inverts H as H Hr
| [H:  SetoidList.eqlistA (liftRBt (zetaCLe _)) [] _ |- _ ]
   =>  invertsn H
| [H:  liftRBt (zetaCLe _) (bterm _ _) _ |- _ ]
   =>  invertsn H
| [H:  zetaCLe _ (oterm _ _) _ |- _ ]
   =>  invertsn H
    end.
