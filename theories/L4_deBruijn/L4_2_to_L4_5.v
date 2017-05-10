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

Require Import SquiggleEq.alphaeq.

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

Let eval42 := @polyEval.eval_n (Named.TermAbsImpl variables.NVar L4Opid).
Let eval45 := @eval_n (Named.TermAbsImpl variables.NVar L4_5Opid).


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
- clear Hprb. simpl. revert Hev.
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
  destruct (eval42 n ant) as [av | ]; simpl in *;[ | invertsn Hev].
  destruct (eval42 n fnt) as [fv | ]; simpl in *;[ | invertsn Hev].
  specialize (Hindf _ eq_refl).
  specialize (Hinda _ eq_refl).
  destruct fv as [ |fvo fvlbt]; [ invertsn Hev| ].
  destruct Hindf as [Hprfe Hindf].
  destruct Hinda as [Hprae Hinda].
  apply isprogram_ot_iff in Hprfe. repnd.
  simpl in *. destruct fvo;  simpl in *; try  invertsn Hev.
  (* Lambda *)
  + simpl; destruct fvlbt as [ | f fvlbt]; simpl; try invertsn Hev;[].
    simpl; destruct fvlbt as [ | ff fvlbt]; simpl; try invertsn Hev ;[].
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
  + revert Hev.
    unfold Named.mkBTermSafe. simpl. repeat rewrite map_map.
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
  + destruct fvlbt; inverts Hprfe0.
    simpl. unfold apply_bterm. simpl. unfold Lam_e. simpl.
    inverts Hev. simpl.
    split; [ apply isprogram_ot_iff; simpl; firstorder | ].
    eapply eval_FixApp_e; eauto;[reflexivity| | reflexivity].
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

End evaln42_45.

