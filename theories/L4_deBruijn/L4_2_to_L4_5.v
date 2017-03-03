Require Import L4.expression.
Require Import L4.variables.
Require Import polyEval.

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


Require Import Common.RandyPrelude.
Open Scope N_scope.
Require Import L4.L4_to_L4_1_to_L4_2.
Require Import L4.L4_5_to_L5. (* TODO: rename L4_2 to L4 *)
Require Import SquiggleEq.list.

(* Move. and replace in SquiggleEq.terms*)
Definition btMapNt {O O2 V} (f: @NTerm V O  -> @NTerm V O2)
   (b: @BTerm V O) : @BTerm V O2 :=
match b with
|bterm lv nt => bterm lv (f nt)
end.

Definition L4_5_Term :Type := (@NTerm NVar L4_5Opid).

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


Lemma L4_2_to_L4_5_correct n t v:
  let eval42 := @eval_n (Named.TermAbsImpl variables.NVar L4Opid) in
  (eval42 n t) = Some v
  -> eval (L4_2_to_L4_5 t) (L4_2_to_L4_5 v).
Proof using.
  intros ?.
  revert v.
  revert t.
  induction n; intros ? ? Hev;[inverts Hev; fail | destruct t as [vv | o lbt];[ | destruct o]].
- inverts Hev.
- (* in this case, need to constrain the shape of the bound terms of lambda in eval_n *) admit.
- admit.
- admit.
- (* apply *)
  simpl in Hev.
  destruct lbt as [ | bt1 lbt]; invertsn Hev.
  destruct lbt as [ | bt2 lbt]; invertsn Hev.
  destruct lbt as [ | ]; invertsn Hev.
  destruct bt2 as [lv arg].
  simpl in Hev.
  destruct lv; invertsn Hev.
  remember (eval42 n arg) as ea.
  symmetry in Heqea.
  destruct ea as [argv | invertsn Heq].
  destruct bt1 as [lv ff].
  simpl in Hev.
  destruct lv; invertsn Hev.
  remember (eval42 n ff) as ef.
  symmetry in Heqef.
  destruct ef as [ffv | invertsn Heq].
  destruct ffv as [? | fvo fvlbt]; [ | destruct fvo]; invertsn Hev.
  + (* lambda *) admit.
  + (* fix *) admit.
  + (* box *)
    destruct fvlbt; [ | invertsn Hev].
    simpl.
    apply IHn in Heqea.
    apply IHn in Heqef.
    eapply eval_FixApp_e; eauto;[reflexivity| | reflexivity].
    simpl. unfold apply_bterm. simpl.
    eapply eval_App_e; eauto;[apply eval_Lam_e | eapply eval_end; eauto| ].
    simpl.
    inverts Hev.
    simpl.
    (* if we revive the proof that eval preserves alpha equality, 
        then we can say that the substitution is a no-op upto alpha equality.
       boundvar renaming may happen if [argv] has [nvary] or [nvarx] free.
       We can also pick  [nvary] or [nvary] to be disjoint from user vars.
       
      Alternatively, because we are evaluating closed terms, we can assume that
      [t] is closed, which will imply that argv is closed.
     *)
    assert (closed argv) as Hca by admit.
    unfold subst.
    rewrite ssubst_trivial4; simpl; eauto; [ apply eval_Fix_e | ].
    intros ? ? Hin. rewrite or_false_r in Hin. inverts Hin.
    unfold closed in Hca.
  (* do a separate proof that L4_2_to_L4_5 preserves free variables *)
    admit.
  + (* box *) inverts Hev.
  + (* box *) inverts Hev.

- admit.
- admit.
- admit.
Admitted.
