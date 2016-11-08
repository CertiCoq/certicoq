Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L2.L2.
Require Import L2_5.compile.
Require Import L2_5.term.
Require Import L2_5.program.
Require Import L2_5.wndEval.
Require Import L2_5.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Defs := L2.compile.Defs.
Definition strip := L2Term_Term.
Definition strips := L2Terms_Terms.
Definition stripDs := L2Defs_Defs.
Definition stripEnv := L2Env_Env.
Definition stripEc := L2EC_EC.

Definition optStrip (t:option L2Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L2Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option (L2Term * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP
           (b: option (nat * L2Terms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, strips t, m)
                           end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, strips y, m).
induction y; simpl; reflexivity.
Qed.
                              
Print L2Env.
Lemma Lookup_hom:
  forall (p:environ L2.compile.Term) s ec, Lookup s p ec -> Lookup s (L2Env_Env p) (L2EC_EC ec).
Proof.
  induction 1; destruct t.
  - change (Lookup s ((s, ecTrm (strip t)) :: (L2Env_Env p))
                   (ecTrm (strip t))).
    apply LHit.
  - cbn. apply LHit.
  - change (Lookup s2 ((s1, ecTrm (strip t)) :: (L2Env_Env p))
                   (L2EC_EC ec)).
    apply LMiss; assumption.
  - cbn. apply LMiss; assumption.
Qed.

Lemma LookupDfn_hom:
 forall p s t, LookupDfn s p t -> LookupDfn s (stripEnv p) (strip t).
unfold LookupDfn. intros.
assert (j:= Lookup_hom H). exact j.
Qed.

Lemma dlength_hom:
  forall ds, L2.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L2.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm bod rarg ds,
    stripDs (L2.compile.dcons nm bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L2.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L2.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.
