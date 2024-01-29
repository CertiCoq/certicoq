
From MetaCoq Require Export Template.Ast.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.

Require Import Common.exceptionMonad.
Require Import Common.RandyPrelude.
Require Import Common.classes.
Require Import Common.AstCommon.
Require Import Common.references.
From compcert Require Import Maps.

(** We translate to a more efficient representations of environment references *)
Definition reference := positive.
Definition indreference : Set := reference * nat (* N ? *).
Definition string_of_ref := StringPos.string_of_pos.

(** An environ is a map from identifiers to definitions. **)
Section environ.
  Context {trm : Set}.
  Variable trm_dec: forall (s t:trm), s = t \/ s <> t.

  Definition environ := PTree.t (envClass trm).
  Record Program : Type := mkPgm { main:trm; env:environ }.
  
  (* for debugging *)
  Fixpoint print_environ (e:environ) : string :=
    (PTree.xfold
      (fun s k ec => "(envcons " ++ StringPos.string_of_pos k ++ (print_ec ec) ++ ")" ++ s)
      xH e "(envnil)")%string.

  Definition empty_environ : environ := PTree.empty _.

  Definition define (k : string) (v : envClass trm) (e : environ) : environ :=
    PTree.set (StringPos.string_to_pos k) v e.
  Definition lookup (k : reference) (e : environ) := PTree.get k e.
  Definition lookup_string (k : string) (e : environ) :=
    PTree.get (StringPos.string_to_pos k) e.
  
  (** environments are finite functions **)
  Definition fresh nm e := lookup nm e = None.
  
  (* Inductive fresh (nm:string) : environ -> Prop := *)
  (* | fcons: forall s p ec, *)
  (*     fresh nm p -> nm <> s -> fresh nm (define p s ec) *)
  (* | fnil: fresh nm empty_environ. *)
  (* Hint Constructors fresh. *)

  (*
  Lemma fresh_dec: forall nm p, (fresh nm p) \/ ~(fresh nm p).
  Proof.
    intros nm. 
    induction p.
    - left. auto.
    - destruct a. destruct IHp. destruct (string_dec nm s).
      + subst. right. intros h. inversion_Clear h. nreflexivity H4.
      + left. constructor; auto.
      + right. intros h. elim H. inversion_Clear h. assumption.
  Qed.

Lemma fresh_tl: forall nm p, fresh nm p -> fresh nm (tl p).
induction 1.
- simpl. assumption.
- auto.
Qed.

Lemma fresh_strengthen:
  forall rs qs nm, fresh nm (rs++qs) -> fresh nm qs.
induction rs; intros qs nm h.
- assumption.
- inversion h. subst. auto.
Qed.

Lemma fresh_not_head:
  forall nm t p nmtp, fresh nm nmtp -> nmtp = ((nm,t)::p) -> False.
induction 1; intros h.
- inversion h. subst. auto.
- discriminate h.
Qed.
*)

(** looking a name up in an environment **)
(** Hack: we code axioms in the environment as ecTyp with itypPack = nil **)
Inductive Lookup: string -> environ -> envClass trm -> Prop :=
| LHit: forall s p t, Lookup s (define s t p) t
| LMiss: forall s1 s2 p t ec,
           s2 <> s1 -> Lookup s2 p ec -> Lookup s2 (define s1 t p) ec.
#[global] Hint Constructors Lookup : core.
Definition LookupDfn s p t := Lookup s p (ecTrm t).
Definition LookupTyp s p n i := Lookup s p (ecTyp trm n i) /\ i <> nil.
Definition LookupAx s p := Lookup s p (ecAx trm).

(** equivalent lookup functions **)

Definition lookupDfn (nm:reference) (p:environ) : exception trm :=
  match lookup nm p with
    | Some (ecTrm t) => ret t
    | _ => raise ("lookupDfn; fails on " ++ string_of_ref nm)
  end.

Definition lookupTyp (nm:reference) (p:environ) : exception (nat * itypPack) :=
  match lookup nm p with
    | Some (ecTyp n ((cons _ _) as t)) => Ret (n, t)
    | _ => raise ("lookupTyp; fails on " ++ string_of_ref nm)
  end.

Import PTree.
Lemma Lookup_lookup:
  forall nm p t, Lookup nm p t -> lookup_string nm p = Some t.
induction 1; intros; subst; unfold lookup_string, define; simpl.
- now rewrite gss. 
- rewrite gso; auto. intro Hi; now apply StringPos.index_inj in Hi.
Qed.
(*
Lemma lookup_Lookup:
  forall nm p t, lookup nm p = Some t -> Lookup nm p t.
Proof.
  unfold lookup; intros.
  revert nm H.
  apply (PTree_Properties.fold_rec
           (fun a k v => define k v a)
           (fun t c => forall nm, t ! (StringPos.string_to_pos nm) = Some c -> Lookup nm t c) t0).
  intros.
  admit. admit.
  
  simpl in l.
  unfol
  
induction p; intros t h. inversion h.
destruct a. destruct (string_dec nm s); simpl in h.
- subst. rewrite (string_eq_bool_rfl s) in h.
  injection h. intros; subst. apply LHit.
- apply LMiss. assumption. apply IHp.
  rewrite (string_eq_bool_neq n) in h. assumption.
Qed.

Lemma not_lookup_not_Lookup:
 forall (nm:string) (p:environ) (ec:envClass),
   ~(lookup nm p = Some ec) <-> ~(Lookup nm p ec).
split; eapply deMorgan_impl.
- apply (Lookup_lookup).
- apply (lookup_Lookup).
Qed.

Lemma LookupDfn_lookupDfn:
  forall nm p t, Lookup nm p t ->
                 forall te, t = (ecTrm te) -> lookupDfn nm p = Ret te.
  induction 1; intros; subst; unfold lookupDfn, lookup.
- rewrite (string_eq_bool_rfl s). reflexivity.
- rewrite (string_eq_bool_neq H). 
  destruct t; apply IHLookup; reflexivity.
Qed.

Lemma lookupDfn_LookupDfn:
  forall nm p t, lookupDfn nm p = Ret t -> Lookup nm p (ecTrm t).
Proof.
  intros nm p t. intros. apply lookup_Lookup.
  unfold lookupDfn in H. 
  case_eq (lookup nm p); intros; rewrite H0 in H.
  - destruct e.
    + myInjection H. reflexivity.
    + discriminate.
  - discriminate.
Qed.

Lemma Lookup_dec:
  forall s p, (exists t, Lookup s p t) \/ (forall t, ~ Lookup s p t).
Proof.
  induction p; intros.
  - right. intros t h. inversion h.
  - destruct IHp; destruct a; destruct (string_dec s s0); subst.
    + left. destruct H. exists e. apply LHit.
    + left. destruct H. exists x. apply LMiss; assumption.
    + destruct e.
      * left. exists (ecTrm t). apply LHit.
      * left. exists (ecTyp n i). apply LHit. 
    + right. intros t h. inversion_Clear h. 
      * elim n. reflexivity.
      * elim (H t). assumption.
Qed.

Lemma Lookup_fresh_neq:
  forall nm2 p t, Lookup nm2 p t -> forall nm1, fresh nm1 p -> nm1 <> nm2.
induction 1; intros.
- inversion H. assumption.
- apply IHLookup. apply (fresh_tl H1).
Qed.

Lemma fresh_Lookup_fails:
  forall nm p ec, fresh nm p -> ~(Lookup nm p ec).
induction 1; intro h; inversion h; subst; auto.
Qed.

Lemma fresh_lookup_None: forall nm p, fresh nm p <-> lookup nm p = None.
split. 
- induction 1; simpl; try reflexivity.
  + rewrite string_eq_bool_neq; assumption.
- induction p; auto.
  + destruct a. destruct (string_dec nm s). 
    * subst. simpl. rewrite string_eq_bool_rfl. discriminate.
    * simpl. rewrite string_eq_bool_neq; try assumption. intros h.
      apply fcons; intuition.
Qed.

Lemma Lookup_single_valued:
  forall (nm:string) (p:environ) (t r:envClass),
    Lookup nm p t -> Lookup nm p r -> t = r.
Proof.
  intros nm p t r h1 h2. 
  assert (j1:= Lookup_lookup h1).
  assert (j2:= Lookup_lookup h2).
  rewrite j1 in j2. myInjection j2. reflexivity. 
Qed.

Lemma LookupDfn_single_valued:
  forall (nm:string) (p:environ) (t r:trm),
    LookupDfn nm p t -> LookupDfn nm p r -> t = r.
Proof.
  unfold LookupDfn. intros nm p t r h1 h2.
  injection (Lookup_single_valued h1 h2). intuition.
Qed.

Lemma lookup_fresh_neq:
  forall nm2 p (ec:envClass),
    lookup nm2 p = Some ec -> forall nm1, fresh nm1 p -> nm1 <> nm2.
Proof.
  intros nm2 p ec. functional induction (lookup nm2 p); intros.
  - discriminate.
  - inversion_Clear H0. rewrite (string_eq_bool_eq _ _ e0). assumption.
  - inversion_Clear H0. specialize (IHo H _ H3). assumption.
Qed.

Lemma Lookup_weaken:
  forall s p t, Lookup s p t -> 
      forall nm ec, fresh nm p -> Lookup s ((nm, ec) :: p) t.
intros s p t h1 nm ec h2.
assert (j1:= Lookup_fresh_neq h1 h2). apply LMiss. apply neq_sym. assumption.
assumption.
Qed.

Lemma Lookup_weaken':
  forall s p t, Lookup s p t -> 
      forall nm ec, s <> nm -> Lookup s ((nm, ec) :: p) t.
intros s p t h1 nm ec h2. apply LMiss; assumption.
Qed.

Lemma lookup_weaken':
  forall s nm, s <> nm -> forall p ec, lookup s p = lookup s ((nm, ec) :: p).
Proof.
  intros s nm h1 p ec.
  change (lookup s p = if (string_eq_bool s nm) then Some ec
                       else lookup s p).
  rewrite string_eq_bool_neq. reflexivity. assumption.
Qed.

Lemma lookupDfn_weaken':
  forall s nm, s <> nm ->
               forall p ec, lookupDfn s p = lookupDfn s ((nm, ec) :: p).
Proof.
  intros s nm h1 p ec. unfold lookupDfn. erewrite lookup_weaken'.
  reflexivity. assumption.
Qed.

Lemma Lookup_strengthen:
  forall (nm1:string) pp t, Lookup nm1 pp t -> 
       forall nm2 ec p, pp = (nm2,ec)::p -> nm1 <> nm2 -> Lookup nm1 p t.
intros nm1 pp t h nm2 ecx px j1 j2. subst. assert (k:= Lookup_lookup h).
simpl in k. rewrite (string_eq_bool_neq j2) in k.
apply lookup_Lookup. assumption.
Qed.
*)

(** find an ityp in an itypPack **)
Definition getInd (ipkg:itypPack) (inum:nat) : exception ityp :=
  exnNth ipkg inum.

(** find a Cnstr in an ityp **)
Definition getCnstr (ip:ityp) (cnum:nat) : exception Cnstr :=
  exnNth (itypCnstrs ip) cnum.


(** total constructor arity (including parameters) is only computed
*** on the fly during translation from L2 to LambdaBoxMut **)
Definition cnstrArity (p:environ) (i:indreference) (cndx:nat) : exception nat :=
  match i with
    | pair nm tndx =>
      match lookupTyp nm p with
        | Exc str => raise ("cnstrArity; lookupTyp fails: " ++ str)
        | Ret (npars, itypkg) =>
          match getInd itypkg tndx with
            | Exc str => raise ("cnstrArity; getInd fails: " ++ str)
            | Ret ity => match getCnstr ity cndx with
                           | Exc str =>
                             raise ("cnstrArity; getCnstr fails: " ++ str)
                           | Ret itp => ret (npars + (CnstrArity itp))
                         end
          end
       end
  end.

End environ.

Arguments environ trm : clear implicits.
Arguments Program trm : clear implicits.
