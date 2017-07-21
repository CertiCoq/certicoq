
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import omega.Omega.
Require Import Recdef.
Require Import Common.Common.
Require L2_5.compile.
Require L2_5.term.
Require L2_5.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2_5Term := L2_5.compile.Term.
Definition L2_5Terms := L2_5.compile.Terms.
Definition L2_5Brs := L2_5.compile.Brs.
Definition L2_5Defs := L2_5.compile.Defs.
Definition L2_5EC := envClass L2_5Term.
Definition L2_5Env := environ L2_5Term.
Definition L2_5Pgm := Program L2_5Term.


Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term 
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term -> Term
| TConst     : string -> Term
| TConstruct : inductive -> nat (* index *) -> Terms -> Term
| TCase      : inductive ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong : Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Brs : Type :=
| bnil : Brs
| bcons : nat -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs. 
Hint Constructors Term Terms Brs Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind
         from Trm_ind', Trms_ind', Brs_ind', Defs_ind'.
Notation tunit t := (tcons t tnil).
Notation dunit nm t m := (dcons nm t m dnil).
Notation bunit t m := (bcons t m dnil).


Definition isConstruct (t:Term) : Prop :=
  exists i n ts, t = TConstruct i n ts.
Lemma IsConstruct: forall i n ts, isConstruct (TConstruct i n ts).
intros. exists i, n, ts. reflexivity.
Qed.
Hint Resolve IsConstruct.

Function tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Lemma tlength_S:
  forall ts p,
    tlength ts > p ->
    exists u us, ts = tcons u us /\ tlength us >= p.
Proof.
  induction ts; intros.
  - cbn in H. omega.
  - cbn in H. case_eq ts; intros; subst.
    + exists t, tnil. auto. cbn in H. assert (j:p = 0). omega. subst.
      intuition.
    + exists t, (tcons t0 t1). intuition.
Qed.
    
Fixpoint tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
Proof.
  induction ts; simpl; try reflexivity.
  rewrite IHts. reflexivity.
Qed.

Lemma tappend_assoc:
  forall xts yts zts,
       (tappend xts (tappend yts zts)) = (tappend (tappend xts yts) zts).
  induction xts; intros yts zts; simpl.
  - reflexivity.
  - rewrite IHxts. reflexivity.
Qed.

Lemma tappend_pres_tlength:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

(** return n (or as many as possible) from front of ts **)
Fixpoint ttake (ts:Terms) (n:nat) : Terms :=
  match ts with
    | tnil => tnil
    | (tcons u us) as uus =>
      match n with
        | 0 => uus
        | S n => ttake us n
      end
  end.

Fixpoint treverse (ts: Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons b bs => tappend (treverse bs) (tunit b)
  end.

Lemma treverse_tappend_distr:
  forall x y:Terms,
    treverse (tappend x y) = tappend (treverse y) (treverse x).
Proof.
  induction x as [| a l IHl]; cbn; intros.
  - destruct y as [| a l]; cbn. reflexivity.
    rewrite tappend_tnil. reflexivity.
  - rewrite (IHl y). rewrite tappend_assoc. reflexivity.
Qed.

Remark treverse_tunit:
  forall (l:Terms) (a:Term),
    treverse (tappend l (tunit a)) = tcons a (treverse l).
Proof.
  intros.
  apply (treverse_tappend_distr l (tunit a)); simpl; auto.
Qed.

Lemma treverse_involutive:
  forall ts:Terms, treverse (treverse ts) = ts.
Proof.
  induction ts as [| a l IHl]; cbn; intros. reflexivity.
  - rewrite treverse_tunit. rewrite IHl. reflexivity.
Qed.
   
Remark tunit_treverse:
    forall (l:Terms) (a:Term),
    tappend (treverse l) (tunit a) = treverse (tcons a l).
Proof.
  intros. cbn. reflexivity.
Qed.

Lemma treverse_pres_tlength:
  forall ts, tlength ts = tlength (treverse ts).
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. rewrite tappend_pres_tlength. cbn. omega.
Qed.

Lemma tcons_has_last:
  forall ts t, exists us u, tcons t ts = tappend us (tunit u).
Proof.
  induction ts; intros; cbn.
  - exists tnil, t. reflexivity.
  - destruct (IHts t) as [x0 [x1 jx]]. rewrite jx.
    exists (tcons t0 x0), x1. cbn. reflexivity.
Qed.
  
Function tfirsts_tlast (t:Term) (ts:Terms) : Terms * Term :=
  match ts with
    | tnil => (tnil, t)
    | tcons u tnil => (tunit t, u)
    | tcons v (tcons u us) =>
      let xsx := tfirsts_tlast u us in
      (tcons t (tcons v (fst xsx)), (snd xsx))
  end.

Lemma tfirsts_tlast_pres_tlength:  
  forall t ts, tlength (fst (tfirsts_tlast t ts)) = tlength ts.
Proof.
  intros t ts. functional induction (tfirsts_tlast t ts); try reflexivity.
  - cbn. rewrite <- IHp. reflexivity.
Qed.

Lemma tfirsts_tlast_spec:
  forall t ts,
    tcons t ts = let xsx := tfirsts_tlast t ts in
                 tappend (fst xsx) (tunit (snd xsx)).
Proof.
  intros t ts. functional induction (tfirsts_tlast t ts); try reflexivity.
  - rewrite IHp. reflexivity.
Qed.
  
Lemma tfirsts_tlast_tnil_tnil:
  forall ys y, fst (tfirsts_tlast y ys) = tnil -> ys = tnil.
Proof.
  induction ys; intros. reflexivity.
  - destruct ys; discriminate.
Qed.

Lemma tfirsts_tlast_tnil_y:
  forall ys y, fst (tfirsts_tlast y ys) = tnil ->
               snd (tfirsts_tlast y ys) = y.
Proof.
  induction ys; intros. reflexivity.
  - destruct ys; discriminate.
Qed.

Lemma tfirsts_tlast_tcons_last:
  forall t t' u us, snd (tfirsts_tlast t (tcons u us)) =
                    snd (tfirsts_tlast t' (tcons u us)).
Proof.
  induction us; intros; cbn; reflexivity.
Qed.

Lemma tfirsts_tlast_tcons:
  forall t u us,
  exists v vs z, tfirsts_tlast t (tcons u us) = (tcons v vs, z).
Proof.
  induction us; intros.
  - exists t, tnil, u. reflexivity.
  - destruct IHus as [x0 [x1 [x2 j]]].
    exists t,
    (tcons u (fst (tfirsts_tlast t0 us))), (snd (tfirsts_tlast t0 us)).
    reflexivity.
Qed.

Inductive Tfirsts_tlast : Term -> Terms -> Terms -> Term -> Prop :=
| Tflnil: forall t, Tfirsts_tlast t tnil tnil t
| Tflc1: forall t u, Tfirsts_tlast t (tcons u tnil) (tunit t) u
| Tflc2: forall t v u us xs x,
           Tfirsts_tlast u us xs x ->
           Tfirsts_tlast t (tcons v (tcons u us)) (tcons t (tcons v xs)) x.

Goal
  forall t ts xs x,
    Tfirsts_tlast t ts xs x -> tlength ts = tlength xs.
Proof.
  induction 1; try reflexivity.
  - cbn. rewrite IHTfirsts_tlast. reflexivity.
Qed.


Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.

Fixpoint blength (ts:Brs) : nat :=
  match ts with 
    | bnil => 0
    | bcons _ _ ts => S (blength ts)
  end.

(** lift a Term over a new binding **)
Fixpoint lift (n:nat) (t:Term) : Term :=
  match t with
    | TRel m => TRel (match m ?= n with
                        | Lt => m
                        | _ => S m
                      end)
    | TLambda nm bod => TLambda nm (lift (S n) bod)
    | TLetIn nm df bod => TLetIn nm (lift n df) (lift (S n) bod)
    | TApp fn arg => TApp (lift n fn) (lift n arg)
    | TConstruct i x args => TConstruct i x (lifts n args)
    | TCase iparsapb mch brs => TCase iparsapb (lift n mch) (liftBs n brs)
    | TFix ds y => TFix (liftDs (n + dlength ds) ds) y
    | _ => t
  end
with lifts (n:nat) (ts:Terms) : Terms :=
       match ts with
         | tnil => tnil
         | tcons u us => tcons (lift n u) (lifts n us)
       end
with liftBs (n:nat) (ts:Brs) : Brs :=
       match ts with
         | bnil => bnil
         | bcons m u us => bcons m (lift n u) (liftBs n us)
       end
with liftDs n (ds:Defs) : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm u j es => dcons nm (lift n u) j (liftDs n es)
       end.

Lemma lifts_pres_tlength:
  forall n ts, tlength (lifts n ts) = tlength ts.
Proof.
  induction ts.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma liftDs_pres_dlength:
  forall n ds, dlength (liftDs n ds) = dlength ds.
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma liftBs_pres_blength:
  forall n ds, blength (liftBs n ds) = blength ds.
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma tappend_pres_lifts:
  forall ts ss n, lifts n (tappend ts ss) = tappend (lifts n ts) (lifts n ss).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.
  
Lemma treverse_pres_lifts:
  forall ts n, lifts n (treverse ts) = treverse (lifts n ts).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite <- IHts. rewrite tappend_pres_lifts.
    reflexivity.
Qed.
  

(** turn (Construct [x1;...;xn; 0;...k-1]])  with arity n+k into
*** (Lam ... (Lam (Construct [x1;...;xn; 0;...k-1])...))
*** lift [x1;...;xn] k times,
*** then append the k fresh variables and surround with k lambdas
**)
Fixpoint mkEtaLams (xtraArity:nat) i x args : Term :=
  match xtraArity with
    | 0 => TConstruct i x args
    | S n => TLambda nAnon (mkEtaLams n i x args)
  end.

Fixpoint mkEtaArgs k args: Terms :=
  match k with
    | 0 => treverse args
    | S n => mkEtaArgs n (tcons (TRel 0) (lifts 0 args))
  end.
  
(** If there are extra args (more than arity, which cannot happen in
*** a program checked by Coq) we just truncate them,
*** and no eta expansion is required 
**)
Definition etaExp_cnstr (i:inductive) (x xtra:nat) (args:Terms) : Term :=
   mkEtaLams xtra i x (mkEtaArgs xtra (treverse args)).

Lemma etaExp_cnstr_0:
  forall (args:Terms) (i:inductive) (n:nat),
    etaExp_cnstr i n 0 args = TConstruct i n args.
Proof. 
  intros. cbn. rewrite treverse_involutive. reflexivity.
Qed.

Lemma etaExp_cnstr_S:
  forall (xtra:nat) (args:Terms) (i:inductive) (x:nat),
    etaExp_cnstr i x (S xtra) args =
    TLambda nAnon
            (mkEtaLams
               xtra i x (mkEtaArgs xtra (tcons (TRel 0)
                                               (lifts 0 (treverse args))))).
Proof.
  reflexivity.
Qed.

Lemma etaExp_cnstr_S':
  forall (xtra:nat) (args:Terms) (i:inductive) (x:nat),
    mkEtaLams (S xtra) i x (mkEtaArgs (S xtra) args) =
    TLambda nAnon
            (mkEtaLams
               xtra i x (mkEtaArgs xtra (tcons (TRel 0) (lifts 0 args)))).
Proof.
  reflexivity.
Qed.

Lemma etaExp_cnstr_tnil:
  forall (i:inductive) (n xtra:nat),
    etaExp_cnstr i n xtra tnil =
    mkEtaLams xtra i n (mkEtaArgs xtra tnil).
Proof.
  reflexivity. 
Qed.

Lemma etaExp_cnstr_tcons:
  forall (xtra:nat) (i:inductive) (n:nat) t ts,
    etaExp_cnstr i n xtra (tcons t ts) =
    mkEtaLams xtra i n (mkEtaArgs xtra (tappend (treverse ts) (tunit t))).
Proof.
  induction xtra; intros.
  - rewrite etaExp_cnstr_0. unfold mkEtaLams, mkEtaArgs.
    rewrite treverse_tunit. rewrite treverse_involutive. reflexivity.
  - rewrite tunit_treverse. reflexivity.
Qed.

Lemma etaExp_cnstr_Lam_or_Cnstr':
  forall i n xtra ts,
    (exists ytra, xtra = S ytra /\
                     etaExp_cnstr i n xtra ts =
                     TLambda nAnon (mkEtaLams ytra i n
                      (mkEtaArgs ytra
                        (tcons (TRel 0) (lifts 0 (treverse ts)))))) \/
    (exists us, xtra = 0 /\ etaExp_cnstr i n xtra ts = TConstruct i n us).
Proof.
  destruct xtra; intros; unfold etaExp_cnstr; cbn.
  - right. exists ts. rewrite treverse_involutive. intuition. 
  - left. exists xtra. intuition.
Qed.

Lemma etaExp_cnstr_Lam_or_Cnstr:
  forall i n xtra ts,
    (exists bod, etaExp_cnstr i n xtra ts = TLambda nAnon bod) \/
    (exists us, etaExp_cnstr i n xtra ts = TConstruct i n us).
Proof.
    destruct xtra; intros; unfold etaExp_cnstr; cbn.
  - right. exists ts. rewrite treverse_involutive. reflexivity.
  - left.
    exists
    (mkEtaLams xtra i n
               (mkEtaArgs xtra (tcons (TRel 0) (lifts 0 (treverse ts))))).
    reflexivity.
Qed.

(** turn (App fn [x1;...;xn]) into (App (... (App fn x1) x2 ...) xn) **)
Function mkApp (fn:Term) (ts:Terms) : Term :=
  match ts with
    | tnil => fn
    | tcons y ys => mkApp (TApp fn y) ys
  end.

Lemma mkApp_idempotent:
  forall ts (fn:Term) (ss:Terms),
    mkApp (mkApp fn ts) ss = mkApp fn (tappend ts ss).
Proof.
  induction ts; destruct fn; intros; cbn; try reflexivity;
  try rewrite <- IHts; try reflexivity.
Qed.                                                       
  
Lemma mkApp_tnil: forall fn, mkApp fn tnil = fn.
  intros. reflexivity.
Qed.

Lemma mkApp_cons:
  forall fn u us, mkApp fn (tcons u us) = mkApp (TApp fn u) us.
Proof.
  intros. reflexivity.
Qed.

Lemma mkApp_out:
  forall ts fn u,
    mkApp fn (tappend ts (tunit u)) = TApp (mkApp fn ts) u.
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.


Function strip (t:L2_5Term) : Term :=
  match t with
    | L2_5.compile.TProof => TProof
    | L2_5.compile.TRel n => (TRel n)
    | L2_5.compile.TCast s => strip s
    | L2_5.compile.TLambda nm bod => TLambda nm (strip bod)
    | L2_5.compile.TLetIn nm dfn bod => TLetIn nm (strip dfn) (strip bod)
    | L2_5.compile.TApp fn arg args =>
      mkApp (TApp (strip fn) (strip arg)) (strips args)
    | L2_5.compile.TConst nm => TConst nm
    | L2_5.compile.TConstruct i n args => TConstruct i n (strips args)
    | L2_5.compile.TCase n mch brs => TCase n (strip mch) (stripBs brs)
    | L2_5.compile.TFix ds n => TFix (stripDs ds) n
    | L2_5.compile.TWrong => TWrong
   end
with strips (ts:L2_5Terms) : Terms := 
  match ts with
    | L2_5.compile.tnil => tnil
    | L2_5.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripBs (ts:L2_5Brs) : Brs := 
  match ts with
  | L2_5.compile.bnil => bnil
  | L2_5.compile.bcons n t ts => bcons n (strip t) (stripBs ts)
  end
with stripDs (ts:L2_5Defs) : Defs := 
  match ts with
    | L2_5.compile.dnil => dnil
    | L2_5.compile.dcons nm t m ds => dcons nm (strip t) m (stripDs ds)
  end.
Functional Scheme strip_ind' := Induction for strip Sort Prop
with strips_ind' := Induction for strips Sort Prop
with stripBs_ind' := Induction for stripBs Sort Prop
with stripDs_ind' := Induction for stripDs Sort Prop.
(*** Anomaly: Uncaught exception Term.DestKO. Please report. ***
Combined Scheme stripStripsStripDs_ind
         from strip_ind', strips_ind', stripDs_ind'.
***)

Lemma strips_pres_tlength:
  forall ts:L2_5Terms,
  tlength (strips ts) = L2_5.term.tlength ts.
Proof.
  induction ts. reflexivity.
  cbn. rewrite IHts. reflexivity.
Qed.
  
Lemma stripDs_pres_dlength:
  forall ds:L2_5Defs,
  dlength (stripDs ds) = L2_5.compile.dlength ds.
Proof.
  induction ds. reflexivity.
  cbn. rewrite IHds. reflexivity.
Qed.
  
Lemma tappend_hom:
  forall ts us,
    strips (L2_5.compile.tappend ts us) = tappend (strips ts) (strips us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  rewrite IHts. reflexivity.
Qed.


(**********
Lemma isL2_5Cnstr_TApp_None:
  forall fn t ts, isL2_5Cnstr (L2_5.compile.TApp fn t ts) = None.
Proof.
  intros. reflexivity.
Qed.

Lemma strip_TAppTConstruct:
  forall i n arty arg args,
    strip (L2_5.compile.TApp (L2_5.compile.TConstruct i n arty) arg args) =
    etaExp_cnstr i n (arty - S (tlength (strips args)))
                 (tcons (strip arg) (strips args)).
Proof.
  intros. reflexivity.
Qed.

Lemma isL2_5Cnstr_Some:
  forall t i cn arty,
    isL2_5Cnstr t = Some (i, cn, arty) -> strip t = etaExp_cnstr i cn arty tnil.
Proof.
  induction t; intros; subst; cbn in H; try discriminate.
  - rewrite <- IHt. reflexivity. assumption.
  - myInjection H. reflexivity.
Qed.

Lemma stripApp_notCnstr:
  forall t fn s, strip t = TApp fn s -> isL2_5Cnstr t = None.
Proof.
  induction t; intros; cbn; try reflexivity.
  - eapply IHt. cbn in H. eassumption.
  - cbn in H. destruct (@etaExp_cnstr_Lam_or_Cnstr i n n0 tnil).
    + destruct H0 as [x0 j]. rewrite j in H. discriminate.
    + destruct H0 as [x0 j]. rewrite j in H. discriminate.
Qed.
  
Lemma stripAppApp_notCnstr:
  forall y0 y1 y2 fn s,
    strip (L2_5.compile.TApp y0 y1 y2) = TApp fn s -> isL2_5Cnstr y0 = None.
Proof.
  induction y0; intros; cbn; try reflexivity.
  - simpl in H. case_eq (isL2_5Cnstr y0); intros; try reflexivity.
    destruct p, p. rewrite H0 in H.
    destruct (@etaExp_cnstr_Lam_or_Cnstr
                i n0 (n - S (tlength (strips y2)))
                (tcons (strip y1) (strips y2))).
    + destruct H1 as [x0 j]. rewrite j in H. discriminate.
    + destruct H1 as [x0 j]. rewrite j in H. discriminate.
  - simpl in H.
    destruct (@etaExp_cnstr_Lam_or_Cnstr
                i n (n0 - S (tlength (strips y2)))
                (tcons (strip y1) (strips y2))).
    + destruct H0 as [x0 j]. rewrite j in H. discriminate.
    + destruct H0 as [x0 j]. rewrite j in H. discriminate.
Qed.

Lemma isL2_5Cnstr_None:
  forall t, isL2_5Cnstr t = None -> ~ L2_5.term.isConstruct t.
Proof.
  intros.
  destruct t; intros h; destruct h as [x0 [x1 [x2 j]]]; try discriminate.
Qed.

Lemma isL2_5Cnstr_Some_strip:
  forall u i x arty,
    isL2_5Cnstr u = Some (i, x, arty) ->
    strip u = strip (L2_5.compile.TConstruct i x arty).
Proof.
  induction u; cbn; intros; try discriminate.
  - rewrite (IHu _ _ _ H). reflexivity.
  - myInjection H. reflexivity.
Qed.
                                         
Lemma TFix_hom:
  forall defs n,
    strip (L2_5.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm bod,
    strip (L2_5.compile.TProd nm bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm bod,
    strip (L2_5.compile.TLambda nm bod)  = TLambda nm (strip bod).
Proof.
  reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn bod,
    strip (L2_5.compile.TLetIn nm dfn bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n mch brs,
    strip (L2_5.compile.TCase n mch brs) =
    TCase n (strip mch) (stripDs brs).
reflexivity.
Qed.

Lemma TConstruct_hom:
  forall i n arty,
    strip (L2_5.compile.TConstruct i n arty) = etaExp_cnstr i n arty tnil.
Proof.
  reflexivity.  
Qed.

Lemma TInd_hom:
  forall i,
        strip (L2_5.compile.TInd i) = (TInd i).
Proof.
  reflexivity.
Qed.

Lemma dlength_hom:
  forall ds, L2_5.compile.dlength ds = dlength (stripDs ds).
induction ds. intuition. cbn. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2_5.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm t m ds,
    stripDs (L2_5.compile.dcons nm t m ds) = dcons nm (strip t) m (stripDs ds).
reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L2_5.compile.TApp fn arg args) =
    match isL2_5Cnstr fn with
      | Some (i, n, arty) =>
        etaExp_cnstr i n (arty - S (tlength (strips args)))
                     (tcons (strip arg) (strips args))
      | None => mkApp (strip fn) (tcons (strip arg) (strips args))
    end.
Proof.
  intros. case_eq fn; intros; try reflexivity.
Qed.
 ***********)



Function stripEC (ec:L2_5EC) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp _ n itp
  end.


Function stripEnv (p:L2_5Env) : environ Term :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, stripEC ec) (stripEnv q)
  end.

Definition stripProgram (p:L2_5Pgm) : AstCommon.Program Term :=
  {| env:= stripEnv (env p); main:= strip (AstCommon.main p) |}.


(** L1-to-L3 translations **)
Definition program_Program (p:program) : Program Term :=
  stripProgram (L2_5.compile.program_Program p).

(*******************
Definition term_Term' (e:L2_5.compile.environ) (t:term) : Term  :=
  strip e (L2_5.compile.term_Term t).
************************)
