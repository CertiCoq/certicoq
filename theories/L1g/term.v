
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.omega.Omega.
Require Export Common.Common.
Require Export L1.term.
Require Export L1g.compile.

Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.

Definition thd_tl ts t us: (Term * Terms) :=
  match ts with
    | tnil => (t, us)
    | tcons v vs => (v, tappend vs (tcons t us))
  end.

(** Printing terms in exceptions for debugging purposes **)
Definition print_name nm : string :=
  match nm with
  | nAnon => " _ "
  | nNamed str => str
  end.
Definition print_inductive i : string :=
  match i with
  | mkInd str n => "str"
  end.
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => "(" ++ (nat_to_string n) ++ ")"
    | TSort _ => " SRT "
    | TProof tm => "(PRF" ++ (print_term tm) ++ ")"
    | TCast _ _ => " CAST "
    | TProd _ _ _ => " PROD "
    | TLambda _ _ _ => " LAM "
    | TLetIn nm _ dfn bod =>
      (" LET " ++ (print_name nm) ++ (print_term dfn) ++ (print_term bod))
    | TApp fn arg args =>
      "(APP" ++ (print_term fn) ++ (print_term arg) ++ " _ " ++ ")"
    | TConst s => "[" ++ s ++ "]"
    | TInd _ => " TIND "
    | TConstruct i _ _ _ => "(CSTR " ++ (print_inductive i) ++")"
    | TCase n _ mch _ =>
      "(CASE " ++ (nat_to_string (snd n)) ++ " _ " ++ (print_term mch) ++
                 " _ " ++")"
    | TFix _ n => "(FIX " ++ (nat_to_string n) ++ ")"
    | TAx s => "(Ax " ++ s ++")"
    | TWrong str => (" Wrong " ++ str )
  end.


Ltac not_is1 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j" in
  intros hh; destruct hh as [xx jj]; discriminate.
Ltac not_is2 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.
Ltac not_is3 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with zz := fresh "z" in
  intros hh; destruct hh as [xx [yy [zz jj]]]; discriminate.

Ltac not_isApp := not_is3.
Ltac not_isLambda := not_is3.
Ltac not_isProof := not_is1.            

Ltac isApp :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with kk := fresh "k"
  with zz := fresh "z"
  with ll := fresh "l" in
  intros hh; destruct hh as [xx jj]; destruct jj as [yy kk];
             destruct kk as [zz ll].


Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (ss tt:Terms), ss = tt \/ ss <> tt) /\
  (forall (bb cc:Brs), bb = cc \/ bb <> cc) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsBrsDefs_ind; intros.
  - Case "TRel". destruct t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - Case "TSort". destruct t; cross. destruct (Srt_dec s s0); [lft | rght].
  - destruct t0; cross. destruct (H t0); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (name_dec n n0);
      destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (name_dec n n0);
      destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t2; cross.
    destruct (name_dec n n0);
      destruct (H t2_1); destruct (H0 t2_2); destruct (H1 t2_3); 
      [lft | rght ..]. 
  - destruct t2; cross.
    destruct (H t2_1); destruct (H0 t2_2); destruct (H1 t2); [lft | rght ..].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t; cross. destruct (inductive_dec i i0); [lft | rght].
  - destruct t; cross.
    destruct (inductive_dec i i0), (eq_nat_dec n n2),
    (eq_nat_dec n0 n3), (eq_nat_dec n1 n4); [lft | rght .. ].
  - destruct t1; cross.
    destruct p as [i n], p0 as [i0 n0].
    destruct (eq_dec n n0), (inductive_dec i i0);
    destruct (H t1_1), (H0 t1_2), (H1 b0); [lft | rght .. ].
  - destruct t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct t; cross. destruct (string_dec s s0).
    + subst. left. reflexivity.
    + right. intros h. myInjection h. elim n. reflexivity.
  - destruct tt; cross. left. reflexivity.
  - destruct tt; cross. destruct (H t1); destruct (H0 tt); [lft | rght .. ].
  - destruct cc; cross; lft.
  - destruct cc; cross.
    destruct (eq_nat_dec n n0), (H t0), (H0 cc); [lft | rght .. ].
  - destruct ee; cross. lft.
  - destruct ee; cross.
    destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
    destruct (H t1); destruct (H0 t2); destruct (H1 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.

Definition Term_dec := proj1 TermTerms_dec.
Definition Terms_dec := proj1 (proj2 TermTerms_dec).

Fixpoint TrmSize (t:Term) : nat :=
  match t with
    | TProd _ ty bod => S (TrmSize bod + TrmSize ty)
    | TLambda _ ty bod => S (TrmSize bod + TrmSize ty)
    | TLetIn _ dfn ty bod => S (TrmSize dfn + TrmSize ty + TrmSize bod)
    | TApp fn a args => S (TrmSize fn + TrmSize a + TrmsSize args)
    | TCase _ ty mch brs => S (TrmSize ty + TrmSize mch + TrmBsSize brs)
    | TFix ds _ => S (TrmDsSize ds)
    | TCast t ty => S (TrmSize t + TrmSize ty)
    | _ => 1
  end
with TrmsSize (ts:Terms) : nat :=
  match ts with
    | tnil => 1
    | tcons s ss => S (TrmSize s + TrmsSize ss)
  end
with TrmBsSize (bs:Brs) : nat :=
  match bs with
    | bnil => 1
    | bcons _ s ss => S (TrmSize s + TrmBsSize ss)
  end
with TrmDsSize (ds:Defs) : nat :=
  match ds with
    | dnil => 1
    | dcons _ t1 t2 _ es => S (TrmSize t1 + TrmSize t2 + TrmDsSize es)
  end.

Definition isProp (t:Term) := t = prop.
Lemma isProp_dec: forall t, isProp t \/ ~ isProp t.
Proof.
  destruct t; try (right; unfold isProp; intros h; discriminate).
  destruct (Srt_dec SProp s).
  - subst. left. reflexivity.
  - right. destruct s.
    + elim n. reflexivity.
    + intros h. unfold isProp in h. discriminate.
    + intros h. unfold isProp in h. discriminate.
Qed.

Definition isLambda (t:Term) : Prop :=
  exists nm ty bod, t = TLambda nm ty bod.
Lemma IsLambda: forall nm ty bod, isLambda (TLambda nm ty bod).
intros. exists nm, ty, bod. reflexivity.
Qed.
Hint Resolve IsLambda.

Ltac isLam_inv :=
  let  xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j" in
  match goal with
    | [ h : (isLambda ?a) |- _ ] =>
      destruct h as [xx [yy [zz jj]]]; discriminate
  end.
              
Lemma isLambda_dec: forall t, {isLambda t}+{~ isLambda t}.
induction t;
  try (solve [right; intros h; unfold isLambda in h;
              elim h; intros x h1; elim h1; intros x0 h2;
              elim h2; intros x1 h3; discriminate]).
left. auto.
Qed.

Definition isCast (t:Term) : Prop :=
  exists tm ty, t = TCast tm ty.
Lemma IsCast: forall t ty, isCast (TCast t ty).
intros. exists t, ty. reflexivity.
Qed.
Hint Resolve IsCast.

Lemma isCast_dec: forall t, {isCast t}+{~ isCast t}.
induction t;
  try (solve [right; intros h; unfold isCast in h;
              destruct h as [tm [ty j]]; discriminate]).
left. auto.
Qed.

Definition isProof (t:Term) := exists prf, t = TProof prf.
Lemma IsProof: forall t, isProof (TProof t).
intros. exists t. reflexivity.
Qed.
Hint Resolve IsProof.

Lemma isProof_dec: forall t, {isProof t}+{~ isProof t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. auto.
Defined.

Lemma mkProof_isProof:
  forall t, isProof (mkProof t).
Proof.
  induction t; cbn; intros; unfold isProof;
  try assumption; try apply (triv_exists).
Qed.

(*************
Definition isCastProp (t:Term) := exists prp, t = TCast prp prop.

Lemma isCastProp_dec: forall t, isCastProp t \/ ~ isCastProp t.
Proof.
  intros. destruct (isCast_dec t).
  - destruct i as [x0 [x1 jx]]. destruct (isProp_dec x1).
    + unfold isProp in H. subst. left.
      unfold isCastProp. exists x0. reflexivity.
    + right. intros h. elim H. unfold isCastProp in h.
      destruct h as [y jy]. subst. myInjection jy. reflexivity.
  - right. unfold isCast in n. unfold isCastProp.
    intros h. destruct h as [y jy]. elim n. exists y, prop.
    assumption.
Qed.

Lemma isProofCast_dec: forall t, isProofCast t \/ ~ isProofCast t.
Proof.
  intros t. destruct (isCast_dec t).
  - destruct i as [tm [ty j]].
    + destruct (isCastProp_dec ty).
      * left. unfold isCastProp in H. destruct H as [x jx]. subst.
        unfold isProofCast. exists tm, x. reflexivity.
      * right. intros h. elim H. destruct h as [y0 [y1 jy]].
        unfold isCastProp. exists y1. subst. myInjection jy.
        reflexivity.
  - right. intros h. elim n. destruct h as [x0 [x1 jx]].
    subst. auto.
Qed.
 ***********************)

Definition isApp (t:Term) : Prop :=
  exists fn arg args, t = TApp fn arg args.
Lemma IsApp: forall fn arg args, isApp (TApp fn arg args).
intros. exists fn, arg, args. reflexivity.
Qed.
Hint Resolve IsApp.

Ltac isApp_inv :=
  let  xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j" in
  match goal with
    | [ h : (isApp ?a) |- _ ] =>
      destruct h as [xx [yy [zz jj]]]; discriminate
  end.

             Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
destruct t; try (right; not_isApp). 
left. auto.
Qed.

Definition isCastApp (t:Term) : Prop :=
  exists fn arg args ty, t = TCast (TApp fn arg args) ty.
Lemma IsAppCast:
  forall fn arg args ty, isCastApp (TCast (TApp fn arg args) ty).
intros. unfold isCastApp.
exists fn, arg, args, ty. reflexivity.
Qed.
Hint Resolve IsAppCast.

Lemma isCastApp_dec: forall t, {isCastApp t}+{~ isCastApp t}.
Proof.
  destruct t;
  try (solve [right; intros h;
              destruct h as [x1 [x2 [x3 [x4 h]]]]; discriminate]).
  destruct t1;
    try (solve [right; intros h;
                destruct h as [x1 [x2 [x3 [x4 h]]]]; discriminate]).
  left. exists t1_1, t1_2, t, t2. reflexivity.
Qed.

Definition isFix (t:Term) : Prop :=
  exists ds m, t = TFix ds m.
Lemma IsFix: forall ds m, isFix (TFix ds m).
intros. exists ds, m. reflexivity.
Qed.
Hint Resolve IsFix.

Ltac not_isFix :=
  let hh := fresh "h"
  with xx := fresh "x"
  with yy := fresh "y" 
  with jj := fresh "j" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.

Lemma isFix_dec: forall t, {isFix t}+{~ isFix t}.
induction t;
  try (solve [right; not_isFix]).
left. auto.
Qed.

Definition isConstruct (t:Term) : Prop :=
  exists i n np na, t = TConstruct i n np na.
Lemma IsConstruct: forall i n np na, isConstruct (TConstruct i n np na).
intros. exists i, n, np, na. reflexivity.
Qed.
Hint Resolve IsConstruct.

Lemma isConstruct_dec: forall t, isConstruct t \/ ~ isConstruct t.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x0 [x1 [x2 [x3 j]]]]; discriminate).
  - left. auto.
Qed.


Inductive isCanonical : Term -> Prop :=
| canC: forall (i:inductive) (n np na:nat), isCanonical (TConstruct i n np na)
| canA: forall (arg:Term) (args:Terms) (i:inductive) (n np na:nat), 
    isCanonical (TApp (TConstruct i n np na) arg args)
| canP: forall t, isCanonical t -> isCanonical (TProof t).
Hint Constructors isCanonical.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
Proof.
  induction t; try (solve [right; intros h; inversion h; inversion H;
                           destruct H1; discriminate]).
  - destruct IHt.
    + left. constructor. assumption.
    + right. intros h. inversion_clear h. contradiction.
  - destruct (isConstruct_dec t1).
    + left. unfold isConstruct in H. destruct H as [x0 [x1 [x2 [x3 j]]]].
      subst. constructor.
    + right. intros h. inversion_Clear h. elim H. auto.
  - left. constructor.
Qed.
     
Function canonicalP (t:Term) : option (nat * Terms) :=
  match t with
    | TConstruct _ r _ _ => Some (r, tnil)
    | TApp (TConstruct _ r _ _) arg args => Some (r, tcons arg args)
    | TProof t => canonicalP t
    | _ => None
  end.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Some x -> isCanonical t.
Proof.
  induction t; simpl; intros; try discriminate.
  - constructor. eapply IHt. eassumption.
  - destruct t1; try discriminate. constructor.
  - constructor.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x, canonicalP t = Some x.
Proof.
  induction 1; simpl.
  - exists (n, tnil). reflexivity.
  - exists (n, tcons arg args). reflexivity.
  - assumption.
Qed.

(** some utility operations on [Terms] ("lists" of Term) **)
Fixpoint tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
induction ts; simpl; try reflexivity.
rewrite IHts. reflexivity.
Qed.
Hint Rewrite tappend_tnil : tappend.

Lemma nil_tappend:
  forall ts us:Terms, tnil = tappend ts us -> ts = tnil /\ us = tnil.
Proof.
  induction ts; cbn; intros.
  - intuition.
  - discriminate.
Qed.

Lemma tappend_assoc:
  forall xts yts zts,
       (tappend xts (tappend yts zts)) = (tappend (tappend xts yts) zts).
  induction xts; intros yts zts; simpl.
  - reflexivity.
  - rewrite IHxts. reflexivity.
Qed.

Lemma tappend_cons_lem:
  forall ys t zs,
    tappend ys (tcons t zs) = tappend (tappend ys (tunit t)) zs.
  induction ys; intros tt zzs; simpl.
  - reflexivity.
  - rewrite IHys. reflexivity.
Qed.
  
Lemma tappend_tappend_lem:
  forall xts yts t zts,
       (tappend xts (tappend yts (tcons t zts))) =
       (tappend (tappend xts (tappend yts (tcons t tnil))) zts).
  intros xts yts t zts. rewrite tappend_cons_lem. rewrite tappend_assoc.
  reflexivity.
Qed.

Lemma tappend_mk_canonical:
  forall ts s ss, exists u us, (tappend ts (tcons s ss)) = tcons u us.
Proof.
  destruct ts; intros s ss; simpl.
  - exists s, ss. reflexivity.
  - exists t, (tappend ts (tcons s ss)). reflexivity.
Qed.

Lemma tlength_tappend:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; simpl; intros; try reflexivity.
  - rewrite IHts. reflexivity.
Qed.

Lemma tappend_tcons_tunit:
  forall bs ds cs x,
    tappend bs (tcons x cs) = tappend ds cs -> tappend bs (tunit x) = ds.
Proof.
  induction bs; destruct ds; cbn; intros.
  - assert (j:= f_equal tlength H). cbn in j. omega.
  - injection H. intros. subst x. destruct ds.
    + reflexivity.
    + injection H; intros.
      assert (j:= f_equal tlength H). cbn in j.
      rewrite tlength_tappend in j. omega.
  - destruct cs.
    + discriminate.
    + injection H; intros. assert (j:= f_equal tlength H0).
      rewrite tlength_tappend in j. cbn in j. omega.
  - injection H; intros.  assert (j:= f_equal tlength H0).
    rewrite tlength_tappend in j. cbn in j.
    specialize (IHbs _ _ _ H0). rewrite IHbs. rewrite H1. reflexivity.
Qed.


Fixpoint tmap (fn:Term -> Term) (ts:Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons x xs => tcons (fn x) (tmap fn xs)
  end.

Fixpoint tIn (a:Term) (l:Terms) : Prop :=
    match l with
      | tnil => False
      | tcons b m => b = a \/ tIn a m
    end.

Lemma tIn_tappend1:
  forall u ts ss, tIn u (tappend ts (tcons u ss)).
Proof.
  induction ts; intros ss.
  - simpl. left. reflexivity.
  - simpl. right. apply IHts.
Qed.

Lemma tIn_tappend2:
  forall t ts us, tIn t ts -> tIn t (tappend ts us).
induction ts; intros us h; inversion_Clear h; simpl.
- left. reflexivity.
- right. apply IHts. assumption.
Qed.

Function tskipn (n:nat) (l:Terms) : option Terms :=
  match n, l with
    | 0, l => Some l
    | S n, tcons a l => tskipn n l
    | S _, tnil => None
  end.

Fixpoint le (n m: nat): bool :=
  match n, m with
    | 0, _ => true
    | S n, S m => le n m
    | _, _ => false
  end.


Record split := mkSplit {fsts:Terms; nst:Term; lsts:Terms}.

Function tsplit (n:nat) (l:Term) (ls:Terms) {struct n} : option split :=
  match n, ls with
    | 0, tnil => Some (mkSplit tnil l tnil)
    | _, tnil => None
    | 0, ts => Some (mkSplit tnil l ts)
    | S m, tcons t ts =>
      match tsplit m t ts with
        | None => None
        | Some (mkSplit fs s ls) => Some (mkSplit (tcons l fs) s ls)
      end
  end.
(***
Definition testts:=
  (tcons (TRel 1) (tcons (TRel 2) (tcons (TRel 3) (tunit (TRel 4))))).
Eval cbv in tsplit 0 (TRel 0) testts.
Eval cbv in tsplit 1 (TRel 0) testts.
Eval cbv in tsplit 2 (TRel 0) testts.
Eval cbv in tsplit 3 (TRel 0) testts.
Eval cbv in tsplit 4 (TRel 0) testts.
Eval cbv in tsplit 5 (TRel 0) testts.
***)

Lemma tsplit_0_Some:
  forall ts t, tsplit 0 t ts = Some (mkSplit tnil t ts).
Proof. 
  destruct ts; intros; reflexivity.
Qed.

Lemma tsplit_tcons:
  forall ix t ts frsts u lasts,
    tsplit ix t ts = Some {| fsts:= frsts; nst:= u; lsts:= lasts |} ->
         tcons t ts = tappend frsts (tcons u lasts).
Proof.
  intros ix t ts.
  functional induction (tsplit ix t ts); intros; try discriminate.
  - myInjection H. reflexivity.
  - myInjection H. reflexivity.
  - myInjection H. cbn. apply f_equal2. reflexivity.
    apply IHo. assumption.
Qed.

Lemma tcons_tsplit:
  forall (frsts ts lasts:Terms) t u,
    tcons t ts = tappend frsts (tcons u lasts) ->
     tsplit (tlength frsts) t ts = Some (mkSplit frsts u lasts).
Proof.
  induction frsts; intros;cbn in *.
  - myInjection H. destruct lasts; reflexivity.
  - destruct (tappend_mk_canonical frsts u lasts) as [y [ys jy]].
    rewrite jy in H. myInjection H.
    erewrite IHfrsts. reflexivity. rewrite jy. reflexivity.
Qed.
  
Lemma tsplit_sanity:
  forall n t ts, match tsplit n t ts with
                 | None => n > tlength ts
                 | Some (mkSplit s1 s2 s3) =>
                   tcons t ts = tappend s1 (tcons s2 s3) /\
                   n = tlength s1
               end.
Proof.
  intros n t ts. functional induction (tsplit n t ts); intros; cbn.
  - intuition.
  - destruct n. elim y. omega.
  - destruct ls. elim y. intuition.
  - rewrite e1 in IHo. omega.
  - rewrite e1 in IHo. rewrite (proj1 IHo). rewrite (proj2 IHo).
    intuition.
Qed.

Function atsplit (n:nat) (ls:Terms) {struct ls} : option split :=
  match n, ls with
    | _, tnil => None
    | 0, tcons t ts => Some (mkSplit tnil t ts)
    | S m, tcons t ts =>
      match atsplit m ts with
        | Some (mkSplit fs u ls) => Some (mkSplit (tcons t fs) u ls)
        | None => None
      end
  end.
(*********
Eval cbv in atsplit 0 (tcons (TRel 0) testts).
Eval cbv in atsplit 1 (tcons (TRel 0) testts).
Eval cbv in atsplit 2 (tcons (TRel 0) testts).
Eval cbv in atsplit 3 (tcons (TRel 0) testts).
Eval cbv in atsplit 4 (tcons (TRel 0) testts).
Eval cbv in atsplit 5 (tcons (TRel 0) testts).
***********)

Lemma atsplit_tsplit:
  forall n u us, atsplit n (tcons u us) = tsplit n u us.
Proof.
  intros n u us.
  functional induction (tsplit n u us); cbn; intros;
  try reflexivity; try discriminate.
  - destruct n.
    + elim y.
    + destruct n; reflexivity.
  - destruct m.
    + rewrite e1 in IHo. cbn in IHo. discriminate.
    + rewrite e1 in IHo. cbn in IHo. destruct (atsplit m ts).
      destruct s. discriminate. reflexivity.
  - rewrite e1 in IHo. cbn in IHo.
    destruct m.
    + injection IHo; intros. subst fs. subst. reflexivity.
    + destruct (atsplit m ts).
      * destruct s0. injection IHo; intros. subst fs. subst.
        reflexivity.
      * discriminate.      
Qed.

Lemma atsplit_S:
  forall m ts fs u ls,
    atsplit m ts = Some {| fsts:= fs; nst:= u; lsts:= ls |} ->
    forall t, atsplit (S m) (tcons t ts) =
              Some {| fsts:= tcons t fs; nst:= u; lsts:= ls |}.
Proof.
  intros; functional induction (atsplit m ts); intros; try discriminate.
  - injection H; intros. subst fs. subst. cbn. reflexivity.
  - injection H; intros. subst fs. subst. cbn. rewrite e1. reflexivity.
Qed.

Function aatsplit (n:nat) (ls:Terms) {struct n} : option split :=
  match n, ls with
    | _, tnil => None
    | 0, tcons t ts => Some (mkSplit tnil t ts)
    | S m, tcons t ts =>
      match aatsplit m ts with
        | Some (mkSplit fs u ls) => Some (mkSplit (tcons t fs) u ls)
        | None => None
      end
  end.

Lemma aatsplit_atsplit:
  forall n ts, aatsplit n ts = atsplit n ts.
Proof.
  intros n ts. functional induction (atsplit n ts); cbn; try reflexivity.
  - destruct n; reflexivity.
  - rewrite IHo. destruct (atsplit m ts).
    + destruct s. myInjection e1. reflexivity.
    + discriminate.
  - rewrite e1 in IHo. rewrite IHo. reflexivity.
Qed.
      
(*****)
Fixpoint treverse (ts: Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons b bs => tappend (treverse bs) (tunit b)
  end.

Fixpoint tfrsts (n:nat) (ts:Terms) : option Terms :=
  match n, ts with
    | 0, _ => Some tnil
    | S m, tnil => None
    | S m, tcons u us => match tfrsts m us with
                           | None => None
                           | Some xs => Some (tcons u xs)
                         end
  end.
Definition tlasts (n:nat) (ts:Terms) : option Terms :=
  match tfrsts (tlength ts - n) (treverse ts) with
    | None => None
    | Some us => Some (treverse us)
  end.
  
Function tnth (n:nat) (l:Terms) {struct l} : option Term :=
  match l with
    | tnil => None
    | tcons x xs => match n with
                      | 0 => Some x
                      | S m => tnth m xs
                    end
  end.

Lemma tnth_tsplit_sanity:
  forall n t ts, match tsplit n t ts with
                 | None => tnth n (tcons t ts) = None
                 | Some sp => tnth n (tcons t ts) = Some (nst sp)
               end.
Proof.
  intros n t ts. functional induction (tsplit n t ts); cbn; try reflexivity.
  - destruct n. elim y. reflexivity.
  - rewrite e1 in IHo. destruct m.
    + cbn in IHo. discriminate.
    + cbn in IHo. assumption.
  - rewrite e1 in IHo. destruct m; cbn in IHo; assumption.
Qed.
    
Lemma tsplit_tnth_sanity:
  forall xs n u, tnth n xs = Some u ->
                 exists t ts frsts lasts,
                   xs = tcons t ts /\
                   tsplit n t ts = Some (mkSplit frsts u lasts).
Proof.
  intros xs n u.
  functional induction (tnth n xs); intros; try discriminate.
  - myInjection H. exists u, xs, tnil, xs. intuition. cbn.
    destruct xs; reflexivity.
  - destruct (IHo H) as [y0 [y1 [y2 [y3 [jy1 jy2]]]]]. subst xs.
    exists x, (tcons y0 y1), (tcons x y2), y3. intuition.
    cbn. rewrite jy2. reflexivity.
Qed.
    
Lemma tnth_tlength_sanity:
  forall fsts t lsts,
    tnth (tlength fsts) (tappend fsts (tcons t lsts)) = Some t.
Proof.
  induction fsts0; intros. reflexivity.
  - cbn. apply IHfsts0.
Qed.

Lemma tnth_None_tsplit_None:
  forall n t ts, tsplit n t ts = None -> tnth n (tcons t ts) = None.
Proof.
  intros. assert (k:= tnth_tsplit_sanity n t ts). rewrite H in k.
  assumption.
Qed.
  
Lemma tnth_extend1:
  forall n l t,  tnth n l = Some t -> n < tlength l.
Proof.
  induction n; induction l; simpl; intros; try discriminate; try omega.
  - apply lt_n_S. eapply IHn. eassumption.
Qed.

Lemma tnth_extend2:
  forall n l,  n < tlength l -> exists t, tnth n l = Some t.
Proof.
  induction n; intros.
  - destruct l. simpl in H. omega. exists t. reflexivity.
  - destruct l. inversion H. simpl in H.
    specialize (IHn _ (lt_S_n _ _ H)). destruct IHn. exists x.
    simpl. assumption.
Qed.

Lemma tnth_append:
  forall n args t, tnth n args = Some t ->
            forall brgs, tnth n (tappend args brgs) = Some t.
Proof.
  induction n; induction args; simpl; intros; try discriminate; try assumption.
  - apply IHn. assumption.
Qed.


(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
    | TApp fn b bs => TApp fn b (tappend bs args)
    | fn => match args with
              | tnil => fn
              | tcons c cs => TApp fn c cs
            end
  end.

Lemma mkApp_tnil_ident: forall t, mkApp t tnil = t.
  destruct t; cbn; try rewrite tappend_tnil; try reflexivity.
Qed.

Inductive MkApp :Term -> Terms -> Term -> Prop :=
| maApp: forall fn b bs cs,
           MkApp (TApp fn b bs) cs (TApp fn b (tappend bs cs))
| maNil: forall fn, ~ isApp fn -> MkApp fn tnil fn
| maCons: forall fn c cs, ~ isApp fn -> MkApp fn (tcons c cs) (TApp fn c cs).
Hint Constructors MkApp.

Lemma MkApp_tcons_isApp:
  forall fn bs res, MkApp fn bs res ->
  forall c cs, bs = tcons c cs -> isApp res.
induction 1; intros cx csx h.
- exists fn, b, (tappend bs cs). reflexivity.
- discriminate.
- injection h; intros; subst.
  exists fn, cx, csx. reflexivity.
Qed.

Lemma MkApp_nil_ident:
  forall fn, ~ isApp fn ->  MkApp fn tnil fn.
induction fn; simpl; intros h; try (constructor; assumption).
Qed.

Lemma MkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, MkApp fn (tcons arg args) (TApp fn arg args).
induction fn; simpl; intros h arg args; try (constructor; assumption).
Qed.

Lemma mkApp_MkApp: forall fn bs, MkApp fn bs (mkApp fn bs).
induction fn; induction bs; intros; simpl;
try (solve [apply maNil; not_isApp]);
try (solve [apply maCons; not_isApp]). 
- apply maApp. 
- apply maApp. 
Qed.

Lemma MkApp_mkApp:
  forall fn bs res, MkApp fn bs res -> mkApp fn bs = res.
induction fn; intros bs res h; try (inversion_Clear h; simpl; try reflexivity).
- rewrite tappend_tnil. reflexivity.
- elim H. exists fn1, fn2, t. reflexivity.
Qed.

Lemma MkApp_single_valued:
  forall fn bs res1, MkApp fn bs res1 ->
     forall res2, MkApp fn bs res2 -> res1 = res2.
Proof.
intros. rewrite <- (MkApp_mkApp H). rewrite <- (MkApp_mkApp H0).
reflexivity.
Qed.

Lemma mkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, mkApp fn (tcons arg args) = TApp fn arg args.
induction fn; simpl; intros h arg args; try (constructor; assumption).
- elim h. exists fn1, fn2, t. reflexivity.
Qed.

Lemma mkApp_goodFn:
  forall fn t ts, ~ isApp fn -> mkApp fn (tcons t ts) = TApp fn t ts.
destruct fn; intros; try reflexivity.
- elim H. auto.
Qed.

Lemma mkProof_goodProof:
  forall t, ~ isProof t -> mkProof t = TProof t.
destruct t; intros; try reflexivity.
- elim H. exists t. reflexivity.
Qed.

Lemma pre_mkApp_isApp:
  forall fn args res, MkApp fn args res ->
  forall b bs, args = tcons b bs -> isApp res.
induction 1; intros bx bsx h.
- exists fn, b, (tappend bs cs). reflexivity.
- discriminate.
- exists fn, c, cs. reflexivity.
Qed.

Lemma mkApp_isApp:
  forall fn arg args, isApp (mkApp fn (tcons arg args)).
intros fn arg args. eapply (@pre_mkApp_isApp fn (tcons arg args)).
- destruct (isApp_dec fn) as [h1 | h2].
  destruct h1 as [x0 [x1 [x2 h]]].
  + rewrite h. apply maApp. 
  + apply mkApp_MkApp. 
- reflexivity.
Qed.

Lemma mkApp_idempotent:
 forall fn args brgs,
   mkApp (mkApp fn args) brgs = mkApp fn (tappend args brgs).
Proof.
  induction fn; induction args; simpl; intros; try reflexivity.
  - rewrite tappend_tnil. reflexivity.
  - rewrite <- tappend_assoc. simpl. reflexivity.
Qed.

Lemma mkProof_idempotent:
 forall t,
   mkProof (mkProof t) = mkProof t.
Proof.
  induction t; cbn; intros; try reflexivity.
Qed.

Lemma isApp_mkApp_isApp:
  forall t, isApp (mkApp t tnil) -> isApp t.
Proof.
  destruct t; intros h; destruct h as [x0 [x1 [x2 j]]]; simpl in j;
  try discriminate.
  - exists t1, t2, t3. reflexivity.
Qed.

Lemma not_isApp_mkApp_not_isApp:
  forall t, ~ isApp t -> ~ isApp (mkApp t tnil).
Proof.
  intros t h1 h2. elim h1. apply isApp_mkApp_isApp. assumption.
Qed.

Lemma isApp_mkApp_isApp2:
  forall t, isApp t -> isApp (mkApp t tnil).
Proof.
  inversion 1. destruct H0 as [x0 [x1 j]]. subst. simpl.
  exists x, x0, (tappend x1 tnil). reflexivity.
Qed.

Lemma not_isApp_mkApp_isApp2:
  forall t, ~ isApp (mkApp t tnil) -> ~ isApp t.
Proof.
  destruct t; intros h1 h2; elim h1; try assumption. 
  - apply isApp_mkApp_isApp2. assumption.
Qed.

Lemma not_isApp_mkApp_TApp:
  forall t arg args, ~ isApp t -> 
    mkApp (mkApp t tnil) (tcons arg args) = TApp (mkApp t tnil) arg args.
induction t; intros arg args h; simpl; try reflexivity.
- elim h. exists t1, t2, t3. reflexivity.
Qed.

(** main lemma for dealing with mkApp **)
Lemma mkApp_isApp_lem:
  forall fn arg args, exists fn' arg' args',
    mkApp fn (tcons arg args) = TApp fn' arg' (tappend args' args) /\
    ((~ isApp fn /\ fn' = fn /\ arg = arg' /\ args' = tnil) \/
     (isApp fn /\ TrmSize fn' < TrmSize fn /\ tIn arg args')).
Proof.
  induction fn; intros arg args; unfold mkApp; simpl.
  - exists (TRel n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TSort s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TProof fn), arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
  - exists (TCast fn1 fn2), arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
  - exists (TProd n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLambda n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLetIn n fn1 fn2 fn3), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - change (exists (fn' arg' : Term) (args' : Terms),
              TApp fn1 fn2 (tappend t (tcons arg args)) =
              TApp fn' arg' (tappend args' args) /\
              (~ isApp (TApp fn1 fn2 t) /\
               fn' = TApp fn1 fn2 t /\ arg = arg' /\ args' = tnil \/
                                                     isApp (TApp fn1 fn2 t) /\ 
               TrmSize fn' < S (TrmSize fn1 + TrmSize fn2 + TrmsSize t) /\
               tIn arg args')).
    exists fn1, fn2, (tappend t (tunit arg)). split.
    + rewrite <- tappend_assoc. simpl. reflexivity.
    + right. split; try split.
      * exists fn1, fn2, t. reflexivity.
      * omega.
      * apply tIn_tappend1.
  - exists (TConst s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TAx s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TInd i), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TConstruct i n n0 n1), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase p fn1 fn2 b), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TWrong s), arg, tnil. cbn. split. reflexivity.
    left. repeat split. not_isApp.
Qed.

Lemma mkApp_mkApp_fn:
  forall fn, exists fn',
    (forall arg args, exists arg' args',
    mkApp fn (tcons arg args) = TApp fn' arg' (tappend args' args)) /\
    (forall brg brgs, exists brg' brgs',
      mkApp fn (tcons brg brgs) = TApp fn' brg' (tappend brgs' brgs)).
Proof.
  intros fn.
  case_eq fn; intros;
  try (solve [exists fn; subst; split; intros carg cargs;
                     exists carg, tnil; reflexivity]).
  - exists t. split; intros crg crgs; exists t0; cbn;
    exists (tappend t1 (tunit crg));
    rewrite <- tappend_assoc; reflexivity.
Qed.

   
(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaSort: forall srt, WFapp (TSort srt)
| wfaProof: forall t, WFapp t -> WFapp (TProof t)
| wfaCast: forall tm ty, WFapp tm -> WFapp ty -> WFapp (TCast tm ty)
| wfaProd: forall nm ty bod,
            WFapp bod -> WFapp ty -> WFapp (TProd nm ty bod)
| wfaLambda: forall nm ty bod,
            WFapp bod -> WFapp ty -> WFapp (TLambda nm ty bod)
| wfaLetIn: forall nm dfn ty bod,
             WFapp dfn -> WFapp bod -> WFapp ty -> 
             WFapp (TLetIn nm dfn ty bod)
| wfaApp: forall fn t ts,
           ~ (isApp fn) -> WFapp fn -> WFapp t -> WFapps ts ->
           WFapp (TApp fn t ts)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaAx: forall s, WFapp (TAx s)
| wfaInd: forall i, WFapp (TInd i)
| wfaConstruct: forall i m np na, WFapp (TConstruct i m np na)
| wfaCase: forall m ty mch brs,
            WFapp mch -> WFappBs brs -> WFapp ty ->
            WFapp (TCase m ty mch brs)
| wfaFix: forall defs m,
            WFappDs defs -> WFapp (TFix defs m)
with WFapps: Terms -> Prop :=
| wfanil: WFapps tnil
| wfacons: forall t ts, WFapp t -> WFapps ts -> WFapps (tcons t ts)
with WFappBs: Brs -> Prop :=
| wfabnil: WFappBs bnil
| wfabcons: forall n b bs, WFapp b -> WFappBs bs ->  WFappBs (bcons n b bs)
with WFappDs: Defs -> Prop :=
| wfadnil: WFappDs dnil
| wfadcons: forall nm ty bod arg ds,
             WFapp ty -> WFapp bod -> WFappDs ds ->
             WFappDs (dcons nm ty bod arg ds).
Hint Constructors WFapp WFapps WFappBs WFappDs.
Scheme WFapp_ind' := Minimality for WFapp Sort Prop
  with WFapps_ind' := Minimality for WFapps Sort Prop
  with WFappBs_ind' := Minimality for WFappBs Sort Prop
  with WFappDs_ind' := Minimality for WFappDs Sort Prop.
Combined Scheme WFappTrmsBrsDefs_ind
         from WFapp_ind', WFapps_ind', WFappBs_ind', WFappDs_ind'.

Lemma tappend_pres_WFapps:
  forall ts, WFapps ts -> forall us, WFapps us -> WFapps (tappend ts us).
Proof.
  induction 1; intros us hus; simpl.
  - assumption.
  - constructor. assumption. apply IHWFapps. assumption.
Qed.

Lemma canonicalP_pres_WFapp:
  forall t, WFapp t ->
  forall r args, canonicalP t = Some (r, args) -> WFapps args.
Proof.
  induction t; simpl; intros; try discriminate.
  - eapply IHt; inversion_Clear H; eassumption.
  - destruct t1; try discriminate. myInjection H0. inversion_Clear H.
    constructor; assumption.
  - myInjection H0. constructor.
Qed.

Lemma WFapps_tappendl:
  forall ts us, WFapps (tappend ts us) -> WFapps ts.
Proof.
  induction ts; simpl; intros us h; intuition. 
  + inversion h; constructor. assumption. eapply IHts. eassumption.
Qed.

Lemma WFapps_tappendr:
  forall ts us, WFapps (tappend ts us) -> WFapps us.
Proof.
  intros ts us. functional induction (tappend ts us); intuition.
  - apply IHt. inversion H. assumption.
Qed.

Lemma WFapp_mkApp_TApp:
  forall u, WFapp u -> forall t a1 args, u = (TApp t a1 args) ->
    mkApp t (tcons a1 args) = TApp t a1 args.
Proof.
  induction 1; intros; try discriminate.
  - injection H3. intros. subst. rewrite (mkApp_cons_App H). reflexivity.
Qed.

Lemma WFapp_mkApp_WFapp:
  forall u, WFapp u -> forall t ts, u = mkApp t ts -> WFapp t /\ WFapps ts.
Proof.
  induction 1; intros tx tsx h; destruct tx; destruct tsx; simpl in *; 
  try discriminate; intuition; injection h; intros; subst;
  try (constructor; assumption); try assumption.
  - constructor; try assumption. eapply WFapps_tappendl. eassumption.
  - constructor; try assumption. eapply WFapps_tappendl. eassumption.
  - eapply WFapps_tappendr. eassumption.
Qed.

Lemma WFapp_mkProof_WFapp:
  forall t, WFapp (mkProof t) -> WFapp t.
Proof. 
  intros t. functional induction (mkProof t); intros.
  - assumption.
  - inversion_Clear H. assumption.
Qed.

Lemma mkApp_pres_WFapp:
  forall ts, WFapps ts -> forall t, WFapp t -> WFapp (mkApp t ts).
Proof.
  induction 1; intros s hs; inversion_Clear hs; simpl; intuition;
  try (constructor; [not_isApp | constructor; assumption| assumption .. ]).
  - rewrite tappend_tnil. constructor; assumption.
  - constructor; try assumption.
    + apply tappend_pres_WFapps. assumption. constructor; assumption.
Qed.

Lemma mkProof_pres_WFapp:
  forall t, WFapp t -> WFapp (mkProof t).
Proof.
  induction 1; cbn; try constructor; try not_isProof; try assumption;
  try (constructor; assumption).
Qed.

Lemma tnth_pres_WFapp:
  forall (brs:Terms), WFapps brs -> forall n t, tnth n brs = Some t -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (tnth n brs); intros; try discriminate.
  - injection H; intros; subst. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma bnth_pres_WFapp:
  forall (brs:Brs), WFappBs brs ->
                    forall n t m, bnth n brs = Some (t,m) -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (bnth n brs); intros; try discriminate.
  - myInjection H. inversion h. assumption.
  - eapply IHo; inversion h; eassumption.
Qed.

Lemma dnthBody_pres_WFapp:
  forall (ds:Defs), WFappDs ds ->
    forall n x ix, (dnthBody n ds) = Some (x, ix) -> WFapp x.
Proof.
  intros ds h n x ix.
  functional induction (dnthBody n ds); intros; auto.
  - discriminate.
  - myInjection H. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.


Lemma tskipn_pres_WFapp:
  forall args, WFapps args -> forall np ts, tskipn np args = Some ts ->
   WFapps ts.
  intros args hargs np ts h.
  functional induction (tskipn np args).
  - injection h. intros. subst. assumption.
  - inversion_Clear hargs. apply IHo; try assumption.
  - discriminate.
Qed.

(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfSort: forall n srt, WFTrm (TSort srt) n
| wfProof: forall n t, WFTrm t n -> WFTrm (TProof t) n
| wfCast: forall n t ty, WFTrm t n -> WFTrm ty n -> WFTrm (TCast t ty) n
| wfProd: forall n nm ty bod,
            WFTrm bod (S n) -> WFTrm ty n -> WFTrm (TProd nm ty bod) n
| wfLambda: forall n nm ty bod,
            WFTrm bod (S n) -> WFTrm ty n -> WFTrm (TLambda nm ty bod) n
| wfLetIn: forall n nm dfn ty bod,
             WFTrm dfn n -> WFTrm bod (S n) -> WFTrm ty n -> 
             WFTrm (TLetIn nm dfn ty bod) n
| wfApp: forall n fn t ts,
           ~ (isApp fn) -> WFTrm fn n -> WFTrm t n -> WFTrms ts n ->
           WFTrm (TApp fn t ts) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfAx: forall n t, WFTrm (TAx t)  n
| wfInd: forall n i, WFTrm (TInd i) n
| wfConstruct: forall n i m np na, WFTrm (TConstruct i m np na) n
| wfCase: forall n m ty mch brs,
            WFTrm mch n -> WFTrmBs brs n -> WFTrm ty n ->
            WFTrm (TCase m ty mch brs) n
| wfFix: forall n defs m,
           WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
with WFTrms: Terms -> nat -> Prop :=
| wfnil: forall n, WFTrms tnil n
| wfcons: forall n t ts, WFTrm t n -> WFTrms ts n -> WFTrms (tcons t ts) n
with WFTrmBs: Brs -> nat -> Prop :=
| wfbnil: forall n, WFTrmBs bnil n
| wfbcons: forall n m b bs,
    WFTrm b n -> WFTrmBs bs n -> WFTrmBs (bcons m b bs) n
with WFTrmDs: Defs -> nat -> Prop :=
| wfdnil: forall n, WFTrmDs dnil n
| wfdcons: forall n nm ty bod arg ds,
             WFTrm ty n -> WFTrm bod n -> WFTrmDs ds n ->
             WFTrmDs (dcons nm ty bod arg ds) n.
Hint Constructors WFTrm WFTrms WFTrmBs WFTrmDs.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrms_ind' := Minimality for WFTrms Sort Prop
  with WFTrmBs_ind' := Minimality for WFTrmBs Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsBrsDefs_ind
         from WFTrm_ind', WFTrms_ind', WFTrmBs_ind', WFTrmDs_ind'.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall ts n, WFTrms ts n -> WFapps ts) /\
  (forall bs n, WFTrmBs bs n -> WFappBs bs) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try (constructor; try assumption).
Qed.


(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:string.

Inductive PoccTrm : Term -> Prop :=
| PoProof: forall t, PoccTrm t -> PoccTrm (TProof t)
| PoProdBod: forall s ty bod, PoccTrm bod -> PoccTrm (TProd s ty bod)
| PoProdTy: forall s ty bod, PoccTrm ty -> PoccTrm (TProd s ty bod)
| PoLambdaBod: forall s ty bod, PoccTrm bod -> PoccTrm (TLambda s ty bod)
| PoLambdaTy: forall s ty bod, PoccTrm ty -> PoccTrm (TLambda s ty bod)
| PoCastTm: forall t ty, PoccTrm t -> PoccTrm (TCast t ty)
| PoCastTy: forall t ty, PoccTrm ty -> PoccTrm (TCast t ty)
| PoLetInDfn: forall s ty dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn ty bod)
| PoLetInBod: forall s ty dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn ty bod)
| PoLetInTy: forall s ty dfn bod,
                PoccTrm ty -> PoccTrm (TLetIn s dfn ty bod)
| PoAppL: forall fn a args, PoccTrm fn -> PoccTrm (TApp fn a args)
| PoAppA: forall fn a args, PoccTrm a -> PoccTrm (TApp fn a args)
| PoAppR: forall fn a args, PoccTrms args -> PoccTrm (TApp fn a args)
| PoConst: PoccTrm (TConst nm)
| PoCaseA: forall n p ty mch brs, PoccTrm (TCase ((mkInd nm n), p) ty mch brs)
| PoCaseL: forall n ty mch brs, PoccTrm mch -> PoccTrm (TCase n ty mch brs)
| PoCaseR: forall n ty mch brs, PoccBrs brs -> PoccTrm (TCase n ty mch brs)
| PoCaseTy: forall n ty mch brs, PoccTrm ty -> PoccTrm (TCase n ty mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstr: forall m1 m2 np na, PoccTrm (TConstruct (mkInd nm m1) m2 np na)
with PoccTrms : Terms -> Prop :=
| PoThd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
| PoTtl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccBrs : Brs -> Prop :=
| PoBhd: forall n t ts, PoccTrm t -> PoccBrs (bcons n t ts)
| PoBtl: forall n t ts, PoccBrs ts -> PoccBrs (bcons n t ts)
with PoccDefs : Defs -> Prop :=
| PoDhd_ty: forall dn dty db dra ds,
           PoccTrm dty -> PoccDefs (dcons dn dty db dra ds)
| PoDhd_bod: forall dn dty db dra ds,
           PoccTrm db -> PoccDefs (dcons dn dty db dra ds)
| PoDtl: forall dn dty db dra ds,
           PoccDefs ds -> PoccDefs (dcons dn dty db dra ds).
Hint Constructors PoccTrm PoccTrms PoccBrs PoccDefs.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poTrms_ind' := Minimality for PoccTrms Sort Prop
  with poBrs_ind' := Minimality for PoccBrs Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsBrsDefs_ind
         from poTrm_ind', poTrms_ind', poBrs_ind', poDefs_ind'.


Lemma PoccTrm_mkProof:
  forall t, PoccTrm (mkProof t) -> PoccTrm t.
Proof.
  induction t; cbn; intros h; inversion_Clear h; try assumption;
  try (constructor; apply IHt; rewrite <- H; constructor; assumption).
  constructor. assumption.
Qed.
  
Lemma Pocc_TConst: forall s2, PoccTrm (TConst s2) -> nm = s2.
intros s2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TConst: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto. 
Qed.

Lemma Pocc_TCnstr:
  forall s2 m1 m2 np na,
    PoccTrm (TConstruct (mkInd s2 m1) m2 np na) -> nm = s2.
intros s2 m1 m2 np na h. inversion h. reflexivity.
Qed.

Lemma notPocc_TCnstr:
  forall s2 m1 m2 np na,
    ~ PoccTrm (TConstruct (mkInd s2 m1) m2 np na) -> nm <> s2.
intros s2 m1 m2 np na h j. elim h. rewrite <- j. auto. 
Qed.

Lemma PoccTrms_tappendl:
  forall ts us, PoccTrms ts -> PoccTrms (tappend ts us).
induction 1; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappendr:
  forall us, PoccTrms us -> forall ts, PoccTrms (tappend ts us).
induction 1; induction ts0; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
- simpl in IHPoccTrms. apply PoTtl. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappend_tcons:
  forall u, PoccTrm u -> forall ts us, PoccTrms (tappend ts (tcons u us)).
intros. apply PoccTrms_tappendr. apply PoThd. assumption.
Qed.

Lemma tnth_PoccTrms:
  forall ix args t, tnth ix args = Some t ->
                    PoccTrm t -> PoccTrms args.
Proof.
  intros ix args t h1  h2.
  functional induction (tnth ix args); try discriminate.
  - myInjection h1. constructor. assumption.
  - apply PoTtl. intuition.
Qed.

Lemma PoccTrms_append_invrt:
  forall bs cs, PoccTrms (tappend bs cs) -> PoccTrms bs \/ PoccTrms cs.
induction bs; intros cs h; simpl in h.
- intuition.
- inversion_Clear h.
  * left. apply PoThd. assumption.
  * destruct (IHbs _ H0).
    left. apply PoTtl. assumption.
    right. assumption.
Qed.

Lemma inverse_Pocc_TConstL: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma notPocc_TApp:
  forall t arg args, ~ PoccTrm (TApp t arg args) ->
     ~ PoccTrm t /\ ~ PoccTrm arg /\ ~ PoccTrms args.
intuition.
Qed.

Lemma notPocc_mkApp:
  forall t args, ~ PoccTrm (mkApp t args) ->
     ~ PoccTrm t /\ ~ PoccTrms args.
Proof.
  induction t; induction args; simpl; intros h; split; intuition; 
  try (solve [inversion H]);
  try (solve [inversion_Clear H; apply h;
               [apply PoAppA; assumption |
                apply PoAppR; assumption]]).
  - inversion_Clear H; apply h.
    + apply PoAppL. assumption.
    + apply PoAppA. assumption.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppL. assumption.
    + apply PoAppA. assumption.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoThd. assumption.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoTtl. assumption.
Qed.

Lemma Pocc_TApp:
  forall t arg args, PoccTrm (TApp t arg args) ->
     PoccTrm t \/ PoccTrm arg \/ PoccTrms args.
inversion 1; intuition.
Qed.

Lemma notPocc_TProd:
  forall n ty bod, ~ PoccTrm (TProd n ty bod) ->
                   ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TLambda:
  forall n ty bod, ~ PoccTrm (TLambda n ty bod) ->
                   ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TLetIn:
  forall n dfn ty bod, ~ PoccTrm (TLetIn n dfn ty bod) ->
                   ~ PoccTrm dfn /\ ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TCase:
  forall n ty mch brs, ~ PoccTrm (TCase n ty mch brs) ->
                   ~ PoccTrm ty /\ ~ PoccTrm mch /\ ~ PoccBrs brs.
intuition. 
Qed.

Lemma notPocc_TFix:
  forall ds m, ~ PoccTrm (TFix ds m) -> ~ PoccDefs ds.
intuition. 
Qed.

Lemma notPoccTrms:
  forall t ts, ~ PoccTrms (tcons t ts) -> ~ PoccTrm t /\ ~ PoccTrms ts.
intuition. 
Qed.

Lemma PoccTrms_tcons:
  forall t ts, PoccTrms (tcons t ts) -> PoccTrm t \/ PoccTrms ts.
inversion 1; intuition. 
Qed.

Lemma notPoccDefs:
  forall nm ty bod rarg ds, ~ PoccDefs (dcons nm ty bod rarg ds) ->
                            ~ PoccTrm ty /\ ~ PoccTrm bod /\ ~ PoccDefs ds.
intuition. 
Qed.

Lemma PoccTrms_append:
  forall ts1 ts2, PoccTrms (tappend ts1 ts2) -> PoccTrms ts1 \/ PoccTrms ts2.
  induction ts1; intros ts2 h. simpl in h.
  - right. assumption.
  - inversion_Clear h.
    + left. apply PoThd. assumption.
    + destruct (IHts1 _ H0).
      * left. apply PoTtl. assumption.
      * right. assumption.
Qed.


Lemma Pocc_mkApp_inv:
  forall fn args, PoccTrm (mkApp fn args) -> PoccTrm fn \/ PoccTrms args.
Proof.
  intros fn args.
  functional induction (mkApp fn args); simpl; intros h; intuition.
  - inversion_Clear h; intuition. 
    + destruct (PoccTrms_append_invrt _ _ H0). 
      * left. apply PoAppR. assumption.
      * right. assumption.
  - destruct (Pocc_TApp h); intuition.
Qed.

Lemma tIn_Pocc_Poccs:
  forall t ts us, tIn t ts -> PoccTrm t -> PoccTrms (tappend ts us).
induction ts; intros us h1 h2.
- inversion h1.
- inversion h1.
  + subst. simpl. apply PoThd. assumption.
  + simpl.  apply PoTtl. apply IHts; assumption.
Qed.

Lemma Pocc_fn_mkApp_lem:
  forall fn, PoccTrm fn -> forall args, PoccTrm (mkApp fn args).
Proof.
  induction 1;
    try (solve[destruct args; simpl;
       [constructor; assumption | repeat constructor; assumption]]).
  - simpl. intros brgs. apply PoAppR. apply PoccTrms_tappendl. assumption. 
Qed.

Lemma Pocc_TApp_mkApp:
  forall fn arg args, PoccTrm (TApp fn arg args) ->
    PoccTrm (mkApp fn (tcons arg args)).
Proof.
  inversion_clear 1.
  - apply Pocc_fn_mkApp_lem. assumption.
  - destruct (mkApp_isApp_lem fn arg args)
      as [x0 [x1 [x2 [h1 h2]]]].
    rewrite h1. destruct h2.
    + destruct H as [j1 [j2 [j3 j4]]]. subst. simpl.
      apply PoAppA. assumption.
    + destruct H as [j1 [j2 j3]]. apply PoAppR.
      eapply tIn_Pocc_Poccs; eassumption.
  - destruct (mkApp_isApp_lem fn arg args)
      as [x0 [x1 [x2 [h1 h2]]]].
    rewrite h1. destruct h2.
    + destruct H as [j1 [j2 [j3 j4]]]. subst. simpl.
      apply PoAppR. assumption.
    + destruct H. apply PoAppR. apply PoccTrms_tappendr. assumption.
Qed.

Lemma Pocc_TProof_mkProof:
  forall (t: Term), PoccTrm (TProof t) -> PoccTrm (mkProof t).
Proof.
  induction t; cbn; intros; try assumption.
  constructor. inversion_Clear H. inversion_Clear H1. assumption.
Qed.
                              
(*****************
Function fPocc (n:nat) (t:Term): bool :=
  match n with
    | 0 => false
    | S n =>
      match t with
        | TCast t ty => fPocc n t || fPocc n ty
        | TProd _ ty t => fPocc n t || fPocc n ty
        | TLambda _ ty t => fPocc n t || fPocc n ty
        | TLetIn _ dfn ty t => fPocc n dfn || fPocc n t || fPocc n ty
        | TApp fn arg args => fPocc n fn || fPocc n arg || fPoccs n args
        | TConst str => string_eq_bool str nm
        | TCase _ ty mch brs =>  fPocc n ty || fPocc n mch || fPoccBs n brs
        | TFix ds _ => fPoccDs n ds
        | _ => false
      end
  end
with fPoccs (n:nat) (ts:Terms): bool :=
       match n with
         | 0 => false
         | S n =>
           match ts with
             | tnil => false
             | tcons u us => fPocc n u || fPoccs n us
           end
       end
with fPoccBs (n:nat) (ds:Brs): bool :=
       match n with
         | 0 => false
         | S n =>
           match ds with
             | bnil => false
             | bcons _ u us => fPocc n u || fPoccBs n us
           end
       end
with fPoccDs (n:nat) (ds:Defs): bool :=
       match n with
         | 0 => false
         | S n =>
           match ds with
             | dnil => false
             | dcons _ u1 u2 _ us => fPocc n u1 || fPocc n u2 || fPoccDs n us
           end
       end.

Function fPocc_env (p:environ Term) : bool :=
  match p with
    | cons (_, ecTrm t) ps => fPocc 1000 t || fPocc_env ps
    | cons (_, ecTyp _ _ _) ps => fPocc_env ps
    | nil => false
  end.
****************************)

(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable (tin:Term).

Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| ISort: forall n srt, Instantiate n (TSort srt) (TSort srt)
| IPrf: forall n t it,
          Instantiate n t it -> Instantiate n (TProof t) (TProof it)
| ICast: forall n t ty it ity,
           Instantiate n t it -> Instantiate n ty ity ->
           Instantiate n (TCast t ty) (TCast it ity)
| IProd: forall n nm ty bod ibod ity,
             Instantiate (S n) bod ibod -> Instantiate n ty ity ->
             Instantiate n (TProd nm ty bod) (TProd nm ity ibod)
| ILambda: forall n nm ty bod ibod ity,
             Instantiate (S n) bod ibod -> Instantiate n ty ity ->
             Instantiate n (TLambda nm ty bod) (TLambda nm ity ibod)
| ILetIn: forall n nm dfn ty bod idfn ibod ity,
               Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
               Instantiate n ty ity -> 
               Instantiate n (TLetIn nm dfn ty bod) (TLetIn nm idfn ity ibod)
| IApp: forall n t a ts it ia its,
          Instantiate n t it -> Instantiate n a ia -> Instantiates n ts its ->
          Instantiate n (TApp t a ts) (mkApp it (tcons ia its))
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IAx: forall n t, Instantiate n (TAx t) (TAx t)
| IInd: forall n ind, Instantiate n (TInd ind) (TInd ind)
| IConstruct: forall n ind m1 np na,
      Instantiate n (TConstruct ind m1 np na) (TConstruct ind m1 np na)
| ICase: forall n np ty s ts is its ity,
           Instantiate n s is -> Instantiate n ty ity ->
           InstantiateBrs n ts its ->
           Instantiate n (TCase np ty s ts) (TCase np ity is its)
| IFix: forall n d m id, 
          InstantiateDefs (n + dlength d) d id ->
          Instantiate n (TFix d m) (TFix id m)
| IWrong: forall n s, Instantiate n (TWrong s) (TWrong s)
with Instantiates: nat -> Terms -> Terms -> Prop :=
| Inil: forall n, Instantiates n tnil tnil
| Icons: forall n t ts it its,
           Instantiate n t it -> Instantiates n ts its ->
           Instantiates n (tcons t ts) (tcons it its)
with InstantiateBrs: nat -> Brs -> Brs -> Prop :=
| Ibnil: forall n, InstantiateBrs n bnil bnil
| Ibcons: forall n m b bs ib ibs,
            Instantiate n b ib ->
            InstantiateBrs n bs ibs ->
            InstantiateBrs n (bcons m b bs) (bcons m ib ibs)
with InstantiateDefs: nat -> Defs -> Defs -> Prop :=
| Idnil: forall n, InstantiateDefs n dnil dnil
| Idcons: forall n nm ty bod rarg ds ity ibod ids,
            Instantiate n ty ity -> Instantiate n bod ibod ->
            InstantiateDefs n ds ids ->
            InstantiateDefs n (dcons nm ty bod rarg ds)
                            (dcons nm ity ibod rarg ids).
Hint Constructors Instantiate Instantiates InstantiateBrs InstantiateDefs.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with Instantiates_ind' := Induction for Instantiates Sort Prop
  with InstantiateBrs_ind' := Induction for InstantiateBrs Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstInstsBrsDefs_ind
         from Instantiate_ind', Instantiates_ind',
              InstantiateBrs_ind', InstantiateDefs_ind'.

Lemma InstantiateBrs_pres_blength:
  forall n bs ibs, InstantiateBrs n bs ibs -> blength bs = blength ibs.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma InstantiateDefs_pres_dlength:
  forall n ds ids, InstantiateDefs n ds ids -> dlength ds = dlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiate_pres_isLambda:
  forall t, isLambda t ->
            forall n it, Instantiate n t it -> isLambda it.
Proof.
  intros t ht n it hit. destruct ht as [x0 [x1 [x2 jx]]]. subst.
  inversion_Clear hit. auto.
Qed.          

Lemma Instantiates_no_gen:
  ~ PoccTrm tin ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, Instantiates n ts ss -> PoccTrms ss -> PoccTrms ts) /\
  (forall n ts ss, InstantiateBrs n ts ss -> PoccBrs ss -> PoccBrs ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstInstsBrsDefs_ind; intros; auto.
  - contradiction.
  - inversion H.
  - constructor. apply H. inversion_Clear H0. assumption.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoCastTy. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoProdTy. intuition.
  - inversion_Clear H1.
    + constructor. apply H. assumption.
    + apply PoLambdaTy. apply H0. assumption.
  - inversion_Clear H2.
    + constructor. apply H. assumption.
    + apply PoLetInBod. apply H0. assumption.
    + apply PoLetInTy. apply H1. assumption.
  - destruct (Pocc_mkApp_inv _ _ H2) as [hit | hiats]; intuition.
    inversion hiats; intuition.
  - inversion_Clear H2.
    + constructor.
    + constructor. apply H. assumption.
    + apply PoCaseR. apply H1. assumption.
    + apply PoCaseTy. apply H0. assumption.
  - inversion_Clear H0.
    + constructor. apply H. assumption.
  - inversion_Clear H1.
    + constructor. apply H. assumption.
    + apply PoTtl. apply H0. assumption.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoBtl. intuition. 
  - inversion_Clear H2.
    + constructor. intuition. 
    + apply PoDhd_bod. intuition. 
    + apply PoDtl. intuition. 
Qed.

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TProof t => TProof (instantiate n t)
    | TApp t a ts =>
      mkApp (instantiate n t) (tcons (instantiate n a) (instantiates n ts))
    | TLambda nm ty bod =>
      TLambda nm (instantiate n ty) (instantiate (S n) bod)
    | TProd nm ty bod => TProd nm (instantiate n ty) (instantiate (S n) bod)
    | TCase np ty s ts =>
      TCase np (instantiate n ty) (instantiate n s) (instantiateBrs n ts)
    | TLetIn nm tdef ty bod =>
      TLetIn nm (instantiate n tdef) (instantiate n ty) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TCast t ty => TCast (instantiate n t) (instantiate n ty)
    | x => x
  end
with instantiates (n:nat) (args:Terms) {struct args} : Terms :=
       match args with
         | tnil => tnil
         | tcons t ts => tcons (instantiate n t) (instantiates n ts)
       end
with instantiateBrs (n:nat) (bs:Brs) {struct bs} : Brs :=
       match bs with
         | bnil => bnil
         | bcons m t ts => bcons m (instantiate n t) (instantiateBrs n ts)
       end
with instantiateDefs (n:nat) (ds:Defs) {struct ds} : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm ty bod rarg ds =>
           dcons nm (instantiate n ty)
                 (instantiate n bod) rarg (instantiateDefs n ds)
       end.

(* Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop *)
(* with instantiates_ind' := Induction for instantiates Sort Prop *)
(* with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop. *)
(* Combined Scheme instantiateAll_ind *)
(*          from instantiate_ind', instantiates_ind', instantiateDefs_ind'. *)


Lemma instantiateDefs_pres_dlength:
  forall n ds, dlength ds = dlength (instantiateDefs n ds).
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

(******* Instantiate and instantiate are same relations **********)
Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, Instantiates n ts its -> instantiates n ts = its) /\
  (forall n ts its, InstantiateBrs n ts its -> instantiateBrs n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
apply InstInstsBrsDefs_ind; intros; simpl; intuition; try (subst; reflexivity).
- rewrite nat_compare_EQ. reflexivity.
- rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
- rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall ts n, Instantiates n ts (instantiates n ts)) /\
  (forall bs n, InstantiateBrs n bs (instantiateBrs n bs)) /\
  (forall (ds:Defs) n, InstantiateDefs n ds (instantiateDefs n ds)).
Proof.
  apply TrmTrmsBrsDefs_ind; intros; simpl; try (solve [constructor]);
  try (solve[constructor; intuition]).  
  - destruct (lt_eq_lt_dec n0 n) as [[h | h] | h].
    + rewrite (proj1 (nat_compare_lt _ _) h). apply IRelLt. assumption.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). subst. apply IRelEq.
    + rewrite (proj1 (nat_compare_gt _ _)). apply IRelGt.
      assumption. assumption.
Qed.


Lemma instant_pres_PoccTrm:
  (forall tbod, PoccTrm tbod -> forall n, PoccTrm (instantiate n tbod)) /\
  (forall ts, PoccTrms ts -> forall n, PoccTrms (instantiates n ts)) /\
  (forall bs, PoccBrs bs -> forall n, PoccBrs (instantiateBrs n bs)) /\
  (forall Ds, PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsBrsDefs_ind; intros; simpl; try solve [constructor; trivial].
  - eapply Pocc_TApp_mkApp. apply PoAppL. auto.
  - eapply Pocc_TApp_mkApp. apply PoAppA. auto. 
  - eapply Pocc_TApp_mkApp. apply PoAppR. auto. 
Qed.

End Instantiate_sec.
End PoccTrm_sec.


Lemma instantiate_pres_WFapp:
  (forall bod, WFapp bod ->
              forall t, WFapp t -> forall n, WFapp (instantiate t n bod)) /\
  (forall ts, WFapps ts ->
              forall t, WFapp t -> forall n, WFapps (instantiates t n ts)) /\
  (forall bs, WFappBs bs ->
              forall t, WFapp t -> forall n, WFappBs (instantiateBrs t n bs)) /\
  (forall ds, WFappDs ds ->
              forall t, WFapp t -> forall n, WFappDs (instantiateDefs t n ds)).
Proof.
  apply WFappTrmsBrsDefs_ind; intros;
  try (solve [unfold instantiate; constructor]).
  - destruct (lt_eq_lt_dec n m) as [[h|h]|h]; unfold instantiate.
    + rewrite (proj1 (nat_compare_lt _ _) h). constructor.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). assumption.
    + rewrite (proj1 (nat_compare_gt _ _) h). constructor.
  - cbn. constructor. apply H0. assumption.
  - change (WFapp (TCast (instantiate t n tm) (instantiate t n ty))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TProd nm (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TLambda nm (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TLetIn nm (instantiate t n dfn)
                          (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
    + apply H4. assumption.
  - change (WFapp (mkApp (instantiate t0 n fn) 
                         (tcons (instantiate t0 n t) (instantiates t0 n ts)))).
    apply mkApp_pres_WFapp.
    + constructor. apply H3; assumption. apply H5. assumption.
    + apply H1. assumption.
  - change (WFapp (TCase m (instantiate t n ty) (instantiate t n mch)
                         (instantiateBrs t n brs))).
    constructor.
    + apply H0; assumption.
    + apply H2; assumption.
    + apply H4; assumption.
  - change (WFapp (TFix (instantiateDefs t (n + dlength defs) defs) m)).
    constructor.
    + apply H0. assumption.
   - change (WFapps (tcons (instantiate t0 n t) (instantiates t0 n ts))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappBs (bcons n (instantiate t n0 b)
                            (instantiateBrs t n0 bs))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappDs (dcons nm (instantiate t n ty)
                            (instantiate t n bod) arg
                            (instantiateDefs t n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
     + apply H4. assumption.
Qed.


(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) (args:Terms) : Term :=
  mkApp (instantiate arg 0 bod) args.

Lemma whBetaStep_pres_WFapp:
  forall bod, WFapp bod -> forall arg, WFapp arg -> forall args, WFapps args ->
    WFapp (whBetaStep bod arg args).
Proof.
  intros bod hbod arg harg args hargs. unfold whBetaStep.
  apply mkApp_pres_WFapp. assumption.
  apply instantiate_pres_WFapp; assumption.
Qed.

Lemma whBetaStep_absorbs_mkApp:
  forall bod arg args brgs, 
    (mkApp (whBetaStep bod arg args) brgs) =
    whBetaStep bod arg (tappend args brgs).
Proof.
  intros. unfold whBetaStep. apply mkApp_idempotent.
Qed.


(****
Lemma not_isApp_whBetaStep:
  forall bod arg args, ~ isApp (whBetaStep bod arg args) ->
    args = tnil /\ ~ isApp (instantiate arg 0 bod).
induction bod; unfold whBetaStep; simpl; intros; split;
try not_isApp; destruct args; try reflexivity;
try (elim H; apply mkApp_isApp).
- unfold mkApp in H. destruct (instantiate arg 0 (TRel n)); try assumption.
******)


(***
Goal
  forall bod arg b bs, isApp (whBetaStep bod arg (tcons b bs)).
Proof.
  intros.
  change (isApp (whBetaStep bod arg (tappend tnil args))).
  rewrite <- whBetaStep_absorbs_mkApp.
***)


(*****
Lemma whBetaStep_noGen:
  forall nm t bod arg args, 
    PoccTrm nm t -> t = (whBetaStep bod arg args) ->
    PoccTrm nm bod \/ PoccTrm nm arg \/ PoccTrms nm args.
unfold whBetaStep. intros nm t bod arg args.
assert (j:= proj1 (instantiate_Instantiate arg)).

induction t.

unfold whBetaStep; simpl; induction 1; intros.
****)

Function whCaseStep (cstrNbr:nat) (ts:Terms) (brs:Brs): option Term :=
  match bnth cstrNbr brs with
    | Some (t, _) => Some (mkApp t ts)
    | None => None
  end.

Lemma whCaseStep_pres_WFapp:
  forall (brs:Brs), WFappBs brs -> forall ts, WFapps ts -> 
  forall (n:nat) (s:Term), whCaseStep n ts brs = Some s -> WFapp s.
Proof.
  intros brs hbrs ts hts n s h. unfold whCaseStep in h.
  case_eq (bnth n brs); intros; rewrite H in h.
  - destruct p. myInjection h. apply mkApp_pres_WFapp.
    + assumption.
    + eapply (bnth_pres_WFapp hbrs n). eassumption.
  - discriminate.
Qed.


(** Unfolding a Fixpoint **)
(** "dts" is a list of the mutual fixpoint definitions
*** "m" tells which of the definitions is being called
**)
Definition pre_whFixStep body dts args : Term :=
  let f := fold_left
             (fun bod ndx => instantiate (TFix dts ndx) 0 bod)
             (list_to_zero (dlength dts)) body in
  (mkApp f args).
Functional Scheme pre_whFixStep_ind := Induction for pre_whFixStep Sort Prop.

Lemma pre_whFixStep_absorbs_mkApp:
  forall bod dts args brgs,
    mkApp (pre_whFixStep bod dts args) brgs =
    pre_whFixStep bod dts (tappend args brgs).
Proof.
  intros. unfold pre_whFixStep. rewrite mkApp_idempotent. reflexivity.
Qed.

Lemma fold_left_pres_WFapp:
  forall (f:Term -> nat -> Term) (ns:list nat) (t:Term),
    (forall u, WFapp u -> forall n, WFapp (f u n)) ->
    WFapp t -> WFapp (fold_left f ns t).
Proof.
  intros f. induction ns; simpl; intros.
  - assumption.
  - apply IHns.
    + intros. apply H. assumption.
    + apply H. assumption.
Qed.

Lemma pre_whFixStep_pres_WFapp:
  forall  (bod:Term) (dts:Defs) (args:Terms),
    WFapp bod -> WFappDs dts -> WFapps args ->
        WFapp (pre_whFixStep bod dts args).
Proof.
  intros bod dts args hbod hdts hargs.
  unfold pre_whFixStep.
  apply mkApp_pres_WFapp. assumption.
  apply fold_left_pres_WFapp; try assumption.
  intros. apply instantiate_pres_WFapp.
  assumption. constructor. assumption.
Qed.
