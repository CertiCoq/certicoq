Require Import UsefulTypes.
Require Import list.
Require Import Coq.Lists.List.
Require Import tactics.
Require Import Omega.
Require Import universe.
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

Hint Rewrite diff_nil : fast.
Set Implicit Arguments.
Section AssociationList.
Variables Key Value : Type.
Definition AssocList : Type := list (Key * Value).
Definition ALDom : AssocList -> list Key := map (fun x => fst x).
Definition ALRange : AssocList -> list Value := map (fun x => snd x).

Theorem ALDomCombine :
  forall lv lnt,
    length lv = length lnt
    -> ALDom (combine lv lnt) = lv.
Proof.
  induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  f_equal; auto.
Qed.

Theorem ALRangeCombine :
  forall lv lnt,
    length lv = length lnt
    -> ALRange (combine lv lnt) = lnt.
Proof.
  induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  f_equal; auto.
Qed.

Lemma ALInEta : forall sub v t,
  LIn (v,t) sub -> (LIn v (ALDom sub)) # (LIn t (ALRange sub)).
Proof.
  induction sub as [| ? Hind]; introv Hin; auto.
  allsimpl. dorn Hin; subst; auto;[].
  apply IHHind in Hin. repnd.
  split; right; auto.
Qed.

Definition ALMap {TK TV : Type} 
  (fk : Key -> TK)
  (fv : Value -> TV) (al : AssocList):=
map (fun p => (fk (fst p), fv (snd p))) al.

Definition ALMapRange {T : Type} (f : Value -> T) (al : AssocList):=
ALMap (fun x=>x) f al.

Definition ALMapDom {T : Type} (f : Key -> T) (al : AssocList):=
ALMap f (fun x=>x)  al.

Require Import varInterface.
Context {deqKey : (Deq Key)}.
(** All definitions/lemmas below need decidable equality on Key.
    If not, they should placed before the line above *)
Fixpoint ALFind 
    (al : AssocList) (key : Key): option Value :=
match al with
| nil => None
| (k, v) :: xs => if (beq_var k key) 
                  then Some v 
                  else ALFind xs key
end.

Definition ALFindDef 
    (al : AssocList) (key : Key) (def: Value):  Value :=
match (ALFind al key) with
| Some v => v
| None => def
end.

(** Same as [AlFind] above, but the output contains proofs of
    correctness. *)
Lemma ALFind2 :
  forall  (sub: AssocList) (a : Key) ,
    { b: Value & LIn (a,b) sub}
    + !(LIn a (ALDom sub)).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - simpl. destruct (decideP (a=a')) as [Hc|Hc]; subst.
      + left. exists b'. left; refl.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. right; auto.
          * intro Hf. apply Hr. simpl in Hf. destruct (split sub).
              dorn Hf; sp.
Defined.

Definition ALFindDef2 
    (al : AssocList) (key : Key) (def: Value):  Value :=
match (ALFind2 al key) with
| inl (existT _ v _ ) => v
| inr _ => def
end.

(** In proofs, it is often convenient to replace
  [ALFindDef] with [ALFindDef2] so that we get some
  correctness hypotheses for free on destruction*)
Lemma ALFindDef2Same : forall
  (key : Key) (def: Value) (al : AssocList),
  ALFindDef al key def=ALFindDef2 al key def.
Proof.
  induction al as [|h th Hind]; auto;[]. destruct h as [k v].
  allunfold ALFindDef. allunfold ALFindDef2.
  simpl. setoid_rewrite decide_decideP.
  cases_ifd Hd; auto.
  - rw Hdt; auto. subst. rewrite deqP_refl. simpl. refl.
  - unfold ALFindDef2 in Hind.
    rw  Hind.  destruct_head_match; simpl; auto.
    destruct s; auto.
Abort.



Fixpoint ALFilter (sub : AssocList) (keys : list Key) : AssocList :=
  match sub with
  | nil => nil
  | (k, v) :: xs =>
      if (memvar k keys)
      then ALFilter xs keys
      else (k, v) :: ALFilter xs keys
  end.

Lemma ALFilter_nil_r :
  forall sub, ALFilter sub [] = sub.
Proof.
  induction sub; simpl; sp.
  rewrite IHsub; auto.
Qed.

Notation DeqKey := (fun (x y: Key) => decideP (x=y)).

Ltac dec :=
unfold beq_var in *;
unfold memvar in *;
(repeat rewrite decide_decideP);
(repeat rewrite memberb_din);
repeat match goal with
[H:context[decide _] |- _] => rewrite decide_decideP in H
|[H:context[memberb _ _ _] |- _] => rewrite memberb_din in H
end.

Lemma ALDomFilterCommute :
  forall l sub,
    diff l (ALDom sub) = ALDom (ALFilter sub l).
Proof.
  induction sub; simpl; sp; allsimpl.
  - apply diff_nil.
  - rewrite diff_cons_r. dec.
    cases_if; simpl; f_equal; auto.
Qed.

(* for some tactics like cpx *)


Ltac dest t :=
let tf := eval cbv beta in t in 
destruct tf.

Lemma ALFindSome :
  forall sub : AssocList,
  forall v : Key,
  forall u : Value,
    ALFind sub v = Some u
    -> LIn (v, u) sub.
Proof.
  induction sub; simpl; sp.
  setoid_rewrite decide_decideP in H.
  dest (DeqKey a0 v); subst; cpx.
  inverts H. cpx.
Qed.

Lemma ALFindNone :
  forall sub v,
    ALFind sub v = None
    -> ! LIn v (ALDom sub).
Proof.
  induction sub; simpl; sp;
  inversion H;
  setoid_rewrite decide_decideP in H;
  setoid_rewrite decide_decideP in H2;
  dest (DeqKey a0 v); cpx.
  apply IHsub in H0;  cpx.
Qed.


Lemma ALFind2Same : forall (sub: AssocList) v, ALFind sub v =
        proj_as_option (ALFind2 sub v).
Proof using.
  induction sub as [| a]; intros; auto; simpl. 
  destruct a. dec. dec.
  destruct (decideP (k = v));
  subst; autorewrite with SquiggleEq; simpl in *; auto.
  rewrite IHsub. destruct ((ALFind2 sub v)); simpl;
  try(destruct s; simpl); auto;
  destruct (decideP (v = k)); cpx.
Qed.



Lemma ALFindFilterSome :
  forall l v t sub,
    (ALFind (ALFilter sub l) v = Some t)
    <=> (ALFind sub v = Some t # ! LIn v l).
Proof.
  induction sub; simpl; sp; split; introv H; sp; allsimpl; dec.
  -  destruct (in_deq Key _ a0 l); allsimpl.
    + rw IHsub in H; sp;case_if as Hd; subst;auto; try contradiction.
    + dec.
       case_if as Hd; subst; auto; try contradiction.
      rw IHsub in H; exrepnd; auto.
  
  - destruct (in_deq Key _ a0 l); allsimpl.
    + apply IHsub in H; exrepnd; auto.
    + dec. dest (DeqKey a0 v); allsimpl; subst; sp;[].
      rw IHsub in H; exrepnd; auto.

  - destruct (in_deq Key _ a0 l); allsimpl.
    + apply IHsub; split; auto. dec.
      dest (DeqKey a0 v); allsimpl; subst; sp.

    + dec. dest (DeqKey a0 v); allsimpl; subst; sp.
       apply IHsub; split; auto.
Qed.

Lemma ALFindFilterNone :
  forall l v sub,
    (ALFind (ALFilter sub l) v = None)
    <=> (ALFind sub v = None [+] LIn v l).
  induction sub; simpl; sp; split; introv H; sp; allsimpl; dec.
  - destruct (in_deq Key _ a0 l); allsimpl; dec;
    dest (DeqKey a0 v); allsimpl;
    subst;
    try(rw IHsub in H); 
    exrepnd; auto;cpx.
  - destruct (in_deq Key _ a0 l); allsimpl;dec;
    dest (DeqKey a0 v); allsimpl;
    subst;cpx;apply IHsub; cpx.
  - dec. dest (in_deq Key _ a0 l); allsimpl; dec;
    dest (DeqKey a0 v); allsimpl;
    subst;cpx;apply IHsub; cpx.
Qed.

Lemma ALFilterSwap :
  forall l1 l2 sub,
    ALFilter (ALFilter sub l1) l2
    = ALFilter (ALFilter sub l2) l1.
Proof.
  induction sub; simpl; sp.
  allsimpl; cases_if as H1d; cases_if as H2d;
  allsimpl; try (rw H1d); try (rw H2d);
  cpx; try (rw IHsub); cpx.
Qed.

Lemma ALFilterAppR :
  forall sub vs1 vs2,
    ALFilter sub (vs1 ++ vs2)
    = ALFilter (ALFilter sub vs1) vs2.
Proof.
  induction sub; simpl; sp; dec.
  rw <- memberb_din.
  rw <- memberb_din.
  rw memberb_app.
  destructr (memberb _ a0 vs1) as [m1 | m1]; simpl.
  apply IHsub. unfold memvar.
  allsimpl. destruct (memberb _ a0 vs2) as [m2 | m2];
  simpl; subst;
  try(rw IHsub); auto.
Qed.

Lemma ALFilterAppAsDiff :
  forall sub l1 l2,
    ALFilter sub (l1 ++ l2)
    = ALFilter sub (l1 ++ diff l1 l2).
Proof.
  induction sub; simpl; sp; allsimpl;[].
  dec.
  cases_ifd  Hd; cases_ifd  Hdd; cpx;
  allrw in_app_iff;
  allrw in_diff.
  - provefalse. apply Hddf.
    dorn Hdt; cpx.
  - provefalse. apply Hdf.
    dorn Hddt; exrepnd; cpx.
  - f_equal. auto.
Qed.

(** [lv] is needs to make the induction
    hypothesis strong enough *)
Lemma ALFilterDom : forall  sub lv,
  ALFilter sub (lv++ALDom sub) =[].
Proof.
  induction sub as [|(v,u) sub Hind] ; introv ; auto;[].
  allsimpl; dec.
  cases_ifd Hd; cpx; allsimpl; allrw in_app_iff;
  cpx; dec.
  - rw cons_as_app. rw app_assoc. rw Hind; auto.
  - provefalse. apply Hdf. right. cpx.
Qed.

Fixpoint ALKeepFirst (sub : AssocList) (vars : list Key) : AssocList :=
match sub with
| nil => nil
| (v, t) :: xs =>
    if in_deq _ _ v vars
    then (v, t) :: ALKeepFirst
                   xs 
                   (diff [v] vars)
    else ALKeepFirst xs vars
end.

Lemma ALKeepFirstNil :
  forall sub,
    ALKeepFirst sub [] = [].
Proof.
  induction sub; simpl; sp.
Qed.


Lemma ALFindSomeKeepFirstSingleton:
  forall sub v t,
    ALFind sub v = Some t
    -> ALKeepFirst sub [v] = [(v,t)].
Proof.
  induction sub as [|(v,t) sub Hind];
  introv Heq; allsimpl; cpx. dec.
  dest (DeqKey v v0);
  subst;allsimpl; cpx.
  rewrite deqP_refl.
  rw ALKeepFirstNil; auto.
  inversion Heq.
  cpx.
  cases_if; cpx.
Qed.

Lemma ALFindNoneKeepFirstSingleton:
  forall sub v,
    ALFind sub v = None
    -> ALKeepFirst sub [v] = [].
Proof.
  induction sub as [|(v,t) sub Hind];
  introv Heq; allsimpl; cpx.
  dec.
  dest (DeqKey v v0);
  subst;allsimpl; cpx.
  cases_if; cpx.
Qed.
Hint Rewrite ALKeepFirstNil ALFilterDom ALFilter_nil_r : fast.

Ltac cpx :=
  repeat match goal with
           (* false hypothesis *)
           | [ H : [] = snoc _ _ |- _ ] =>
             complete (apply nil_snoc_false in H; sp)
           | [ H : snoc _ _ = [] |- _ ] =>
             complete (symmetry in H; apply nil_snoc_false in H; sp)

           (* simplifications *)
           | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; GC

           | [ H : Some _ = Some _ |- _ ] => inversion H; subst; GC
           | [ H : Some _ = None |- _ ] => inversion H; GC
           | [ H : None = Some _ |- _ ] => inversion H; GC

           | [ H : 0 = length _ |- _ ] =>
             symmetry in H; trw_h length0 H; subst
           | [ H : length _ = 0 |- _ ] =>
             trw_h length0 H; subst

           | [ H : 1 = length _ |- _ ] =>
             symmetry in H; trw_h length1 H; exrepd; subst
           | [ H : length _ = 1 |- _ ] =>
             trw_h length1 H; exrepd; subst

           | [ H : [_] = snoc _ _ |- _ ] =>
             symmetry in H; trw_h snoc1 H; repd; subst
           | [ H : snoc _ _ = [_] |- _ ] =>
             trw_h snoc1 H; repd; subst

           | [ H : context[length (snoc _ _)] |- _ ] =>
             rewrite length_snoc in H
         end;
  inj;
  try (complete (allsimpl; sp)).

Lemma ALKeepFirstLin:
  forall sub v vs t,
    LIn (v,t) (ALKeepFirst sub vs)
    <=> (ALFind sub v = Some t # LIn v vs).
Proof.
  induction sub; simpl; sp;[split;sp|]. dec.
  dest (DeqKey a0 v);
  destruct (in_deq Key _ a0 vs);
  subst; cpx; split; introns Hyp; allsimpl; exrepnd; cpx.
  - dec. dorn Hyp; cpx; cpx. apply IHsub in Hyp.
    exrepnd.
    apply in_remove in Hyp; cpx.
  - dec. cpx.
     apply IHsub in Hyp; exrepnd; cpx.
  - dorn Hyp; cpx. apply IHsub in Hyp.
    exrepnd.
    apply in_remove in Hyp; cpx.
  - right. apply IHsub; dands; cpx.
    apply in_remove; dands; cpx.
Qed.

Lemma ALKeepFirstLinApp:
  forall sub v vs vss t,
    LIn (v,t) (ALKeepFirst sub (vs))
    -> LIn (v,t) (ALKeepFirst sub (vs++ vss)).
Proof.
  introv X.
  apply ALKeepFirstLin in X.
  apply ALKeepFirstLin.
  exrepnd; dands; auto.
  apply in_app_iff.
  cpx.
Qed.

Lemma ALFilterLIn :
  forall v t sub vars,
    LIn (v, t) (ALFilter sub vars)
    <=>
    (
      LIn (v, t) sub
      #
      ! LIn v vars
    ).
Proof.
  induction sub; simpl; sp; dec.
  split; sp. cases_if;
  simpl; allrw; split; sp; cpx.
Qed.

Lemma ALFilterSubset :
  forall sub vars,
    subset (ALFilter sub vars) sub.
Proof.
  introv Hin.
  destruct x;
  rw ALFilterLIn in Hin; cpx.
Qed.

Lemma ALKeepFirstSubst :
  forall sub vars,
    subset (ALKeepFirst sub vars) sub.
Proof.
  introv Hin.
  destruct x;
  rw ALKeepFirstLin in Hin; exrepnd;
  cpx.
  apply ALFindSome; cpx.
Qed.

Hint Resolve ALFilterSubset ALKeepFirstSubst :
  SetReasoning.

Lemma ALKeepFirstAppLin:
  forall lv1 lv2 sub v u,
  LIn (v,u) (ALKeepFirst sub (lv1++lv2))
  -> LIn (v,u) (ALKeepFirst sub lv1) [+]
     LIn (v,u) (ALKeepFirst sub lv2). 
Proof. introv Hin.
  apply ALKeepFirstLin in Hin.
  repnd.
  apply in_app_iff in Hin. dorn Hin;[left|right];
  apply ALKeepFirstLin;sp.
Qed.

Lemma ALKeepFirstFilterDiff:
forall sub lvk lvf,
  (ALKeepFirst  sub (diff lvf lvk))
  = 
  (ALKeepFirst (ALFilter sub lvf) lvk).
Proof.
  induction sub; allsimpl;
  autorewrite with fast; cpx; dec;[].
  intros. allsimpl.
  destruct a. dec.
  cases_ifd H1d; cases_ifd H2d;
   allrw in_diff; exrepnd; allsimpl; cpx.
  - cases_ifd H3d; cpx. f_equal.
    rw <- diff_remove. apply IHsub.
  - cases_ifd H3d; cpx. provefalse.
    apply H1df. dands;cpx.
Qed.


Lemma ALFilterAppSub :
  forall sub1 sub2 l,
  ALFilter (sub1++sub2) l
  = (ALFilter sub1 l)++(ALFilter sub2 l).
Proof.
  induction sub1; simpl; sp;[].
  rw IHsub1.
  cases_ifd Hd; cpx.
Qed.

Lemma ALFindApp :
  forall v sub1 sub2,
    ALFind (sub1 ++ sub2) v
    = match ALFind sub1 v with
        | Some t => Some t
        | None => ALFind sub2 v
      end.
Proof.
  induction sub1; simpl; sp.
  cases_if; auto.
Qed.


Lemma ALFindRangeMapSome :
  forall v t sub f,
    ALFind sub v = Some t
    -> ALFind (ALMapRange f sub) v 
        = Some (f t).
Proof.
  induction sub; simpl; sp; allsimpl;[].
  cases_ifd Hd; cpx.
Qed.
  
Lemma ALFindRangeMapNone :
  forall v sub f,
    ALFind sub v = None
    -> ALFind (ALMapRange f sub) v = None.
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_ifd Hd; cpx.
Qed.

Fixpoint ALRangeRel  (R : Value -> Value-> [univ]) 
    (subl subr : AssocList) : [univ] :=
match (subl, subr) with 
| ([],[]) => True
| ((vl,tl) :: sl , (vr,tr) :: sr) => (vl=vr # R tl tr # ALRangeRel R sl sr)
| ( _ , _) => False
end.


Lemma ALRangeRelApp : forall R subl1 subl2 subr1 subr2,
  (ALRangeRel  R subl1 subl2 # ALRangeRel R subr1 subr2)
  ->   ALRangeRel R (subl1 ++ subr1)  (subl2 ++ subr2).
Proof.
  induction subl1 as [|(v1,t1) subl1 Hind]; introv Hsr;
  destruct subl2 as [|(v2,t2) subl2]; inverts Hsr; allsimpl;sp.
Qed.

Lemma ALRangeRelRefl : forall R,
  refl_rel R -> refl_rel (ALRangeRel R).
Proof.
  introv Hr. unfold refl_rel in Hr. unfold refl_rel.
  induction x as [|(v1,t1) subl1 Hind];  allsimpl;sp.
Qed.
  
Lemma ALRangeRelSameDom : forall R 
  (subl subr : AssocList),
  ALRangeRel R subl subr
  -> ALDom subl = ALDom subr.
Proof.
  induction subl as [| (kl,vl) subl Hind]; introv Hal;
  destruct subr as [| (kr,vr) subr]; allsimpl; repnd; dands; cpx.
  f_equal; cpx.
Qed.

Lemma ALRangeRelFind : forall R 
  (subl subr : AssocList) k t,
  ALRangeRel R subl subr
  -> ALFind subl k = Some t
  -> { tr : Value & ALFind subr k = Some tr # R t tr}.
Proof.
  induction subl as [| (kl,vl) subl Hind]; cpx; introv HAl Hf.
  allsimpl. destruct subr as [| (kr,vr) subr]; cpx;[].
  allsimpl. repnd. subst.
  cases_ifd Hd; cpx.
  eexists; eauto.
Qed.

Lemma ALRangeRelFilter : forall R 
  (subl subr : AssocList) l,
  ALRangeRel R subl subr
  ->  ALRangeRel R
        (ALFilter  subl l) 
        (ALFilter  subr l).
Proof.
  induction subl as [| (kl,vl) subl Hind]; introv Hal;
  destruct subr as [| (kr,vr) subr]; allsimpl; repnd; dands; subst; cpx.
  cases_if; cpx.
Qed.

(* hints should be placed (again) after this line.
  the ones in the section get deactivated
 *)
End AssociationList.
Hint Rewrite ALKeepFirstNil ALFilterDom ALFilter_nil_r 
  ALRangeCombine ALDomCombine: fast.

Hint Resolve ALFilterSubset ALKeepFirstSubst :
  SetReasoning.

Definition ALSwitch {K V} (sub : AssocList K V)  : AssocList V K :=
  map (fun x => (snd x, fst x)) sub.

Lemma ALSwitchCombine : forall {K V} (lv: list V) (lk : list K) ,
  combine lv lk = ALSwitch (combine lk lv).
Proof.
  induction lv; allsimpl.
  - destruct lk; cpx.
  - destruct lk; cpx.
    allsimpl. f_equal. cpx.
Qed.

Lemma ALMapRangeFilterCommute :
  forall K V l T (deq : Deq K) (f: V -> T) (sub : AssocList K V),
  (ALFilter (ALMapRange f sub) l)  = ALMapRange f (ALFilter sub l).
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_if; simpl; auto; f_equal; auto.
Qed.

Ltac dec :=
unfold beq_var in *;
(repeat rewrite decide_decideP);
(repeat rewrite memberb_din);
repeat match goal with
[H:context[decide _] |- _] => rewrite decide_decideP in H
|[H:context[memberb _ _ _] |- _] => rewrite memberb_din in H
end.




Lemma ALFindMapSome :
  forall {KA KB VA VB : Type} 
    (DKA : Deq KA)
    (DKB : Deq KB)
    (fk : KA -> KB)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v t, ALFind sub v = Some t
  -> ALFind  (ALMap fk fv sub) (fk v) 
        = Some (fv t).
Proof.
  introv Hik.
  induction sub;simpl; introv Heq; sp; allsimpl;[].
  dec.
  cases_ifd Hd; cpx.
  + f_equal. apply Hik in Hdt.
    destruct Hdt. rewrite deqP_refl in Heq.
    invertsn Heq. refl.
  + apply IHsub. revert Heq. cases_ifd Hdd;
    subst; cpx.
Qed.

Lemma ALFindMapNone :
  forall {KA KB VA VB : Type} 
    (DKA : Deq KA)
    (DKB : Deq KB)
    (fk : KA -> KB)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v, ALFind  sub v = None
  -> ALFind (ALMap fk fv sub) (fk v) 
        = None.
Proof.
  introv Hik.
  induction sub;simpl; introv Heq; sp; allsimpl;[].
  dec.
  cases_ifd Hd; cpx.
  + f_equal. apply Hik in Hdt.
    destruct Hdt. rewrite deqP_refl in Heq.
    invertsn Heq. 
  + apply IHsub. revert Heq. cases_ifd Hdd;
    subst; cpx.
Qed.

Lemma ALFindEndoMapSome :
  forall {KA VA VB: Type} 
    (DKA : Deq KA)
    (fk : KA -> KA)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) 
      v, ALFind sub v = None
  -> ALFind (ALMap fk fv sub) (fk v) 
        = None.
Proof.
  intros. eapply ALFindMapNone; eauto.
Qed.

Lemma ALMapFilterCommute :
  forall {KA KB VA VB : Type} 
  (DKA : Deq KA)
  (DKB : Deq KB)
  (fk : KA -> KB)
  (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) l,
      (ALFilter  (ALMap fk fv sub) (map fk l))  
          = ALMap fk fv (ALFilter  sub l).
Proof.
  introv Hin.
  induction sub; simpl; sp; allsimpl;
  dec. dec.
  cases_ifd Hd; cases_ifd Hc;
    simpl; auto; f_equal; auto.
  - dec. apply in_map_iff in Hdt. exrepnd. apply Hin in Hdt1.
    subst. cpx.
  - rw in_map_iff in Hdf. provefalse.
    apply Hdf. eexists; eauto.
Qed.

(** endo maps avoid the need to provide another
    decider for keys *)
Lemma ALEndoMapFilterCommute :
  forall {KA VA VB : Type} 
  (DKA : Deq KA)
  (fk : KA -> KA)
  (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) l,
      (ALFilter  (ALMap fk fv sub) (map fk l))  
          = ALMap fk fv (ALFilter  sub l).
Proof.
  intros. apply ALMapFilterCommute; auto.
Qed.

Lemma ALMapRangeFindCommute :
  forall K V T (v: K) (deq : Deq K) (f: V -> T) (sub : AssocList K V),
  (ALFind  (ALMapRange f sub) v)  = option_map f (ALFind  sub v).
Proof.
  induction sub; simpl; sp; allsimpl.
  cases_if; simpl; auto; f_equal; auto.
Qed.

(* Move *)
Ltac dALFind sn :=
  match goal with
    | [  |- context[ALFind ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (ALFind s v) as sn;
        destruct sn as [sns |]
    | [ H: context[ALFind ?s ?v] |- _ ] =>
      let sns := fresh sn "s" in
      remember (ALFind s v) as sn;
        destruct sn as [sns |]
  end.


Lemma ALMapCombine :
  forall {KA KB VA VB : Type} 
    (fk : KA -> KB)
    (fv : VA -> VB) ka va,
  ALMap fk fv (combine ka va)
  = (combine (map fk ka) (map fv va)).
Proof using.
  induction ka; intros ?; eauto.
  simpl.
  destruct va; auto.
  unfold ALMap. simpl.
  f_equal. eauto.
Qed.

Lemma ALFindMap2 :
  forall {KA KB VA VB : Type} 
    {DKA : Deq KA}
    {DKB : Deq KB}
    (fk : KA -> KB)
    (fv : VA -> VB),
  forall (sub : AssocList KA VA) k,
  (forall s, In s sub -> fk (fst s) = fk k -> fst s = k)
  -> ALFind  (ALMap fk fv sub) (fk k) = option_map fv (ALFind  sub k).
Proof using.
  clear.
  introv Hik.
  induction sub;simpl; sp; allsimpl;[].
  dec.
  cases_ifd Hd; cpx.
  + specialize (Hik _ (or_introl eq_refl)). symmetry in Hdt.
    simpl in Hik. symmetry in Hdt.
    apply Hik in Hdt. subst.
    rewrite deqP_refl. refl.
  + rewrite IHsub. 
    * clear IHsub. dec. cases_if as Hd;
      subst; cpx.
    * intros ? ?. apply Hik. cpx.
Qed.

Lemma ALFindMap :
  forall {KA KB VA VB : Type} 
    {DKA : Deq KA}
    {DKB : Deq KB}
    (fk : KA -> KB)
    (fv : VA -> VB),
  injective_fun fk
  -> forall (sub : AssocList KA VA) k,
  ALFind  (ALMap fk fv sub) (fk k) = option_map fv (ALFind  sub k).
Proof using.
  introv Hik. intros. apply ALFindMap2.
  intros ? ?. apply Hik.
Qed.


Lemma ALFindNoneIf {KA VA : Type} 
    {DKA : Deq KA} :
  forall k (sub: AssocList KA VA),
  (not (In k (ALDom sub))) -> ALFind  sub k = None.
Proof using.
  intros ? ? ?.
  dALFind ss;[| refl].
  provefalse.
  symmetry in Heqss.
  apply ALFindSome in Heqss.
  apply ALInEta in Heqss. tauto.
Qed.

Notation lmap := AssocList.

(*this is slightly different from ALFind2*)
Lemma lmap_find :
  forall {A B: Type}
         (eqdec: Deq A) (sub: lmap A B) (a : A) ,
    { b: B & LIn (a,b) sub}
    + !(LIn a (fst (split sub))).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - destruct (decideP (a'= a)) as [Hc|Hc]; subst.
      + left. exists b'. left; refl.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. right; auto.
          * intro Hf. apply Hr. simpl in Hf. destruct (split sub).
              dorn Hf; sp.
Defined.

Notation dom_lmap := ALDom.



(**same as above, but the impelemtation is guaranteed to return the first match*)
Lemma lmap_find_first: forall {A B: Type}
  (eqdec: Deq A) (sub: lmap A B) (a : A) ,
    { b: B & {n:nat & n < length sub
            # nth n sub (a,b) = (a,b)
            # (forall m, m<n ->  (nth m (dom_lmap sub) a) <> a) } }
       + !LIn a (dom_lmap sub).
Proof.
   induction sub as [| (a', b') sub Hind]; intro a.
   - right.  sp.
   - destruct (decideP (a'=a)) as [Hc|Hc]; subst.
      + left. exists b'. exists 0. split; simpl; auto. apply  lt_0_Sn.
        split; auto. introv Hm; inverts Hm.
      + destruct (Hind a) as [Hl | Hr]; exrepnd ;[left | right].
          * exists b. exists (S n). repeat(split); auto; simpl. apply lt_n_S. auto.
            introv Hlt. destruct m; auto. apply Hl1. apply lt_S_n; auto.
          * introv Hf. apply Hr. simpl in Hf. 
              dorn Hf; sp. 
Defined.

