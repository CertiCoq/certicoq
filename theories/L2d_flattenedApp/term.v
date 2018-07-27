(*** type fields are stripped from term notations ***)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import FunInd Coq.omega.Omega.
Require Import Common.Common.  (* shared namespace *)
Require Import L2.L2.
Require Import L2d.compile.

Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.


(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => "(Rel " ++ (nat_to_string n) ++ ")"
    | TProof => "(PRF)"
    | TLambda nm t => "(LAM "++ (print_name nm) ++ "[" ++ print_term t ++ "])"
    | TLetIn nm _ _ => "(LET " ++ (print_name nm) ++ ")"
    | TApp fn arg =>
      "(" ++ (print_term fn) ++ " @ " ++ (print_term arg) ++ ")"
    | TConst s => "[" ++ s ++ "]"
    | TConstruct i n _ _  =>
      "(CSTR " ++ (print_inductive i) ++ " " ++ (nat_to_string n) ++ ")"
    | TCase i mch _ =>
      "(CASE:" ++ (print_inductive (fst i)) ++ " " ++ (print_term mch) ++ ")"
    | TFix _ n => "(FIX " ++ (nat_to_string n) ++ ") "
    | TWrong str => ("(TWrong:" ++ str ++ ")")
    | TDummy str => ("(Dummy:" ++ str ++ ")")
  end.

Inductive shape : Set :=
  | sRel | sProof | sLambda | sLetIn | sApp | sConst | sInd | sConstruct
  | sCase | sFix | sWrong | sDummy.

Definition Term_shape (t:Term) : shape :=
  match t with
    | TRel _ => sRel
    | TProof => sProof
    | TLambda _ _ => sLambda
    | TLetIn _ _ _ => sLetIn
    | TApp _ _ => sApp
    | TConst _ => sConst
    | TConstruct _ _ _ _  => sConstruct
    | TCase _ _ _ => sCase
    | TFix _ _ => sFix
    | TWrong _ => sWrong
    | TDummy _ => sDummy
  end.

Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (ss tt:Terms), ss = tt \/ ss <> tt) /\
  (forall (ss tt:Brs), ss = tt \/ ss <> tt) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsBrsDefs_ind; intros.
  - induction t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - induction t; cross. lft.
  - induction t0; cross.
    destruct (name_dec n n0); destruct (H t0); [lft | rght ..]. 
  - induction t1; cross.
    destruct (name_dec n n0); destruct (H t1_1); destruct (H0 t1_2); 
    [lft | rght ..]. 
  - induction t1; cross.
    destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..].
  - induction t; cross. destruct (string_dec s s0); [lft | rght].
  - induction t; cross.
    destruct (inductive_dec i i0), (eq_nat_dec n n2),
      (eq_nat_dec n0 n3), (eq_nat_dec n1 n4); [lft | rght .. ].
  - destruct t0; cross.
    destruct p as [i n], p0 as [i0 n0];
    destruct (eq_nat_dec n n0), (inductive_dec i i0);
    destruct (H t0), (H0 b0); [lft | rght .. ].
  - induction t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght .. ].
  - induction t; cross.
    destruct (string_dec s s0); [lft | rght].
  - destruct tt; cross; lft.
  - destruct tt; cross.
    destruct (H t1), (H0 tt); [lft | rght .. ].
  - destruct tt; cross; lft.
  - destruct tt; cross.
    destruct (eq_nat_dec n n0), (H t0), (H0 tt); [lft | rght .. ].
  - induction ee; cross. lft.
  - induction ee; cross.
    destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
    destruct (H t0); destruct (H0 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.

Definition Term_dec := proj1 TermTerms_dec.
Definition Terms_dec := proj1 (proj2 TermTerms_dec).


Fixpoint TrmSize (t:Term) {struct t} : nat :=
  match t with
    | TLambda _ bod => S (TrmSize bod)
    | TLetIn _ dfn bod => S (TrmSize dfn + TrmSize bod)
    | TApp fn a => S (TrmSize fn + TrmSize a)
    | TCase _ mch brs => S (TrmSize mch + TrmBsSize brs)
    | TFix ds n => S (TrmDsSize ds)
    | _ => S 0
  end
with TrmBsSize (ts:Brs) {struct ts} : nat :=
  match ts with
    | bnil => 1
    | bcons _ s ss => S (TrmSize s + TrmBsSize ss)
  end
with TrmDsSize (ds:Defs) : nat :=
  match ds with
    | dnil => 1
    | dcons _ t2 _ es => S (TrmSize t2 + TrmDsSize es)
  end.


Definition isRel (t:Term) : Prop := exists n, t = TRel n.

Definition isLambda (t:Term) : Prop :=
  exists nm bod, t = TLambda nm bod.
Lemma IsLambda: forall nm bod, isLambda (TLambda nm bod).
intros. exists nm, bod. reflexivity.
Qed.
Hint Resolve IsLambda.

Lemma isLambda_dec: forall t, {isLambda t}+{~ isLambda t}.
induction t;
  try (solve [right; intros h; unfold isLambda in h;
              elim h; intros x h1; elim h1; intros x0 h2; discriminate]).
left. auto.
Qed.

Definition isCase (t:Term) : Prop :=
  exists xn mch ds, t = TCase xn mch ds.

Lemma isCase_dec: forall t, {isCase t}+{~ isCase t}.
Proof.
  destruct t; try (solve[right; not_isCase]).
  left. unfold isCase. exists p, t, b. reflexivity.
Qed.
Lemma IsCase: forall xn mch ds, isCase (TCase xn mch ds).
Proof.
  intros. exists xn, mch, ds. reflexivity.
Qed.
  
Definition isApp (t:Term) : Prop :=
  exists fn arg, t = TApp fn arg.
Lemma IsApp: forall fn arg, isApp (TApp fn arg).
intros. exists fn, arg. reflexivity.
Qed.
Hint Resolve IsApp.
Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
Proof.
  destruct t; try (right; not_isn).
  left. auto.
Qed.

Definition isFix (t:Term) : Prop :=
  exists ds n, t = TFix ds n.
Lemma IsFix: forall ds n, isFix (TFix ds n).
intros. exists ds, n. reflexivity.
Qed.
Hint Resolve IsFix.
Lemma isFix_dec: forall t, {isFix t}+{~ isFix t}.
Proof.
  induction t;
  try (solve [right; intros h; unfold isFix in h;
              elim h; intros x h1; elim h1; intros x0 h2; discriminate]).
  left. auto.
Qed.

Definition isProof (t:Term) : Prop := t = TProof.
Lemma IsProof: isProof TProof.
intros. reflexivity.
Qed.
Hint Resolve IsProof.
Lemma isProof_dec: forall t, {isProof t}+{~ isProof t}.
Proof.
  destruct t;
  try (right; intros h; red in h; discriminate).
  - left. auto.
Defined.

Definition isWrong t : Prop := exists s, t = TWrong s.
Lemma isWrong_dec: forall t, {isWrong t}+{~ isWrong t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. exists s. reflexivity.
Defined.

Definition isDummy t : Prop := exists s, t = TDummy s.
Lemma isDummy_dec: forall t, {isDummy t}+{~ isDummy t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. exists s. reflexivity.
Defined.

Definition isConstruct (t:Term) : Prop :=
  exists i n np na, t = TConstruct i n np na.
Lemma isConstruct_dec: forall t, {isConstruct t}+{~ isConstruct t}.
Proof.
  destruct t; try (right; not_isn).
  - left. exists i, n, n0, n1. reflexivity.
Qed.

Inductive isCanonical : Term -> Prop :=
| canC: forall (i:inductive) (n np na:nat),
    isCanonical (TConstruct i n np na)
| canA: forall fn t, isCanonical fn -> isCanonical (TApp fn t).
Hint Constructors isCanonical.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
Proof.
  induction t; try (right; intros h; inversion h; inversion H;
                           destruct H1; discriminate).
  - destruct IHt1.
    + left. constructor. assumption.
    + right. intros h. inversion_clear h. contradiction.
  - left. constructor.
Qed.
          
Function canonicalP (t:Term) : option (nat * Terms) :=
  match t with
    | TConstruct _ r _ _ => Some (r, tnil)
    | TApp fn arg =>
      match canonicalP fn with
      | Some (r, args) => Some (r, tappend args (tunit arg))
      | None => None
      end
    | _ => None
  end.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Some x -> isCanonical t.
Proof.
 induction t; simpl; intros; try discriminate.
  - destruct (canonicalP t1).
    + constructor. eapply IHt1. reflexivity.
    + discriminate. 
  - constructor.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x args, canonicalP t = Some (x, args).
Proof.
  induction 1; simpl.
  - exists n, tnil. reflexivity.
  - destruct IHisCanonical as [x0 [x1 jx]].
    exists x0, (tappend x1 (tunit t)). rewrite jx. reflexivity.
Qed.

Function CanonicalP (t:Term): option (inductive * nat * nat * nat * Terms) :=
  match t with
    | TConstruct i r np na => Some (i, r, np, na, tnil)
    | TApp fn arg =>
      match CanonicalP fn with
      | Some (i, r, np, na, args) =>
        Some (i, r, np, na, tappend args (tunit arg))
      | None => None
      end
    | _ => None
  end.

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

Lemma tappend_assoc:
  forall xts yts zts,
       (tappend xts (tappend yts zts)) = (tappend (tappend xts yts) zts).
  induction xts; intros yts zts; simpl.
  - reflexivity.
  - rewrite IHxts. reflexivity.
Qed.

Lemma tappend_cons_lem:
  forall ys t zs,
    tappend ys (tcons t zs) = tappend (tappend ys (tcons t tnil)) zs.
Proof.
  induction ys; intros tt zzs; simpl.
  - reflexivity.
  - rewrite IHys. reflexivity.
Qed.
  
Lemma tappend_tappend_lem:
  forall xts yts t zts,
       (tappend xts (tappend yts (tcons t zts))) =
       (tappend (tappend xts (tappend yts (tunit t))) zts).
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

Lemma pre_tappend_tcons_tunit:
  forall bs cs x,
    tappend bs (tcons x cs) = tappend (tappend bs (tunit x)) cs.
Proof.
  induction bs; intros.
  - reflexivity.
  - cbn. rewrite IHbs. reflexivity.
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

Lemma tappend_pres_tlength:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L2.compile.tappend ts us) = tappend (strips ts) (strips us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  rewrite IHts. reflexivity.
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

Lemma treverse_terms_ind:
 forall (P : Terms -> Prop),
       P tnil ->
       (forall (a: Term) (l:Terms),
           P (treverse l) -> P (treverse (tcons a l))) ->
       forall l:Terms, P (treverse l).
Proof.
  intros. induction l.
  - cbn. assumption.
  - eapply H0. assumption.
Qed.

Lemma treverse_ind:
  forall (P: Terms -> Prop),
    P tnil ->
    (forall (x: Term) (l: Terms), P l -> P (tappend l (tunit x))) ->
    forall l: Terms, P l.
Proof.
  intros.
  assert (j: treverse (treverse l) = l). apply treverse_involutive.
  rewrite <-j.
  apply treverse_terms_ind.
  - assumption.
  - intros. cbn. apply H0. assumption.
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

Function tnth (n:nat) (l:Terms) {struct l} : option Term :=
  match l with
    | tnil => None
    | tcons x xs => match n with
                      | 0 => Some x
                      | S m => tnth m xs
                    end
  end.

Lemma tlast_tappend:
  forall ts t x,
    tlast t (tappend ts (tunit x)) = (tcons t ts, x).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. repeat (apply f_equal2; try reflexivity). 
Qed.

(*************************
Lemma AppMk_tunit:
  forall fn u, 
    AppMk fn (tunit u) = TApp fn u.
Proof.
  intros. destruct fn; try reflexivity.
  - elim H0. exists s. reflexivity.
  - elim H. reflexivity.
Qed.

Goal
  forall us u fn,
        fn <> TDummy -> ~ isWrong fn ->
        AppMk fn (tcons u us) = AppMk (TApp fn u) us.
Proof.
  induction us; intros.
  - rewrite AppMk_tunit; try assumption. reflexivity.
  -


      Goal
  forall us fn u,
     fn <> TDummy -> ~ isWrong fn ->
     mkApp fn (tappend us (tunit u)) = TApp (AppMk fn us) u.
Proof.
  induction us; intros.
  - cbn. rewrite AppMk_tnil; try assumption. destruct fn; try reflexivity.
    + elim H0. exists s. reflexivity.
    + elim H. reflexivity.
  - cbn.

    destruct (isDummy_dec fn).
    + subst. destruct H. reflexivity.
    + destruct (isWrong_dec fn).
      * destruct i as [x0 jx]. subst. elim H0. exists x0. reflexivity.
      * cbn.




        Goal
  forall us fn u,
     fn <> TDummy -> ~ isWrong fn ->
     AppMk fn (tappend us (tunit u)) = TApp (AppMk fn us) u.
Proof.
  induction us using treverse_ind; intros.
  - cbn. rewrite AppMk_tnil. apply AppMk_tunit; assumption.
  - rewrite <- tappend_assoc. cbn.

    destruct (isDummy_dec fn).
    + subst. destruct H. reflexivity.
    + destruct (isWrong_dec fn).
      * destruct i as [x0 jx]. subst. elim H0. exists x0. reflexivity.
      * cbn.


    cbn. reflexivity.  HERE
  
Goal
  forall args fn t,
    fn <> TDummy -> ~ isWrong fn ->
    AppMk (TApp fn t) args = AppMk fn (tcons t args).
Proof.
  induction args; intros.
  - unfold AppMk at 1. unfold AppMk; destruct fn; try reflexivity.
    + elim H0. exists s. reflexivity.
    + elim H. reflexivity.
  -



    
  induction args using treverse_ind; intros.
  - cbn. destruct fn; try reflexivity.
    + elim H0. exists s. reflexivity.
    + elim H. reflexivity.
  - destruct args.
    + cbn. unfold AppMk. destruct fn; try reflexivity.
      * elim H0. exists s. reflexivity.
      * elim H. reflexivity.
    + change
        (AppMk (TApp fn t) (tcons t0 (tappend args (tunit x))) =
         AppMk fn (tcons t (tcons t0 (tappend args (tunit x))))).



  - destruct fn; try reflexivity.
    + elim H0. exists s. reflexivity.
    + elim H. reflexivity.
  - destruct fn.





  Lemma mkApp_AppMk:
  forall args fn, mkApp fn args = AppMk fn args.
Proof.
  induction args; intros.
  - reflexivity.
  - destruct (isDummy_dec fn).
    + subst. reflexivity.
    + destruct (isWrong_dec fn).
      * destruct i as [x0 jx]. subst. reflexivity.
      *{ rewrite mkApp_cons; try assumption. rewrite IHargs.

         destruct fn; try reflexivity.
         - change
             (mkApp (TApp (TRel n1) t) args = AppMk (TRel n1) (tcons t args)).
           rewrite IHargs. destruct args.
           + reflexivity.
           + rewrite <- IHargs. cbn.
           destruct (tlast t args).
                             





  
(*********
Lemma mkApp_out:
  forall ts fn u,
    mkApp fn (tappend ts (tunit u)) = TApp (mkApp fn ts) u.
Proof.
  induction ts; intros. reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.
 ***********)
 ************************)

(*****************
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
 *********************)

Lemma tnth_tlength_sanity:
  forall fsts t lsts,
    tnth (tlength fsts) (tappend fsts (tcons t lsts)) = Some t.
Proof.
  induction fsts; intros. reflexivity.
  - cbn. apply IHfsts.
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

(** operations on Defs and branches **)
Fixpoint blength (ts:Brs) : nat :=
  match ts with 
    | bnil => 0
    | bcons _ _ ts => S (blength ts)
  end.

Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.

Function dnthBody (n:nat) (l:Defs) {struct l} : option Term :=
  match l with
    | dnil => None
    | dcons _ x _ t => match n with
                           | 0 => Some x
                           | S m => dnthBody m t
                         end
  end.

Function bnth (n:nat) (l:Brs) {struct l} : option (Term * nat) :=
  match l with
    | bnil => None
    | bcons ix x bs => match n with
                           | 0 => Some (x, ix)
                           | S m => bnth m bs
                       end
  end.

Definition is_dunit (ds:Defs) : Prop :=
  exists (nm:name) (s:Term) (n:nat), ds = dunit nm s n.

Lemma is_dunit_dlength:
  forall ds, is_dunit ds <-> dlength ds = 1.
Proof.
  intros ds. split; intros h.
  - destruct h as [x0 [x1 [x2 jx]]]. subst ds. reflexivity.
  - destruct ds.
    + discriminate.
    + destruct ds.
      * exists n, t, n0. reflexivity.
      * discriminate.
Qed.

Lemma is_dunit_dec: forall ds, is_dunit ds \/ ~ (is_dunit ds).
Proof.
  intros ds. case_eq ds; intros.
  - right. intros h. destruct h as [x0 [x1 [x2 jx]]]. discriminate.
  - case_eq d; intros; subst.
    + left. exists n, t, n0. reflexivity.
    + right. intros h.
      pose proof (proj1 (is_dunit_dlength
                           (dcons n t n0 (dcons n1 t0 n2 d0))) h).
      discriminate.
Qed.

(***************
(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
    | TApp fn b bs => TApp fn b (tappend bs args)
    | fn => match args with
              | tnil => fn
              | tcons c cs => TApp fn c cs
            end
  end.
 ****************)

Lemma mkApp_tnil_ident: forall t, mkApp t tnil = t.
  destruct t; simpl; try rewrite tappend_tnil; try reflexivity.
Qed.

(**
Lemma mkApp_goodFn:
  forall fn t ts, ~ isApp fn -> mkApp fn (tcons t ts) = TApp fn t ts.
destruct fn; intros; try reflexivity.
- elim H. auto.
Qed.
 ***)

(****************
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

Lemma mkApp_nil_ident:
  forall fn, ~ isApp fn -> mkApp fn tnil = fn.
intros fn h.
apply MkApp_mkApp. apply MkApp_nil_ident. assumption.
Qed.

Lemma mkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, mkApp fn (tcons arg args) = TApp fn arg args.
induction fn; simpl; intros h arg args; try (constructor; assumption).
- elim h. exists fn1, fn2, t. reflexivity.
Qed.

Lemma pre_mkApp_isApp:
  forall fn args res, MkApp fn args res ->
  forall b bs, args = tcons b bs -> isApp res.
induction 1; intros bx bsx h.
- exists fn, b, (tappend bs cs). reflexivity.
- discriminate.
- exists fn, c, cs. reflexivity.
Qed.
****************)

(**************
Goal
  forall arg args fn,
   mkApp (mkApp fn (tunit arg)) brgs = mkApp fn (tappend args brgs).
Proof.
  induction args using treverse_ind; intros; cbn; intros; try reflexivity.


  Goal
  forall args brgs fn,
   mkApp (mkApp fn args) brgs = mkApp fn (tappend args brgs).
Proof.
  induction args using treverse_ind; intros; cbn; intros; try reflexivity.


  Lemma mkApp_idempotent:
 forall args brgs fn,
   mkApp (mkApp fn args) brgs = mkApp fn (tappend args brgs).
Proof.
  induction args using treverse_ind; intros; cbn; intros; try reflexivity.
  - destruct fn; reflexivity.
  - specialize (IHargs (tcons x brgs) fn).
    rewrite <- (tappend_cons_lem args x brgs).
    rewrite <- IHargs.

Lemma mkApp_idempotent:
 forall brgs fn args,
   mkApp (mkApp fn args) brgs = mkApp fn (tappend args brgs).
Proof.
  induction brgs; intros; intros; try reflexivity.
  - rewrite tappend_tnil. destruct (mkApp fn args); reflexivity.
  - rewrite (tappend_cons_lem args t brgs). 
    Check (tappend_cons_lem args t brgs). in IHbrgs.

    specialize (IHbrgs fn (tappend args (tunit t))).
    
    rewrite <- (tappend_cons_lem args t brgs) in IHbrgs.
    rewrite <- IHbrgs. 
    destruct (mkApp fn args); try reflexivity.
    assert (j:tappend (tappend args (tunit t)) brgs =
              tappend args (tcons t brgs)


    rewrite <- tappend_assoc.

    
    + destruct (mkApp (TRel n) args); try reflexivity.
    + destruct (mkApp (TProof fn) args); try reflexivity.
    + destruct (mkApp (TProof fn) args); try reflexivity.
  
  induction args using treverse_ind; intros; cbn; intros; try reflexivity.
  - destruct fn; try reflexivity.
  - rewrite <- tappend_assoc. destruct fn; cbn.
    + specialize (IHargs (tcons x brgs)). rewrite <- IHargs.
cbn. destruct args.
    induction fn.
    + rewrite <- tappend_assoc.
      specialize (IHargs (tappend (tunit x) brgs)). rewrite <- IHargs.

      
  induction fn; induction args; cbn; intros; try reflexivity.
  - rewrite tappend_tnil. reflexivity.
  - rewrite <- tappend_assoc. simpl. reflexivity.
Qed.

Goal
  forall brgs args fn,
    mkApp fn (tappend args brgs) =
    mkApp (mkApp fn args) brgs.
Proof.
  induction args; intros.
  - cbn. destruct fn; reflexivity.
  - cbn. destruct fn.
    + cbn. Check  (mkApp_idempotent (TApp (TRel n) t)).

    induction brgs; intros.
  - rewrite tappend_tnil. rewrite mkApp_tnil.
    + reflexivity.
    +

    + intros j. functional inversion j; subst.
      * elim H. reflexivity.
      * elim H. reflexivity.
      * 
      destruct fn. try reflexivity.
  -



      Lemma mkApp_isApp:
  forall args fn arg,
    fn <> TDummy -> ~ isWrong fn -> isApp (mkApp fn (tcons arg args)).
Proof.
  induction args using treverse_ind; intros.
  - cbn. destruct fn; auto.
    + elim H0. exists s. reflexivity.
    + elim H. reflexivity.
  - specialize (IHargs fn arg H H0).
    cbn in IHargs; destruct fn; destruct IHargs as [y0 [y1 jy]].
    cbn. rewrite jy.
      intros; cbn.
  - induction args.
    + cbn. auto.
    +
  - elim H0. exists s. reflexivity.
  - elim H. reflexivity.
  - specialize (IHargs H H0).
    destruct IHargs as [x0 [x1 jx]].
    cbn in jx. functional inversion jx; subst.
    + cbn. auto.
    + cbn.

    rewrite jx. intuition.
  try (cbn in IHargs; intuition).
  - change
      (isApp (mkApp (TApp (TRel n) arg) args)).
    change
      (isApp (mkApp (TApp (TRel n) arg) args)).
  -
    
  cbn; auto.
  - change
      (isApp (mkApp (TApp (TRel n) arg) args)).
    change
      (isApp (mkApp (TApp (TRel n) arg) args)).

    unfold mkApp. auto. elim H0. exists s. reflexivity.
  - elim H. reflexivity.
Qed.

Goal
  forall ts t fn,
    fn <> TDummy -> ~ isWrong fn -> isApp (mkApp fn (tcons t ts)).
Proof.
  induction ts; intros.
  - rewrite mkApp_tunit; try assumption. auto.
  - Check (IHts t0 _ H H0).

    destruct fn; cbn. eapply IHts.

Lemma mkApp_isApp:
  forall ts t fn,
    ~ isWrong fn -> fn <> TDummy ->
    isApp (mkApp fn (tcons t ts)).
Proof.
  induction ts; intros.
  - rewrite mkApp_tunit; try assumption. auto.
  - apply IHts.
Qed.
*************)

Lemma isApp_mkApp_TApp:
  forall args fn arg, isApp (mkApp (TApp fn arg) args).
Proof.
  induction args; intros; cbn.
  - auto.
  - apply IHargs.
Qed.

Lemma mkApp_idempotent:
  forall ts (fn:Term) (ss:Terms),
    mkApp (mkApp fn ts) ss = mkApp fn (tappend ts ss).
Proof.
  induction ts; destruct fn; intros; cbn; try reflexivity;
    try rewrite <- IHts; try reflexivity.
Qed.                                                       


(***********
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
  - exists (TProof fn), arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
  - exists (TLambda n fn), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLetIn n fn1 fn2), arg, tnil. split. reflexivity.
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
  - exists TInd, arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TConstruct i n n0 n1), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase p fn b), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TWrong s), arg, tnil. cbn. split. reflexivity.
    left. repeat split. not_isApp.
  - exists TDummy, arg, tnil. cbn. split. reflexivity.
    left. repeat split. not_isApp.
Qed.
 ***************)

(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaProof: WFapp TProof
| wfaLambda: forall nm bod, WFapp bod -> WFapp (TLambda nm bod)
| wfaLetIn: forall nm dfn bod,
             WFapp dfn -> WFapp bod -> WFapp (TLetIn nm dfn bod)
| wfaApp: forall fn t, WFapp fn -> WFapp t -> WFapp (TApp fn t)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaConstruct: forall i m1 np na, WFapp (TConstruct i m1 np na)
| wfaCase: forall m mch brs,
            WFapp mch -> WFappBs brs -> WFapp (TCase m mch brs)
| wfaFix: forall defs m, WFappDs defs -> WFapp (TFix defs m)
| wfaDummy: forall str, WFapp (TDummy str)
with WFapps: Terms -> Prop :=
| wfanil: WFapps tnil
| wfacons: forall t ts, WFapp t -> WFapps ts -> WFapps (tcons t ts)
with WFappBs: Brs -> Prop :=
| wfabnil: WFappBs bnil
| wfabcons: forall n b bs, WFapp b -> WFappBs bs ->  WFappBs (bcons n b bs)
with WFappDs: Defs -> Prop :=
| wfadnil: WFappDs dnil
| wfadcons: forall nm bod arg ds,
             WFapp bod -> WFappDs ds ->
             WFappDs (dcons nm bod arg ds).
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
  induction 1; cbn; intros; try discriminate.
  - destruct (canonicalP fn); try discriminate.
    + destruct p. myInjection H1.
      eapply tappend_pres_WFapps. apply (IHWFapp1 _ _ eq_refl).
      constructor. assumption. constructor.
  - myInjection H. constructor. 
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

(**********
Lemma WFapp_mkApp_WFapp:
  forall u, WFapp u -> forall t args, u = mkApp t args ->
       WFapp t /\ WFapps args .
Proof.
  induction 1; intros tx args h;
  try (destruct tx, args; simpl in h; try discriminate;
              try (solve [constructor]);
              try (solve [injection h; intros; subst; intuition]);
              intuition;
              injection h; intros; subst; intuition).
  - constructor; try assumption. rewrite tappend_tnil in H2; assumption.
  - constructor; try assumption. eapply WFapps_tappendl. eassumption.
  - assert (j:= WFapps_tappendr _ _ H2). inversion j. constructor; assumption.
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
 ************)

Lemma tnth_pres_WFapp:
  forall (brs:Terms), WFapps brs -> forall n t, tnth n brs = Some t -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (tnth n brs); intros; try discriminate.
  - injection H; intros; subst. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma dnthBody_pres_WFapp:
  forall (ds:Defs), WFappDs ds ->
    forall n x, (dnthBody n ds) = Some x -> WFapp x.
Proof.
  intros ds h n x.
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

Lemma bnth_pres_WFapp:
  forall (brs:Brs), WFappBs brs ->
                    forall n t m, bnth n brs = Some (t,m) -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (bnth n brs); intros; try discriminate.
  - myInjection H. inversion h. assumption.
  - eapply IHo; inversion h; eassumption.
Qed.

(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfProof: forall n, WFTrm TProof n
| wfLambda: forall n nm bod,
    WFTrm bod (S n) -> WFTrm (TLambda nm bod) n
| wfLetIn: forall n nm dfn bod,
    WFTrm dfn n -> WFTrm bod (S n) ->
    WFTrm (TLetIn nm dfn bod) n
| wfApp: forall n fn t,
    WFTrm fn n -> WFTrm t n -> WFTrm (TApp fn t) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfConstruct: forall n i m np na,
    WFTrm (TConstruct i m np na) n
| wfCase: forall n m mch brs,
    WFTrm mch n -> WFTrmBs brs n ->
    WFTrm (TCase m mch brs) n
| wfFix: forall n defs m,
    WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
| wfDummy: forall n str, WFTrm (TDummy str) n
with WFTrms: Terms -> nat -> Prop :=
     | wfnil: forall n, WFTrms tnil n
     | wfcons: forall n t ts, WFTrm t n -> WFTrms ts n -> WFTrms (tcons t ts) n
with WFTrmBs: Brs -> nat -> Prop :=
     | wfbnil: forall n, WFTrmBs bnil n
     | wfbcons: forall n m b bs,
         WFTrm b n -> WFTrmBs bs n -> WFTrmBs (bcons m b bs) n
with WFTrmDs: Defs -> nat -> Prop :=
     | wfdnil: forall n, WFTrmDs dnil n
     | wfdcons: forall n nm bod arg ds,
         WFTrm bod n -> WFTrmDs ds n ->
         WFTrmDs (dcons nm bod arg ds) n.
Hint Constructors WFTrm WFTrms WFTrmBs WFTrmDs.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrms_ind' := Minimality for WFTrms Sort Prop                   
  with WFTrmBs_ind' := Minimality for WFTrmBs Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsBrsDefs_ind
         from WFTrm_ind', WFTrms_ind', WFTrmBs_ind', WFTrmDs_ind'.

Lemma WFTrm_shape:
  forall t n, WFTrm t n -> t <> TRel n.
Proof.
  induction t; intros; inversion_Clear H; intros h; try discriminate.
  myInjection h. omega.
Qed.
    
Lemma WFTrm_up:
  (forall t m, WFTrm t m -> WFTrm t (S m)) /\
  (forall ts m, WFTrms ts m -> WFTrms ts (S m)) /\
  (forall ts m, WFTrmBs ts m -> WFTrmBs ts (S m)) /\
  (forall ds m, WFTrmDs ds m -> WFTrmDs ds (S m)).
Proof.
  apply WFTrmTrmsBrsDefs_ind; cbn; intros; try econstructor; try eassumption.
  omega.
Qed.
  
Lemma WFTrm_Up:
  (forall t m, WFTrm t m -> forall n, m <= n -> WFTrm t n).
Proof.
  intros t m h. induction 1. assumption. apply WFTrm_up. assumption.
Qed.
  
Lemma WFTrmDs_Up:
  (forall ds m, WFTrmDs ds m -> forall n, m <= n -> WFTrmDs ds n).
Proof.
  intros ds m h. induction 1. assumption.
  apply (proj2 (proj2 WFTrm_up)). assumption.
Qed.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall ts n, WFTrms ts n -> WFapps ts) /\
  (forall bs n, WFTrmBs bs n -> WFappBs bs) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try (constructor; try assumption).
Qed.

(**********
Lemma tappend_pres_WFTrms:
  forall ts ss m, WFTrms ts m -> WFTrms ss m -> WFTrms (tappend ts ss) m.
Proof.
  induction ts; intros.
  - cbn. assumption.
  - cbn. inversion_Clear H. constructor; intuition.
Qed.

Lemma treverse_pres_WFTrms:
  forall ts m, WFTrms ts m -> WFTrms (treverse ts) m.
Proof.
  induction ts; intros.
  - cbn. constructor.
  - inversion_Clear H. cbn. apply tappend_pres_WFTrms; intuition.
Qed.
 **************)

(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:string.

Inductive PoccTrm : Term -> Prop :=
| PoLambdaBod: forall s bod, PoccTrm bod -> PoccTrm (TLambda s bod)
| PoLetInDfn: forall s dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn bod)
| PoLetInBod: forall s dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn bod)
| PoAppL: forall fn a, PoccTrm fn -> PoccTrm (TApp fn a)
| PoAppA: forall fn a, PoccTrm a -> PoccTrm (TApp fn a)
| PoConst: PoccTrm (TConst nm)
| PoCaseL: forall n mch brs, PoccTrm mch -> PoccTrm (TCase n mch brs)
| PoCaseR: forall n mch brs, PoccBrs brs -> PoccTrm (TCase n mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstr: forall m1 n np na,
    PoccTrm (TConstruct (mkInd nm m1) n np na)
with PoccTrms: Terms -> Prop :=
     | Pohd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
     | Potl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccBrs : Brs -> Prop :=
| PoBhd: forall n t ts, PoccTrm t -> PoccBrs (bcons n t ts)
| PoBtl: forall n t ts, PoccBrs ts -> PoccBrs (bcons n t ts)
with PoccDefs : Defs -> Prop :=
| PoDhd_bod: forall dn db dra ds,
           PoccTrm db -> PoccDefs (dcons dn db dra ds)
| PoDtl: forall dn db dra ds,
           PoccDefs ds -> PoccDefs (dcons dn db dra ds).
Hint Constructors PoccTrm PoccTrms PoccBrs PoccDefs.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poTrms_ind' := Minimality for PoccTrms Sort Prop
  with poBrs_ind' := Minimality for PoccBrs Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsBrsDefs_ind
         from poTrm_ind', poTrms_ind', poBrs_ind', poDefs_ind'.


Lemma Pocc_TConst: forall s2, PoccTrm (TConst s2) -> nm = s2.
intros s2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TConst: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto. 
Qed.

(*********
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
 ****************)

(*************
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
 ***************)

Lemma inverse_Pocc_TConstL: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma notPocc_TApp:
  forall t arg, ~ PoccTrm (TApp t arg) -> ~ PoccTrm t /\ ~ PoccTrm arg.
intuition.
Qed.

Lemma Pocc_TApp:
  forall t arg, PoccTrm (TApp t arg) -> PoccTrm t \/ PoccTrm arg.
inversion 1; intuition.
Qed.

Lemma notPocc_TLambda:
  forall n bod, ~ PoccTrm (TLambda n bod) -> ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TLetIn:
  forall n dfn bod, ~ PoccTrm (TLetIn n dfn bod) ->
                   ~ PoccTrm dfn /\ ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TCase:
  forall n mch brs, ~ PoccTrm (TCase n mch brs) ->
                    ~ PoccTrm mch /\ ~ PoccBrs brs.
intuition. 
Qed.

Lemma notPocc_TFix:
  forall ds m, ~ PoccTrm (TFix ds m) -> ~ PoccDefs ds.
intuition. 
Qed.

(**********
Lemma notPoccTrms:
  forall t ts, ~ PoccTrms (tcons t ts) -> ~ PoccTrm t /\ ~ PoccTrms ts.
intuition. 
Qed.

Lemma PoccTrms_tcons:
  forall t ts, PoccTrms (tcons t ts) -> PoccTrm t \/ PoccTrms ts.
inversion 1; intuition. 
Qed.
 *************)

Lemma notPoccDefs:
  forall nm bod rarg ds, ~ PoccDefs (dcons nm bod rarg ds) ->
                         ~ PoccTrm bod /\ ~ PoccDefs ds.
intuition. 
Qed.

(********
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
  - simpl. intros brgs. Check PoAppR.
    apply PoAppR. apply PoccTrms_tappendl. assumption. 
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
*****************)

(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable (tin:Term).

Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| IProof: forall n, Instantiate n TProof TProof
| ILambda: forall n nm bod ibod,
    Instantiate (S n) bod ibod -> 
    Instantiate n (TLambda nm bod) (TLambda nm ibod)
| ILetIn: forall n nm dfn bod idfn ibod,
    Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
    Instantiate n (TLetIn nm dfn bod) (TLetIn nm idfn ibod)
| IApp: forall n t a it ia,
    Instantiate n t it -> Instantiate n a ia ->
    Instantiate n (TApp t a) (TApp it ia)
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IConstruct: forall n ind m1 np na,
    Instantiate n (TConstruct ind m1 np na) (TConstruct ind m1 np na)
| ICase: forall n np s ts is its,
    Instantiate n s is -> InstantiateBrs n ts its ->
    Instantiate n (TCase np s ts) (TCase np is its)
| IFix: forall n d m id, 
    InstantiateDefs (n + dlength d) d id ->
    Instantiate n (TFix d m) (TFix id m)
| IWrong: forall n s, Instantiate n (TWrong s) (TWrong s)
| IDummy: forall n str, Instantiate n (TDummy str) (TDummy str)
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
     | Idcons: forall n nm bod rarg ds ibod ids,
         Instantiate n bod ibod ->
         InstantiateDefs n ds ids ->
         InstantiateDefs n (dcons nm bod rarg ds)
                         (dcons nm ibod rarg ids).
Hint Constructors Instantiate Instantiates InstantiateBrs InstantiateDefs.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with Instantiates_ind' := Induction for Instantiates Sort Prop
  with InstantiateBrs_ind' := Induction for InstantiateBrs Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstTrmsBrsDefs_ind from
         Instantiate_ind', Instantiates_ind',
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
  intros t ht n it hit. destruct ht as [x0 [x1 jx]]. subst.
  inversion_Clear hit. auto.
Qed.          

(* Instantiate preserves shape of closed terms *)
Lemma Instantiate_pres_shape:
  forall n t s,
    Instantiate n t s -> t <> TRel n -> Term_shape t = Term_shape s.
Proof.
  induction 1; intros; try reflexivity.
  - elim H. reflexivity.
Qed.

(** Instantiate preserves closedness **)
Lemma Instantiate_pres_WFTrm:
  (forall n bod ibod,
      Instantiate n bod ibod ->
      forall m, n <= m -> WFTrm bod (S m) -> WFTrm tin m -> WFTrm ibod m) /\
  (forall n ts ss,
      Instantiates n ts ss ->
      forall m, n <= m -> WFTrms ts (S m) -> WFTrm tin m -> WFTrms ss m) /\
  (forall n ts ss,
      InstantiateBrs n ts ss ->
      forall m, n <= m -> WFTrmBs ts (S m) -> WFTrm tin m -> WFTrmBs ss m) /\
  (forall n ts ss,
      InstantiateDefs n ts ss ->
      forall m, n <= m -> WFTrmDs ts (S m) -> WFTrm tin m -> WFTrmDs ss m).
Proof.
  apply InstTrmsBrsDefs_ind; intros; trivial;
  try (inversion_Clear H1; constructor; try assumption; apply H; assumption);
  try (inversion_Clear H0; try econstructor; try eassumption; omega).
  - inversion_Clear H1. constructor; try assumption.
    apply H; try assumption; try omega. apply (proj1 WFTrm_up). assumption.
  - inversion_Clear H2. econstructor; try eassumption.
    + apply H; try eassumption.
    + apply H0; try eassumption; try omega.
      apply (proj1 WFTrm_up). assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; try assumption.
    + apply H0; try assumption.
  - inversion_Clear H2. constructor; try assumption.
    + apply H; try assumption.
    + apply H0; try assumption.
  - pose proof (InstantiateDefs_pres_dlength i) as k.
    inversion_Clear H1. constructor; try omega.
    + eapply H; try omega; rewrite <- k. assumption.
      * eapply WFTrm_Up. eassumption. omega.
  - inversion_Clear H2. constructor; intuition.
  - inversion_Clear H2. constructor; intuition.
  - inversion_Clear H2. constructor; intuition.
Qed.

(************
Lemma Instantiate_pres_WFapp:
  forall n bod ibod,
    Instantiate n bod ibod -> WFapp bod -> WFapp tin -> WFapp ibod.
Proof.
  induction 1; intros; try eassumption;
    try (solve[inversion_Clear H0; constructor; intuition]);
    try (solve[inversion_Clear H1; constructor; intuition]).
  - inversion_Clear H1; constructor; intuition.
Check (
    
  - inversion_Clear H0. constructor; intuition.
  - inversion_Clear H0. constructor; intuition.

    
  intros. eapply WFTrm_WFapp. instantiate (1:= S n).
  eapply Instantiate_pres_WFTrm; try eassumption.
  - omega.
  - eapply Instantiate_pres_WFTrm; try eassumption.
************)
  
(************
(* Instantiate doesn't generate new names *)
Lemma Instantiates_no_gen:
  (~ PoccTrm tin) ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, InstantiateBrs n ts ss -> PoccBrs ss -> PoccBrs ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstBrsDefs_ind; intros; auto.
  - contradiction.
  - inversion H.
  - inversion_Clear H0.
    + constructor. intuition.
  - inversion_Clear H0.
    + constructor. intuition.
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoLetInBod. intuition.
  - inversion_Clear H1.
    + apply PoAppL. apply H. assumption.
    + apply PoAppA. apply H0. assumption.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoCaseR. intuition.
  - inversion_Clear H0.
    + constructor. apply H. assumption.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoBtl. intuition.
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoDtl. intuition. 
Qed.
 *******************)

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a =>
      TApp (instantiate n t) (instantiate n a)
    | TLambda nm bod =>
      TLambda nm (instantiate (S n) bod)
    | TCase np s ts =>
      TCase np (instantiate n s) (instantiateBrs n ts)
    | TLetIn nm tdef bod =>
      TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TProof => TProof
    | TConstruct i m np na => TConstruct i m np na
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
         | dcons nm bod rarg ds =>
           dcons nm (instantiate n bod) rarg (instantiateDefs n ds)
       end.

(* MS: fixme bug in 8.6 *)
(* Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop *)
(* with instantiates_ind' := Induction for instantiates Sort Prop *)
(* with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop. *)

Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, Instantiates n ts its -> instantiates n ts = its) /\
  (forall n ts its, InstantiateBrs n ts its -> instantiateBrs n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
Proof.
  apply InstTrmsBrsDefs_ind; intros; simpl; intuition; try (subst; reflexivity).
  - rewrite nat_compare_EQ. reflexivity.
  - rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
  - rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall bs n, Instantiates n bs (instantiates n bs)) /\
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
  (forall (Ds:Defs), PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsBrsDefs_ind; intros; cbn; try solve [constructor; trivial].
Qed.

Lemma instantiate_mkApp_commute:
  forall args fn n,
    instantiate n (mkApp fn args) =
    mkApp (instantiate n fn) (instantiates n args).
Proof.
  induction args; intros.
  - reflexivity.
  - induction fn; intros; try eapply IHargs.
Qed.


(**********
Lemma instantiate_TApp_mkApp:
  forall n fn arg args,
  instantiate n (TApp fn arg args) =
   mkApp (instantiate n fn) (instantiates n (tcons arg args)).
Proof.
  intros. cbn. reflexivity.
Qed.
 **********)


(* instantiate preserves shape of closed terms *)
Lemma instantiate_pres_shape:
  forall n t s,
    instantiate n t = s -> t <> TRel n -> Term_shape t = Term_shape s.
Proof.
  intros. eapply Instantiate_pres_shape.
  rewrite <- H. eapply (proj1 instantiate_Instantiate ).
  assumption.
Qed.  

Lemma shape_isApp:
  forall t, Term_shape t = sApp <-> isApp t.
Proof.
  destruct t; split; cbn; intros; try discriminate;
  destruct H as [x0 [x1 jx]]; try discriminate.
  auto. reflexivity.
Qed.

Lemma shape_isConstruct:
  forall t, Term_shape t = sConstruct <-> isConstruct t.
Proof.
  destruct t; split; cbn; intros; try discriminate;
  try (destruct H as [x0 [x1 [x2 [x3 jx]]]]; try discriminate).
  exists i, n, n0, n1. reflexivity. reflexivity.
Qed.

Lemma instantiate_pres_WFTrm:
  forall m bod, WFTrm bod (S m) -> WFTrm tin m -> 
                  forall n, n <= m -> WFTrm (instantiate n bod) m.
Proof.
  intros.
  apply (proj1 (Instantiate_pres_WFTrm) n bod); try assumption.
  refine (proj1 (instantiate_Instantiate) _ _).
Qed.

Lemma instantiate_pres_WFapp:
  (forall bod, WFapp bod ->
              WFapp tin -> forall n, WFapp (instantiate n bod)) /\
  (forall ts, WFapps ts ->
              WFapp tin -> forall n, WFapps (instantiates n ts)) /\
  (forall bs, WFappBs bs ->
              WFapp tin -> forall n, WFappBs (instantiateBrs n bs)) /\
  (forall ds, WFappDs ds ->
              WFapp tin -> forall n, WFappDs (instantiateDefs n ds)).
Proof.
  apply WFappTrmsBrsDefs_ind; intros;
  try (solve [unfold instantiate; constructor]).
  - destruct (lt_eq_lt_dec n m) as [[h|h]|h]; unfold instantiate.
    + rewrite (proj1 (nat_compare_lt _ _) h). constructor.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). assumption.
    + rewrite (proj1 (nat_compare_gt _ _) h). constructor.
  - cbn. constructor. apply H0. assumption.
  - change (WFapp (TLetIn nm0 (instantiate n dfn) (instantiate (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TApp (instantiate n fn)  (instantiate n t))).
    + constructor; intuition. 
  - change (WFapp (TCase m (instantiate n mch) (instantiateBrs n brs))).
    constructor.
    + apply H0; assumption.
    + apply H2; assumption.
   - change (WFapp (TFix (instantiateDefs (n + dlength defs) defs) m)).
     constructor.
     + apply H0. assumption.
   - change (WFapps (tcons (instantiate n t) (instantiates n ts))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappBs (bcons n (instantiate n0 b) (instantiateBrs n0 bs))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappDs (dcons nm0 (instantiate n bod) arg (instantiateDefs n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
Qed.

End Instantiate_sec.
End PoccTrm_sec.


(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) : Term := instantiate arg 0 bod.

Lemma whBetaStep_pres_WFTrm:
  forall bod n, WFTrm bod (S n) ->
                forall arg, WFTrm arg n-> WFTrm (whBetaStep bod arg) n.
Proof.
  intros. unfold whBetaStep.
  eapply instantiate_pres_WFTrm; try eassumption. omega.
Qed. 
                                                             
Definition whCaseStep (cstrNbr:nat) (args:Terms) (brs:Brs): option Term := 
  match bnth cstrNbr brs with
    | Some (t, _) => Some (mkApp t args)
    | None => None
  end.

Lemma mkApp_pres_WFTrm:
  forall n args, WFTrms args n ->
                   forall fn, WFTrm fn n ->
                              WFTrm (mkApp fn args) n.
Proof.
  induction 1; intros; cbn.
  - destruct fn; assumption.
  - assert (j: WFTrm (TApp fn t) n).
    { constructor; assumption. }
    specialize (IHWFTrms _ j). destruct fn; eassumption.
Qed.

Lemma bnth_pres_WFTrm:
  forall n (brs:Brs), WFTrmBs brs n ->
    forall m x ix, bnth m brs = Some (x, ix) -> WFTrm x n.
Proof.
  intros n brs h m x ix.
  functional induction (bnth m brs); intros; auto.
  - discriminate.
  - myInjection H. inversion_Clear h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma whCaseStep_pres_WFTrm:
  forall n ts, WFTrms ts n -> forall brs, WFTrmBs brs n ->
  forall m s, whCaseStep m ts brs = Some s -> WFTrm s n.
Proof.
  intros n ts h1 brs h2 m s h3. unfold whCaseStep in h3.
  assert (j: bnth m brs = None \/ (exists t, bnth m brs = Some t)).
  { destruct (bnth m brs).
    + destruct p. right. exists (t, n0). reflexivity.
    + left. reflexivity. }
  destruct j.
  - rewrite H in h3. discriminate.
  - destruct H as [x jx]. rewrite jx in h3. destruct x as [y0 y1].
    myInjection h3. apply mkApp_pres_WFTrm; try assumption.
    eapply (bnth_pres_WFTrm h2). eassumption.
Qed.

(** Unfolding a Fixpoint **)
(** "dts" is a list of the mutual fixpoint definitions
*** "m" tells which of the definitions is being called
**)
Definition pre_whFixStep body dts arg : Term :=
  let f := fold_left
             (fun bod ndx => instantiate (TFix dts ndx) 0 bod)
             (list_to_zero (dlength dts)) body in
  (TApp f arg).
Functional Scheme pre_whFixStep_ind := Induction for pre_whFixStep Sort Prop.

Lemma pre_whFixStep_dunit:
  forall nm bod d arg,
    pre_whFixStep bod (dunit nm d 0) arg =
    TApp (instantiate (TFix (dunit nm d 0) 0) 0 bod) arg.
Proof.
  intros. unfold pre_whFixStep, dlength, list_to_zero.
  reflexivity.
Qed.
  
Lemma fold_left_pres_WFTrm:
  forall (f:Term -> nat -> Term) (ns:list nat) (a:nat),
    (forall u m, m >= a ->
                 WFTrm u (S m) -> forall n, In n ns -> WFTrm (f u n) m) ->
    forall t, WFTrm t (a + List.length ns) -> WFTrm (fold_left f ns t) a.
Proof.
  intros f. induction ns; cbn; intros.
  - replace (a + 0) with a in H0. assumption. omega.
  - apply IHns.
    + intros. apply H; try assumption. apply (or_intror H3).
    + replace (a0 + S (Datatypes.length ns))
        with (S (a0 + (Datatypes.length ns))) in H0.
      assert (j: a0 + Datatypes.length ns >= a0). omega.
      specialize (H t _ j H0).
      apply H. apply (or_introl eq_refl). omega.
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
  forall  (bod:Term) (dts:Defs) (arg:Term),
    WFapp bod -> WFappDs dts -> WFapp arg ->
        WFapp (pre_whFixStep bod dts arg).
Proof.
  intros bod dts arg hbod hdts hargs.
  unfold pre_whFixStep. constructor; try assumption.
  apply fold_left_pres_WFapp; try assumption.
  intros. eapply (proj1 (instantiate_pres_WFapp (TFix dts n))).
  assumption. constructor. assumption.
Qed.

