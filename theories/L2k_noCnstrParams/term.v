(*** type fields are stripped from term notations ***)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.  (* shared namespace *)
Require Import L2k.compile.

Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.


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
Ltac not_is4 :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with zz := fresh "z"
  with ww := fresh "w" in
  intros hh; destruct hh as [xx [yy [zz [ww jj]]]]; discriminate.
Ltac not_isApp := not_is2.
Ltac not_isLambda := not_is2.
Ltac not_isCase := not_is3.
Ltac not_isFix := not_is2.
Ltac not_isCast := not_is1.
Ltac not_isConstruct := not_is3.
            
Ltac isApp_inv h :=
  let hh := fresh "h"
  with xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j"
  in destruct h as [xx [yy [zz jj]]]; discriminate.
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

Lemma mkApp_tl:
  forall bs fn b, mkApp fn (tappend bs (tunit b)) = TApp (mkApp fn bs) b.
Proof.
  induction bs; intros.
  - reflexivity.
  - cbn. rewrite IHbs. reflexivity.
Qed.

Lemma mkApp_tunit:
  forall fn u, 
    mkApp fn (tunit u) = TApp fn u.
Proof.
  intros. destruct fn; try reflexivity.
Qed.
           

(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => "(Rel " ++ (nat_to_string n) ++ ")"
    | TProof t => "(PRF " ++ print_term t ++ ")"
    | TLambda nm t => "(LAM "++ (print_name nm) ++ " [" ++ print_term t ++ "])"
    | TLetIn nm _ _ => "(LET " ++ (print_name nm) ++ ")"
    | TApp fn arg =>
      "(" ++ (print_term fn) ++ " @ " ++ (print_term arg) ++ ")"
    | TConst s => "[" ++ s ++ "]"
    | TConstruct i n _ =>
      "(CSTR " ++ (print_inductive i) ++ " " ++ (nat_to_string n) ++ ")"
    | TCase i mch _ =>
      "(CASE " ++ (print_inductive i) ++ ":"
               ++ (print_term mch) ++ " _ " ++") "
    | TFix _ n => " (FIX " ++ (nat_to_string n) ++ ") "
    | TWrong str => ("(TWrong:" ++ str ++ ")")
    | TDummy str => ("TDummy:" ++ str ++ ")")
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
  - destruct t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - destruct t0; cross.
    destruct (H t0); [lft | rght ..].
  - destruct t0; cross.
    destruct (name_dec n n0); destruct (H t0); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (name_dec n n0); destruct (H t1_1); destruct (H0 t1_2); 
    [lft | rght ..]. 
  - destruct t1; cross.
    destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t0; cross.
    destruct (inductive_dec i i0), (eq_nat_dec n n0), (H t0);
      [lft | rght .. ].
  - destruct t0; cross.
    destruct (inductive_dec i i0), (H t0), (H0 b0);
    [lft | rght .. ].
  - destruct t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t; cross.
    destruct (string_dec s s0); [lft | rght .. ].
  - destruct tt; cross; lft.
  - destruct tt; cross.
    destruct (H t1), (H0 tt); [lft | rght .. ].
  - destruct tt; cross. lft.
  - destruct tt; cross.
    destruct (eq_nat_dec n n0), (H t0), (H0 tt); [lft | rght .. ].
  - destruct ee; cross. lft.
  - destruct ee; cross.
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
    | TConstruct _ _ args => S (TrmsSize args)
    | _ => S 0
  end
with TrmsSize (ts:Terms) {struct ts} : nat :=
  match ts with
    | tnil => 1
    | tcons s ss => S (TrmSize s + TrmsSize ss)
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

Definition isWrong (t:Term) : Prop :=  exists str, t = TWrong str.
Lemma IsWrong: forall str, isWrong (TWrong str).
  intros. exists str. reflexivity.
Qed.
Hint Resolve IsWrong.
Lemma isWrong_dec: forall t, {isWrong t}+{~ isWrong t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. auto.
Qed.

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

Definition isOLambda (t:option Term) : Prop :=
  exists nm bod, t = Some (TLambda nm bod).

Definition isConstruct (t:Term) : Prop :=
  exists i n args, t = TConstruct i n args.
Lemma IsConstruct: forall i n args, isConstruct (TConstruct i n args).
intros. exists i, n, args. reflexivity.
Qed.
Hint Resolve IsConstruct.
Lemma isConstruct_dec: forall t, {isConstruct t}+{~ isConstruct t}.
Proof.
  destruct t;
    try (right; intros h; destruct h as [x1 [x2 [x3 j]]]; discriminate).
  - left. auto.
Qed.

Definition isOConstruct t : Prop :=
  exists i n args, t = Some (TConstruct i n args).
Lemma isOConstruct_dec: forall t, (isOConstruct t) \/ (~ isOConstruct t).
Proof.
  destruct t;
    try (right; intros h; destruct h as [x1 [x2 [x3 j]]]; discriminate).
  destruct (isConstruct_dec t).
  - destruct i as [x0 [x1 [x2 jx]]]; subst. left. unfold isOConstruct.
    exists x0, x1, x2. reflexivity.
  - right. intros h. elim n. destruct h as [x0 [x1 [x2 jx]]].
    myInjection jx. auto.
Qed.

Lemma isOConstruct_Some:
  forall i m npars, isOConstruct (Some (TConstruct i m npars)).
Proof.
  intros. unfold isOConstruct. exists i, m, npars. reflexivity.
Qed.

Lemma isOConstruct_None:
  ~ isOConstruct None.
Proof.
  intros h. destruct h as [x0 [x1 [x2 jx]]]. discriminate.
Qed.
             

Definition goodF (F:Terms -> Term) :=
  forall ts us, isApp (F ts) -> isApp (F us).

(*****
Lemma etaExpand_args_up:
  forall na actualArgs (F:Terms -> Term) computedArgs,
    goodF F ->
    isOApp (etaExpand_args_Lam (S na) actualArgs F computedArgs) ->
    isOApp (etaExpand_args_Lam na actualArgs F computedArgs).
Proof.
  induction na; induction actualArgs; intros.
  - cbn. cbn in H0. destruct H0 as [x0 [x1 [x2 jx]]]. discriminate.
  - cbn. cbn in H. cbn in IHactualArgs. destruct actualArgs.
    
  Lemma etaExpand_args_up:
  forall na actualArgs (F:Terms -> Term) computedArgs,
    isOLambda (etaExpand_args
                na actualArgs (fun b => TLambda nAnon (F b)) computedArgs) ->
    isOLambda (etaExpand_args
                (S na) actualArgs (fun b => TLambda nAnon (F b)) computedArgs).
Proof.
  induction na; intros.
  - cbn in *. destruct actualArgs.
    + apply isOLambda_Some.
    + destruct actualArgs; auto. elim isOLambda_None. assumption.
  - cbn in *. destruct actualArgs.
    + refine (IHna tnil (fun b : Terms => TLambda nAnon (F b))
                  (tappend (lifts 0 computedArgs) (tunit (TRel 0))) _).
      assumption.
    + eapply IHna. assumption.
Qed.

Lemma na_isLambda_etaExpand_args:
  forall na actualArgs,
    na >= tlength actualArgs ->
    forall (F:Terms -> Term) computedArgs,
      isOLambda (etaExpand_args
                   na actualArgs (fun b => TLambda nAnon (F b)) computedArgs).
Proof.
  induction na; induction actualArgs; cbn; intros; try omega; auto.
  - apply isOLambda_Some.
  - refine (IHna tnil _  (fun b : Terms => TLambda nAnon (F b))
                 (tappend (lifts 0 computedArgs) (tunit (TRel 0)))).
    cbn. omega.
  - refine (IHna actualArgs _  F (tappend computedArgs (tunit t))).
    omega.
Qed.
    
Lemma na_isConstruct_etaExpand_args:
  forall na aArgs,
    na = tlength aArgs ->
    forall i m npars cArgs,
      (isOConstruct
         (etaExpand_args
            na aArgs (fun b => TConstruct i m npars) cArgs)).
Proof.
  induction na; induction aArgs; cbn; intros; try omega.
  - apply isOConstruct_Some.
  - assert (j: na = tlength aArgs). omega.
    eapply (IHna aArgs j i m npars). 
Qed.


Goal
  forall na tlaArgs,
    na >= S tlaArgs ->
  forall aArgs, tlaArgs = tlength aArgs ->
    forall (F:Terms -> Term) cArgs,
      isOLambda (etaExpand_args_Lam
                   na aArgs (fun b => TLambda nAnon (F b)) cArgs).
Proof.
  induction 1; intros.
  - assert (j: exists t ts, aArgs = tcons t ts). admit.
    destruct j as [x0 [x1 jx]]. subst. cbn.
    induction x1.
    + cbn. apply isOLambda_Some.
    + cbn. assumption.
  
  induction na; induction aArgs; cbn; intros.
  - destruct (H cArgs) as [x0 [x1 jx]]. rewrite jx. apply isOLambda_Some.
  - destruct (H cArgs) as [x0 [x1 jx]]. specialize (H cArgs).

    Check (IHaArgs _ cArgs H).
******************)


(*********
Goal
  forall ts F na aArgs cArgs,
  isConstruct (etaExpand_args na aArgs F cArgs) ->
  isConstruct (etaExpand_args na aArgs F (tappend cArgs ts)).
Proof.
  induction ts; intros.
  - rewrite tappend_tnil. assumption.
  - specialize (IHts _ _ _ _ H).
***********)


(*****************
Lemma na_isConstruct_etaExpand_args:
  forall na aArgs,
    na < tlength aArgs ->
    forall i m (F:Terms -> Terms) cArgs,
      isOConstruct (etaExpand_args
                     na aArgs (fun b => TConstruct i m (F b)) cArgs).
Proof.
  induction na; induction aArgs; cbn; intros; try omega.
  - cbn in *. destruct aArgs; intuition. 
  - assert (j0: na < tlength aArgs). omega.
    Check (IHna _ j0). assumption.
Qed.
 ******************)



              
(**********
Lemma na_isConstruct_etaExpand_args:
  forall na aArgs,
    na < tlength aArgs ->
    forall i m (F:Terms -> Terms) cArgs,
      isConstruct (etaExpand_args na aArgs
                                  (fun b => TConstruct i m (F b)) cArgs) \/
      isWrong (etaExpand_args na aArgs
                              (fun b => TConstruct i m (F b)) cArgs).
Proof.
  induction na; induction aArgs; cbn; intros; try omega.
  - intuition. 
  - left. assert (j0: na < tlength aArgs). omega.
    Check (IHna _ j0). assumption.
Qed.

Lemma na_isLam_or_isConstruct_etaExpand_args:
  forall na actualArgs computedArgs,
    (forall F:Terms -> Term,
        tlength actualArgs <= na /\
        isLambda
          (etaExpand_args
             na actualArgs (fun b => TLambda nAnon (F b)) computedArgs)) \/
    (forall i m (F:Terms -> Terms),
        tlength actualArgs > na /\
        isConstruct
          (etaExpand_args
             na actualArgs (fun b => TConstruct i m (F b)) computedArgs)).
Proof.
  intros. destruct (le_lt_dec (tlength actualArgs) na).
  - left. intros. split. omega. eapply na_isLambda_etaExpand_args. omega.
  - right. intros. split. omega. eapply na_isConstruct_etaExpand_args. omega.
Qed.
 ***********************)

(****************
Lemma na_isLam_or_isConstruct_etaExpand_args:
  forall na actualArgs computedArgs,
    (forall F:Terms -> Term,
        isLambda
          (etaExpand_args
             na actualArgs (fun b => TLambda nAnon (F b)) computedArgs)) \/
    (forall i m (F:Terms -> Terms),
        isConstruct
          (etaExpand_args
             na actualArgs (fun b => TConstruct i m (F b)) computedArgs)).
Proof.
  intros. destruct (le_lt_dec (tlength actualArgs) na).
  - left. intros. eapply na_isLambda_etaExpand_args. omega.
  - right. intros. eapply na_isConstruct_etaExpand_args. omega.
Qed.
 ***************)

Lemma pre_isConstruct_etaExpand:
  forall i m,
    etaExpand i m tnil 0 0 = TConstruct i m tnil.
Proof.
  cbn. intuition.
Qed.

(*************
Lemma etaExpand_no_params:
  forall (actualArgs:Terms) (nargs:nat) i m,
    etaExpand i m actualArgs 0 nargs =
    etaExpand_args nargs actualArgs (TConstruct i m) tnil.
Proof.
  intros. cbn. destruct actualArgs; reflexivity.
Qed.

Goal
  forall (npars nargs:nat) (params actualArgs:Terms) (F:Terms -> Term),
    npars > tlength params ->
    etaExpand F (tappend params actualArgs) npars nargs =
    etaExpand_args nargs actualArgs F tnil.
Proof.
  induction params; intros; cbn.
  - destruct npars. omega. destruct actualArgs; cbn.

    induction npars; intros; cbn.
  - destruct params; cbn.
    + destruct actualArgs; try reflexivity.
    + omega.
  - destruct params; cbn.
    + erewrite <- IHnpars.

    try reflexivity. rewrite <- IHparams. reflexivity.
Qed.


Goal
  forall (actualArgs:Terms) (npars nargs:nat)
         (F:Terms -> Term) (computedArgs:Terms),
    tlength actualArgs < npars ->
    etaExpand F computedArgs actualArgs npars nargs =
    etaExpand_args nargs actualArgs F computedArgs.
Proof.


Goal
  forall (actualArgs:Terms) (npars nargs:nat)
  (F:Terms -> Term) (computedArgs:Terms),
    tlength actualArgs >= npars ->
    etaExpand F computedArgs actualArgs npars nargs =
    etaExpand_args nargs actualArgs F computedArgs.
Proof.
  induction actualArgs; destruct npars; cbn; intros;
    try omega; try reflexivity.
  assert (j: tlength actualArgs >= npars). omega.
  
  rewrite (IHactualArgs _ _ F tnil j).


  
  Lemma pre_isLambda_etaExpand:
  forall np na F,
    isLambda
      (etaExpand (fun b : Terms => TLambda nAnon (F b)) tnil tnil np na).
Proof.
  induction np; intros.
  - cbn. induction na; cbn.
    + auto.
    + unfold etaExpand_args.
  - cbn. apply IHnp. 


      (****************)
Goal
  forall actualArgs np na computedArgs (F:Terms -> Term),
    S (tlength actualArgs) < np ->
      isLambda (etaExpand (fun b => F b) computedArgs actualArgs np na).
Proof.
  induction actualArgs; induction np; intros; try omega.
  - assert (j: np = S (pred np)). cbn in H. omega.
    rewrite j in *. cbn.
    change
      (isLambda
         (etaExpand (fun b : Terms => TLambda nAnon (TLambda nAnon (F b))) tnil
                    tnil np na)).


    Lemma pre_isConstruct_etaExpand:
      forall np na F,
  isLambda
    (etaExpand
       (fun b : Terms => TLambda nAnon (TLambda nAnon (TLambda nAnon (F b))))
       tnil tnil (S np) na).



  ) \/
    (forall i m (F:Terms -> Terms),
        isConstruct
          (etaExpand_args
             na actualArgs (fun b => TConstruct i m (F b)) computedArgs)).
Proof.
  intros.
  intros. destruct (le_lt_dec (tlength actualArgs) na).
  - left. intros. split. omega. eapply na_isLambda_etaExpand_args. omega.
  - right. intros. split. omega. eapply na_isConstruct_etaExpand_args. omega.
Qed.
    
Proof.
  induction np; induction na; induction computedArgs; induction actualArgs;
    cbn; intros; auto.
  - eapply na_isLambda_etaExpand_args. cbn. omega.
  - destruct (na_isLam_or_isConstruct_etaExpand_args na actualArgs (tunit t)).
    + destruct (H F) as [x0 [x1 jx]]. rewrite jx. auto.
    +
  - destruct (dec_le (tlength actualArgs) na F).
    + eapply na_isLambda_etaExpand_args. omega.
    +
                                                      
    + admit.
    + 
  - eapply na_isLambda_etaExpand_args. cbn. omega.
  - eapply na_isLambda_etaExpand_args. 


  Lemma isLambda_etaExpand:
  forall nallArgs np,
    np > nallArgs ->
    forall computedArgs actualArgs,
          nallArgs = tlength computedArgs + tlength actualArgs ->
    forall na (F:Terms -> Term),
      isLambda (etaExpand F computedArgs actualArgs np na).
Proof.
  induction nallArgs; intros np; case_eq np; intros; cbn; try omega. 
  - assert (j0: computedArgs = tnil). admit.
    assert (j1: actualArgs = tnil). admit.
    subst. cbn.
    Check (@IHnp 0 _ tnil tnil).
    subst computedArgs. cbn.
    eapply IHnp.
    cbn.

    assert (j: np = S (pred np) \/ na = S (pred na)). omega. destruct j.
    + rewrite H1 in *. eapply IHnpa.
      * cbn. omega.
      * replace (S (Init.Nat.pred np) + na)
          with (S (Init.Nat.pred np + na)) in H0; try omega.

  
  - assert (j: np = 0 /\ na = 0). omega. destruct j. subst. cbn. auto.
  - assert (j: np = S (pred np) \/ na = S (pred na)). omega. destruct j.
    + rewrite H1 in *. cbn. eapply IHnpa.
      * cbn. omega.
      * replace (S (Init.Nat.pred np) + na)
          with (S (Init.Nat.pred np + na)) in H0; try omega.
    + rewrite H1 in *.
      replace (np + S (Init.Nat.pred na))
          with (S (np + Init.Nat.pred na)) in H0; try omega.
      myInjection H0. 
      eapply (IHnpa ).
      * cbn. omega.
      * apply f_equal2. reflexivity. rewrite H1 at 2. cbn.



      eapply IHnpa.
      * cbn. omega.
      * replace (np + S (Init.Nat.pred na))
          with (S (np + Init.Nat.pred na)) in H0; try omega.
        myInjection H0. apply f_equal2. reflexivity.

        rewrite H1. cbn.

      
    eapply isLambda_etaExpand_args. cbn. assumption.
  - eapply IHnp. omega.
Qed.

Lemma isLambda_etaExpand:
  forall np na actualArgs,
    na >= tlength actualArgs ->
    forall (F:Terms -> Term) computedArgs,
      isLambda (etaExpand (fun b : Terms => TLambda nAnon (F b))
                          computedArgs actualArgs np na).
Proof.
  induction np; induction actualArgs; cbn; intros; try omega; auto.
  - eapply isLambda_etaExpand_args. cbn. omega.
  - eapply isLambda_etaExpand_args. cbn. assumption.
  - eapply IHnp. omega.
Qed.

Lemma isConstruct_etaExpand:
  forall np na actualArgs,
    na < tlength actualArgs ->
    forall i m (F:Terms -> Terms) computedArgs,
      isConstruct
        (etaExpand (fun b : Terms => TConstruct i m (F b))
                   computedArgs actualArgs np na).
Proof.
  induction np; induction actualArgs; cbn; intros; try omega; auto.
  - eapply isConstruct_etaExpand_args. cbn. omega.
  - eapply (IHnp ).
Qed.
 ****************)


(*******************
Goal
  forall actualArgs np na,
    np + na = tlength actualArgs ->
      forall i m computedArgs,
        isConstruct (etaExpand (fun b => TConstruct i m b)
                               computedArgs actualArgs np na).
Proof.
  induction actualArgs; intros; cbn in H.
  - assert (jnp: np = 0). omega.
    assert (jna: na = 0). omega. subst. cbn. auto.
  - assert (k: np = S (pred np) \/ na = S (pred na)). omega. destruct k.
    + rewrite H0. cbn. refine (IHactualArgs _ _ _ _ _ _).
      rewrite H0 in H. omega.
    + destruct np.
      rewrite H0 in *. cbn in *. myInjection H. refine (IHactualArgs _ _ _ _ _ _).
      rewrite H0 in H. omega.

      Check (IHactualArgs (S np) na _ i m computedArgs).

Proof.
  induction npa; induction actualArgs; cbn; intros; try discriminate.
  - assert (jnp: np = 0). omega.
    assert (jna: na = 0). omega. subst. cbn. auto.
  - assert (j0: np = S (tlength actualArgs) - na). omega.
    assert (j1: na = S (tlength actualArgs) - np). omega.
    assert (k: np = S (pred np) \/ na = S (pred na)). omega. destruct k.
    + assert (k0: npa = tlength actualArgs). omega.
      Check (IHnpa

      rewrite j0. cbn. destruct na; cbn in *.
    + assert (j1: np = S npa). omega. Check (IHactualArgs


    assert (j1: na = S (tlength actualArgs) - np). omega.

    
Goal
  forall actualArgs np na computedArgs,
    (forall F, isLambda (etaExpand F computedArgs actualArgs np na)) \/
    (forall i m, isConstruct (etaExpand (fun b => TConstruct i m b)
                           computedArgs actualArgs np na)) \/
    (forall F, isWrong (etaExpand F computedArgs actualArgs np na)).
Proof.
  induction actualArgs; induction np; induction na; cbn; intros.
  - right. auto.
  - assert (j: na >= tlength tnil). cbn. omega.
    left. intros.
    apply (@isLambda_etaExpand_args
             na tnil j F (tappend (lifts 0 computedArgs) (tunit (TRel 0)))).
  - assert (j: 0 >= tlength tnil). cbn. omega.
    left. intros.
    apply (@isLambda_etaExpand np 0 tnil j F tnil).
  - assert (j: S na >= tlength tnil). cbn. omega.
    left. intros.
    apply (@isLambda_etaExpand np (S na) tnil j F tnil).
  - intuition.
  - right. left.

 Goal
  forall actualArgs np na computedArgs i m,
    isLambda (etaExpand (fun b => TConstruct i m b)
                        computedArgs actualArgs np na) \/
    isConstruct (etaExpand (fun b => TConstruct i m b)
                           computedArgs actualArgs np na) \/
    isWrong (etaExpand (fun b => TConstruct i m b)
                           computedArgs actualArgs np na).
Proof.
  induction actualArgs; induction np; induction na; cbn; intros.
  - right. auto.
  - assert (j: na >= tlength tnil). cbn. omega.
    left.
    apply (@isLambda_etaExpand_args
             na tnil j (fun b => TConstruct i m b)
             (tappend (lifts 0 computedArgs) (tunit (TRel 0)))).
  - assert (j: 0 >= tlength tnil). cbn. omega.
    left.
    apply (@isLambda_etaExpand np 0 tnil j (fun b => TConstruct i m b) tnil).
  - assert (j: S na >= tlength tnil). cbn. omega.
    left.
    apply (@isLambda_etaExpand np (S na) tnil j (fun b => TConstruct i m b) tnil).
  - intuition.
  -
 ***************************)  


    (************
Lemma etaExpand_np_up:
  forall np na actualArgs (F:Terms -> Term) computedArgs,
    isLambda (etaExpand F computedArgs actualArgs np na) ->
    isLambda (etaExpand F computedArgs actualArgs (S np) na).
Proof.
  intros. cbn. destruct actualArgs.
  - cbn.

  functional induction (etaExpand F computedArgs actualArgs np na).
  - cbn. refine (isLambda_etaExpand_args _ _ _ _). cbn. omega.
  - cbn.

  - cbn in *. destruct actualArgs.
    + refine (isLambda_etaExpand_args _ _ _ _). cbn. omega.
    +
  - cbn. destruct actualArgs.
    assert (j: na = 0 \/ na = S (pred na)). omega. destruct j.
    + subst. cbn. auto.
    + rewrite H0. refine (etaExpand_args_up _ _ _ _ _).



      Lemma etaExpand_np_up:
  forall np na actualArgs (F:Terms -> Term) computedArgs,
    isLambda (etaExpand F computedArgs actualArgs np na) ->
    isLambda (etaExpand (fun b => TLambda nAnon (F b))
                        computedArgs actualArgs (S np) na).
Proof.
  induction np; induction actualArgs; intros.
  - cbn in *. 
    + refine (isLambda_etaExpand_args _ _ _ _). cbn. omega.
  - cbn. destruct actualArgs.
    assert (j: na = 0 \/ na = S (pred na)). omega. destruct j.
    + subst. cbn. auto.
    + rewrite H0. refine (etaExpand_args_up _ _ _ _ _).
      
Goal
  forall npa np na,
    npa = np + na ->
    forall actualArgs, npa >= tlength actualArgs ->
    forall (F:Terms -> Term) computedArgs,
      isLambda (etaExpand (fun b => TLambda nAnon (F b))
                          computedArgs
                          actualArgs np na).
Proof.
  induction npa; induction actualArgs; cbn; intros; try omega; auto.
  - assert (j: np = 0 /\ na = 0). omega. destruct j. subst. cbn. auto.
  - assert (j: np > 0 \/ na > 0). omega. destruct j.
    assert (j0: npa = pred (np + na)). omega.
    + refine (IHnpa (pred np) na _ tnil _ _ _). omega.




      Goal
  forall (np na:nat) (actualArgs:Terms),
    np + na > tlength actualArgs ->
    forall (i: inductive) (r: nat) (computedArgs:Terms),
      isLambda (etaExpand (fun b : Terms => TConstruct i r b)
                          computedArgs actualArgs np na).
Proof.
  induction np; induction na; induction actualArgs;
    cbn; intros; try omega.
  - specialize (IHna tnil). cbn in IHna.
  

Goal
  forall na np i r, na > 0 -> isLambda (strip (L2.compile.TConstruct i r np na)).
Proof.
  cbn. intros.
  induction na; intros; try omega. cbn.
  specialize (IHna 0 i r). cbn in IHna.
  
  - cbn. replace np with (S (pred np)); try omega.
    cbn.

    induction na.
  - destruct np.
    + cbn. auto.
    + cbn. cbn in IHnp.
      specialize (IHnp i r). cbn in IHnp.

  - induction na; cbn.
    + right. auto.
    + unfold etaExpand_args.
    
    assert (j1: na = 0). omega. subst. cbn. right. auto.
  - assert (j: np <> 0 \/ na <> 0). omega. destruct j.
    + assert (j: np = S (pred np)). omega. rewrite j in *. cbn.
Admitted.
*******************)

(***********
Goal
  forall npa np na i r, npa = np + na ->
         isLambda
         (etaExpand (np + na)
                    (fun b : Terms => TLambda nAnon (TConstruct i r b)) tnil tnil np na).
Proof.
  intros.
  functional induction (etaExpand (np + na)
                    (fun b : Terms => TLambda nAnon (TConstruct i r b)) tnil tnil np na).
  induction npa; intros; cbn.
  - assert (j0: np = 0). omega.
    assert (j1: na = 0). omega. subst. cbn. auto. 
  - assert (j: np <> 0 \/ na <> 0). omega. destruct j.
    + assert (j: np = S (pred np)). omega. rewrite j in *. 
      assert (j0: npa = Init.Nat.pred np + na). omega.
      specialize (IHnpa (pred np) _ i r j0). 


      unfold etaExpand. case_eq na; intros; subst. auto.

    
  - rewrite <- H. cbn. destruct np. destruct na.
    + omega.
    + cbn in H. myInjection H. cbn in IHnpa.


  induction np; induction na.
  - cbn. right. auto.
  - cbn. destruct na.
    + cbn. left. auto.
    + cbn in IHna.
      
    unfold etaExpand.
****************)



    
  (******************
Goal
  forall args npars nargs i n,
    tlength args >= npars + nargs ->
    isConstruct
      (etaExpand
         (npars + nargs) (fun b : Terms => TConstruct i n b)  tnil args npars nargs).
Proof.
  induction args; cbn; intros.
  - assert (j0: npars = 0). omega.
    assert (j1: nargs = 0). omega.
    subst. cbn. auto.
  - assert (npars >= S (pred npars) \/ nargs >= S (pred nargs)). omega.
    destruct H0.
    + rewrite H0 in H. myInjection H.
     specialize (IHargs (Init.Nat.pred npars) nargs i n H1).       
      rewrite H0. cbn. assumption.
    + rewrite H0 in H.
       replace (npars + S (Init.Nat.pred nargs))
        with (S (npars + (Init.Nat.pred nargs))) in H; try omega.
      myInjection H.
      specialize (IHargs npars (Init.Nat.pred nargs) i n H1).


      Goal
  forall args npars nargs i n,
    tlength args = npars + nargs ->
    isConstruct
      (etaExpand
         (npars + nargs) (fun b : Terms => TConstruct i n b)  tnil args npars nargs).
Proof.
  induction args; cbn; intros.
  - assert (j0: npars = 0). omega.
    assert (j1: nargs = 0). omega.
    subst. cbn. auto.
  - assert (npars = S (pred npars) \/ nargs = S (pred nargs)). omega.
    destruct H0.
    + rewrite H0 in H. myInjection H.
     specialize (IHargs (Init.Nat.pred npars) nargs i n H1).       
      rewrite H0. cbn. assumption.
    + rewrite H0 in H.
       replace (npars + S (Init.Nat.pred nargs))
        with (S (npars + (Init.Nat.pred nargs))) in H; try omega.
      myInjection H.
      specialize (IHargs npars (Init.Nat.pred nargs) i n H1).
      rewrite <- H0. 
      rewrite H0 in H1.

      
      replace (npars + S (Init.Nat.pred nargs))
        with (S (npars + (Init.Nat.pred nargs))); try omega.
      specialize (IHargs npars (Init.Nat.pred nargs) i n H1). cbn. assumption.

      
      cbn.
      cbn in H. myInjection H.
      
      rewrite H0 in IHargs. cbn in IHargs.


    
  Lemma etaExpandSanity:
  forall fuel npars nargs args i n,
    fuel = npars + nargs ->
    tlength args < npars  ->
    isLambda (etaExpand (npars + nargs)
                        (fun b : Terms => TConstruct i n b) tnil args npars nargs).
Proof.
  induction fuel; cbn; intros; try omega.
  destruct npars, nargs; try omega.
  - assert (j0: fuel = npars + 0). omega.
      Check (IHfuel (S npars) 0). _ _ _ j0).
    
  induction npars; intros.
  - destruct args, nargs; cbn in H; omega.
  - destruct args, nargs; cbn in *.
    + eapply IHnpars.
    tlength args <= nargs  ->
    isLambda (etaExpand (npars + nargs)
                        (fun b : Terms => TConstruct i n b) tnil args npars nargs) /\
    
    
    isConstruct
      (etaExpand (npars + nargs)
                 (fun b : Terms => TConstruct i n b) tnil args npars nargs).
Proof.
  induction args; intros.
  - destruct npars.
    + cbn. destruct nargs.
      * cbn. auto.
      * cbn. 
  
  intros. induction npars; induction nargs; cbn; intros.
  - destruct args. auto. unfold tlength in H. omega.
  - destruct args. cbn in IHnargs.
 ******************)

(***
Lemma mkEtaLams_sanityS:
  forall (xtra:nat) (body:Term), isLambda (mkEtaLams (S xtra) body).
Proof.
  intros. cbn. auto.
Qed.
 ***)

Definition isCase (t:Term) : Prop :=
  exists i mch ds, t = TCase i mch ds.

Lemma isCase_dec: forall t, {isCase t}+{~ isCase t}.
Proof.
  destruct t; try (solve[right; not_isCase]).
  left. unfold isCase. exists i, t, b. reflexivity.
Qed.
Lemma IsCase: forall i mch ds, isCase (TCase i mch ds).
Proof.
  intros. exists i, mch, ds. reflexivity.
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

Definition isProof (t:Term) : Prop := exists s, t = TProof s.
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

Definition isDummy (t:Term) : Prop := exists s, t = TDummy s.
Lemma IsDummy: forall t, isDummy (TDummy t).
intros. exists t. reflexivity.
Qed.
Hint Resolve IsDummy.
Lemma isDummy_dec: forall t, {isDummy t}+{~ isDummy t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. auto.
Defined.

Inductive isCanonical : Term -> Prop :=
| canC: forall (i:inductive) (n:nat) args, isCanonical (TConstruct i n args)
| canP: forall t, isCanonical t -> isCanonical (TProof t).
Hint Constructors isCanonical.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
Proof.
  induction t; try (solve [right; intros h; inversion h; inversion H;
                           destruct H1; discriminate]).
  - destruct IHt.
    + left. constructor. assumption.
    + right. intros h. inversion_clear h. contradiction.
  - left. constructor.
Qed.
     
Function canonicalP (t:Term) : option  (nat * Terms) :=
  match t with
    | TConstruct _ r args => Some (r, args)
    | TProof t => canonicalP t
    | _ => None
  end.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Some x -> isCanonical t.
Proof.
  induction t; simpl; intros; try discriminate.
  - constructor. eapply IHt. eassumption.
  - constructor.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x, canonicalP t = Some x.
Proof.
  induction 1; simpl.
  - exists (n, args). reflexivity.
  - assumption.
Qed.


(** some utility operations on [Terms] ("lists" of Term) **)
Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
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

Lemma lifts_tappend:
  forall n ts us,
  lifts n (tappend ts us) = tappend (lifts n ts) (lifts n us).
Proof.
  induction ts; intros.
  - reflexivity.
  - change
      (lifts n (tcons t (tappend ts us)) =
       tcons (lift n t) (tappend (lifts n ts) (lifts n us))).
    rewrite <- IHts. reflexivity.
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
    
Lemma tnth_tlength_sanity:
  forall fsts t lsts,
    tnth (tlength fsts) (tappend fsts (tcons t lsts)) = Some t.
Proof.
  induction fsts0; intros. reflexivity.
  - cbn. apply IHfsts0.
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

(** operations on Defs **)
Function dnthBody (n:nat) (l:Defs) {struct l} : option Term :=
  match l with
    | dnil => None
    | dcons _ x _ t => match n with
                           | 0 => Some x
                           | S m => dnthBody m t
                         end
  end.

Function bnth (n:nat) (l:Brs) {struct l} : option (Term) :=
  match l with
    | bnil => None
    | bcons _ x bs => match n with
                           | 0 => Some x
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

Definition is_bunit (ds:Brs) : Prop :=
  exists (n:nat) (s:Term), ds = bunit n s.

Lemma is_bunit_blength:
  forall ds, is_bunit ds <-> blength ds = 1.
Proof.
  intros ds. split; intros h.
  - destruct h as [x0 [x1 jx]]. subst ds. reflexivity.
  - destruct ds.
    + discriminate.
    + destruct ds.
      * exists n, t. reflexivity.
      * discriminate.
Qed.

Lemma is_bunit_dec: forall ds, is_bunit ds \/ ~ (is_bunit ds).
Proof.
  intros ds. case_eq ds; intros.
  - right. intros h. destruct h as [x0 [x1 jx]]. discriminate.
  - case_eq b; intros; subst.
    + left. exists n, t. reflexivity.
    + right. intros h.
      pose proof (proj1 (is_bunit_blength
                           (bcons n t (bcons n0 t0 b0))) h).
      discriminate.
Qed.

(*******************
(** syntactic control of "TApp": no nested apps, app must have an argument **)
Lemma mkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, mkApp fn (tcons arg args) = TApp fn arg args.
induction fn; simpl; intros h arg args; try (constructor; assumption).
- elim h. exists fn1, fn2, t. reflexivity.
Qed.

Goal
  forall args fn arg,
    isApp (mkApp fn args) -> isApp (mkApp fn (tcons arg args)).
Proof.
  intros args fn. functional induction (mkApp fn args); intros.
  - unfold mkApp. rewrite e. assumption.
  - unfold mkApp. rewrite e. functional inversion e; subst.
    + cbn. rewrite H1. auto.
    + cbn. rewrite e. auto.
  - destruct H as [x0 [x1 jx]].
    change (mkApp (TApp fn y) ys = TApp x0 x1) in jx.
    change (match eatsArgs (TApp fn y) with
            | Some tc => tc
            | None => match ys with
                      | tnil => (TApp fn y)
                      | tcons u us => mkApp (TApp (TApp fn y) u) us
                      end
            end = TApp x0 x1) in jx.


    unfold mkApp in jx. rewrite e in jx.

    cbn. rewrite e. cbn. destruct H as [x0 [x1 jx]]. rewrite jx.

    assumption.
  induction brgs; intros.
  - rewrite tappend_tnil. assumption.
  - rewrite tappend_tcons. apply IHbrgs.
    destruct (tappend_mk_canonical args t tnil) as [x0 [x1 jx]].
    change (isApp (mkApp fn (tappend args (tunit t)))).
    rewrite jx.

    
Goal
  forall brgs fn args, isApp (mkApp fn args) ->
                  isApp (mkApp fn (tappend args brgs)).
Proof.
  induction brgs; intros.
  - rewrite tappend_tnil. assumption.
  - rewrite tappend_tcons. apply IHbrgs.
    destruct (tappend_mk_canonical args t tnil) as [x0 [x1 jx]].
    change (isApp (mkApp fn (tappend args (tunit t)))).
    rewrite jx.


    Goal
  forall fn args, isApp (mkApp fn args) ->
                  forall brgs, isApp (mkApp fn (tappend args brgs)).
Proof.
  intros fn args h0 brgs. functional induction (mkApp fn args).
  - cbn.




         Lemma mkApp_isApp:
  forall fn, eatsArgs fn = None ->
             forall arg args, isApp (mkApp fn (tcons arg args)).
Proof.
  intros fn. functional induction (eatsArgs fn); intros; try discriminate.
  - cbn. rewrite H. specialize (IHo cbn

  
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
  - exists (TConstruct i n t), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase i fn b), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TWrong s), arg, tnil. cbn.  split. reflexivity.
    left. repeat split. not_isApp.
  - exists TDummy, arg, tnil. cbn.  split. reflexivity.
    left. repeat split. not_isApp.
  - exists TInd, arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
Qed.
 *********************)

Lemma lift_App:
  forall fn arg n,
    lift n (TApp fn arg) = TApp (lift n fn) (lift n arg).
  reflexivity.
Qed.

Lemma isApp_lift_isApp:
  forall t n, isApp (lift n t) -> isApp t.
Proof.
  induction t; cbn; intros;
  destruct H as [x0 [x1 jx]]; try discriminate. auto.
Qed.

Lemma lift_pres_isApp:
  forall t, isApp t -> forall n, isApp (lift n t).
Proof.
  destruct t; intros; destruct H as [x0 [x1 jx]]; try discriminate.
  cbn. auto.
Qed.

Lemma lift_pres_isApp_contra:
  forall t n, isApp (lift n t) -> isApp t.
Proof.
  destruct t; intros; destruct H as [x0 [x1 jx]]; try discriminate.
  cbn in jx. myInjection jx. auto.
Qed.

(**********
Lemma lift_mkApp:
  forall n fn args, lift n (mkApp fn args) = mkApp (lift n fn) (lifts n args).
Proof.
  intros. destruct args.
  - rewrite mkApp_tnil. unfold lifts. rewrite mkApp_tnil. reflexivity.
  - destruct (isApp_dec fn).
    + destruct i as [x0 [x1 jx]]. subst. cbn.
      change
        (lift n (mkApp (TApp (TApp x0 x1) t) args) =
         mkApp (TApp (lift n x0) (lift n x1)) (lifts n (tcons t args))).
      change
        (lift n (TApp x0 (mkApp (TApp (TApp x0 x1) t) args) =
         mkApp (TApp (lift n x0) (lift n x1)) (lifts n (tcons t args))).
      
      apply f_equal3; try reflexivity.
      rewrite lifts_tappend. reflexivity.
    + rewrite mkApp_goodFn; try assumption.
      unfold lifts. rewrite mkApp_goodFn. reflexivity.
      intros h. elim n0. eapply isApp_lift_isApp. eassumption.
Qed.
*******************)

(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaProof: forall tm, WFapp tm -> WFapp (TProof tm)
| wfaLambda: forall nm bod, WFapp bod -> WFapp (TLambda nm bod)
| wfaLetIn: forall nm dfn bod,
    WFapp dfn -> WFapp bod -> WFapp (TLetIn nm dfn bod)
| wfaApp: forall fn t, WFapp fn -> WFapp t -> WFapp (TApp fn t)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaConstruct: forall i m1 args,
    WFapps args -> WFapp (TConstruct i m1 args)
| wfaCase: forall i mch brs,
    WFapp mch -> WFappBs brs -> WFapp (TCase i mch brs)
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

Lemma treverse_pres_WFapps:
  forall ts, WFapps ts -> WFapps (treverse ts).
Proof.
  induction 1. constructor. cbn.
  apply tappend_pres_WFapps. assumption.
  constructor. assumption. constructor.
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

(************
Lemma WFapp_mkApp_TApp:
  forall u, WFapp u -> forall t a1, u = (TApp t a1) ->
    mkApp t (tcons a1 args) = TApp t a1 args.
Proof.
  induction 1; intros; try discriminate.
  - injection H3. intros. subst. rewrite (mkApp_cons_App H). reflexivity.
Qed.

Lemma WFapp_mkApp_WFapp:
  forall u, WFapp u -> forall t args, u = mkApp t args ->
       WFapp t /\ WFapps args .
Proof.
  induction 1; intros tx argsx h.
  destruct tx, argsx; try rewrite mkApp_tnil in h; try discriminate.
  
  try (destruct tx, argsx; simpl in h; try discriminate;
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
 ***************)

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

Lemma bnth_pres_WFapp:
  forall (brs:Brs), WFappBs brs ->
                    forall n t, bnth n brs = Some t-> WFapp t.
Proof.
  intros brs h n t.
  functional induction (bnth n brs); intros; try discriminate.
  - myInjection H. inversion h. assumption.
  - eapply IHo; inversion h; eassumption.
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


Lemma lifts_pres_WFapps:
  (forall t, WFapp t -> forall n, WFapp (lift n t)) /\
  (forall ts, WFapps ts -> forall n, WFapps (lifts n ts)) /\
  (forall ts, WFappBs ts -> forall n, WFappBs (liftBs n ts)) /\
  (forall ds, WFappDs ds -> forall n, WFappDs (liftDs n ds)).
Proof.
  apply WFappTrmsBrsDefs_ind; cbn; intros; try (constructor; intuition).
Qed.                             

(**********
Lemma addDummyArgs_pres_WFapps:
  forall n args, WFapps args -> WFapps (addDummyArgs n args).
Proof.
  induction n; intros; cbn.
  - apply treverse_pres_WFapps. assumption.
  - apply IHn. constructor. constructor. apply lifts_pres_WFapps. assumption.
Qed.               
            
Lemma mkEtaArgs_pres_WFapps:
  forall np na args, WFapps args -> WFapps (mkEtaArgs np na args).
Proof.
  induction np; intros; cbn.
  - apply addDummyArgs_pres_WFapps. apply treverse_pres_WFapps. assumption.
  - induction args.
    + apply addDummyArgs_pres_WFapps. constructor.
    + apply IHnp. inversion_Clear H. assumption.
Qed.               

Lemma mkEtaLams_pres_WFapp:
  forall n bod, WFapp bod -> WFapp (mkEtaLams n bod).
Proof.
  induction n; intros; cbn.
  - assumption.
  - constructor. intuition.
Qed.

Lemma manyMore_pres_WFapps:
  forall args, WFapps args -> forall i x na, WFapp (manyMore i x na args).
Proof.
  induction 1; intros.
  - induction na.
    + cbn. constructor. constructor.
    + change (WFapp (ec_rec (oneMore b) m

                (manyMore i x (S na) tnil))


    
Qed.

Lemma etaExp_cnstr_pres_WFapp:
  forall args, WFapps args ->
               forall np i x na, WFapp (etaExp_cnstr i x np na args).
Proof.
  induction 1; intros.
  - induction np.
    + cbn.

    
  intros. unfold etaExp_cnstr. apply mkEtaLams_pres_WFapp.
  constructor. apply mkEtaArgs_pres_WFapps. assumption.   
Qed.
  
Lemma etaExp_cnstr_sanity:
  forall (i:inductive) (x npars nargs:nat) (args:Terms),
    match (npars + nargs) - (tlength args) with
    | 0 => etaExp_cnstr i x npars nargs args =
           TConstruct i x (mkEtaArgs npars nargs args)
    | S a =>
      (etaExp_cnstr i x npars nargs args) =
      TLambda nAnon
              (mkEtaLams a (TConstruct i x (mkEtaArgs npars nargs args)))
    end.
Proof.
  intros. unfold etaExp_cnstr.
  case_eq (npars + nargs - tlength args); intros h; cbn.
  - reflexivity.
  - intros. reflexivity.
Qed.
 ********************)

(******************
Lemma etaExp_cnstr_Sanity:
  forall (i:inductive) (x npars nargs:nat) (args:Terms),
    let xx := npars + nargs - (tlength args) in
    (xx = 0 /\ isConstruct (etaExp_cnstr i x npars nargs args))
    \/ ((exists z, xx = S z) /\
        isLambda (etaExp_cnstr i x npars nargs args)).
Proof.
  intros i x npars nargs args xx. unfold xx.
  assert (j:= etaExp_cnstr_sanity i x npars nargs args).
  case_eq xx.
  - intros k. unfold xx in k. rewrite k in j. left. intuition.
  - intros m k. unfold xx in k. rewrite k in j. right. intuition.
    exists m. assumption.    
Qed.

Lemma etaExp_cnstr_Sanity':
  forall (i:inductive) (x npars nargs:nat) (args:Terms),
    etaExp_cnstr i x npars nargs args =
    TConstruct i x (mkEtaArgs npars nargs args) \/
    etaExp_cnstr i x npars nargs args =
    TLambda nAnon
            (mkEtaLams (pred ((npars + nargs) - (tlength args)))
                       (TConstruct i x (mkEtaArgs npars nargs args))).
Proof.
  intros. assert (j:= etaExp_cnstr_sanity i x npars nargs args).
  destruct (npars + nargs - tlength args).
  - left. assumption.
  - right. exact j. 
Qed.

Lemma strip_pres_isApp:
  forall t, isApp (strip t) -> L2.term.isApp t.
Proof.
  induction t; intros h; 
    destruct h as [x0 [x1 [x2 jx]]]; try discriminate.
  - destruct (L2.term.isConstruct_dec t1).
    + destruct i as [y0 [y1 [y2 [y3 jy]]]]. subst. auto.
    + destruct t1; try auto.
  - cbn in jx. pose proof (etaExp_cnstr_sanity i n n0 n1 tnil) as h.
    destruct (n0 + n1 - tlength tnil); rewrite jx in h; discriminate.
  - destruct p. cbn in jx. discriminate.        
Qed.
 ***************)


(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfProof: forall n t, WFTrm t n -> WFTrm (TProof t) n
| wfLambda: forall n nm bod,
    WFTrm bod (S n) -> WFTrm (TLambda nm bod) n
| wfLetIn: forall n nm dfn bod,
    WFTrm dfn n -> WFTrm bod (S n) ->
    WFTrm (TLetIn nm dfn bod) n
| wfApp: forall n fn t, WFTrm fn n -> WFTrm t n -> WFTrm (TApp fn t) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfConstruct: forall n i m args,
    WFTrms args n -> WFTrm (TConstruct i m args) n
| wfCase: forall n i mch brs,
    WFTrm mch n -> WFTrmBs brs n ->
    WFTrm (TCase i mch brs) n
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
         from WFTrm_ind', WFTrms_ind',  WFTrmBs_ind', WFTrmDs_ind'.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall ts n, WFTrms ts n -> WFapps ts) /\
  (forall ts n, WFTrmBs ts n -> WFappBs ts) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try (constructor; try assumption).
Qed.

Lemma WF_nolift:
  (forall t n, WFTrm t n -> forall i, n <= i -> lift i t = t) /\
  (forall ts n, WFTrms ts n -> forall i, n <= i -> lifts i ts = ts) /\
  (forall ts n, WFTrmBs ts n -> forall i, n <= i -> liftBs i ts = ts) /\
  (forall ds n, WFTrmDs ds n -> forall i, n <= i -> liftDs i ds = ds).  
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H0; try reflexivity; omega);
  try (cbn; rewrite H0, H2; try reflexivity; omega).
  - cbn. case_eq (m ?= i); intros; Compare_Prop; try omega. reflexivity.
Qed.

Remark ClosedTermsNoLift:
  forall t, WFTrm t 0 -> forall i, lift i t = t.
Proof.
  intros. eapply WF_nolift. eassumption. omega.
Qed.                                           

Lemma WF_lift_closed:
  forall t n, WFTrm t n -> WFTrm (lift n t) n.
Proof.
  intros. pose proof (proj1 WF_nolift _ _ H n) as h. rewrite h; try omega.
  assumption.
Qed.                                            

Lemma WF_lifts_closed:
  forall ts n, WFTrms ts n -> WFTrms (lifts n ts) n.
Proof.
  intros. pose proof (proj1 (proj2 WF_nolift) _ _ H n) as h.
  rewrite h; try omega. assumption.
Qed.                                            

Lemma WF_liftBs_closed:
  forall ts n, WFTrmBs ts n -> WFTrmBs (liftBs n ts) n.
Proof.
  intros. pose proof (proj1 (proj2 (proj2 WF_nolift)) _ _ H n) as h.
  rewrite h; try omega. assumption.
Qed.                                            

Lemma WF_liftDs_closed:
  forall ts n, WFTrmDs ts n -> WFTrmDs (liftDs n ts) n.
Proof.
  intros. pose proof (proj2 (proj2 (proj2 WF_nolift)) _ _ H n) as h.
  rewrite h; try omega. assumption.
Qed.                                            

 
Lemma WFTrm_up:
  (forall t m, WFTrm t m -> WFTrm t (S m)) /\
  (forall ts m, WFTrms ts m -> WFTrms ts (S m)) /\
  (forall ts m, WFTrmBs ts m -> WFTrmBs ts (S m)) /\
  (forall ds m, WFTrmDs ds m -> WFTrmDs ds (S m)).
Proof.
  apply WFTrmTrmsBrsDefs_ind; cbn; intros; constructor; try assumption; omega.
Qed.
  
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

Lemma lift_pres_WFTrm:
  (forall t m, WFTrm t m -> forall n, WFTrm (lift n t) (S m)) /\
  (forall ts m, WFTrms ts m -> forall n, WFTrms (lifts n ts) (S m)) /\
  (forall ts m, WFTrmBs ts m -> forall n, WFTrmBs (liftBs n ts) (S m)) /\
  (forall ds m, WFTrmDs ds m -> forall n, WFTrmDs (liftDs n ds) (S m)).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try (solve[cbn; constructor]);
  try (solve[cbn; constructor; intuition]).
  - cbn; case_eq (m ?= n0); intros; Compare_Prop; subst; constructor; omega.
  - change
      (WFTrm (TFix (liftDs (n0 + dlength defs) defs) m) (S n)).
    constructor. rewrite liftDs_pres_dlength. apply (H0 (n0 + dlength defs)).
Qed. 

Definition stableF (F:Terms -> Term) :=   (*** HERE ***)
  forall ts n, WFTrms ts (S n) -> WFTrm (F ts) n.

(********
Lemma etaExpand_args_Lam'_pres_WFTrm:
  forall nargs cArgs,
    WFTrms cArgs 0 ->
    forall (bod:Terms->Term), stableF (fun b => TLambda nAnon (bod b)) ->
    WFTrm (etaExpand_args_Lam' nargs bod cArgs) 0.
Proof.
  induction nargs; intros.
  - cbn. intuition. unfold stableF in H0. eapply H0.
    apply (proj1 (proj2 WFTrm_up)). assumption.
  - cbn. eapply IHnargs.
    + eapply tappend_pres_WFTrms.
      * apply WF_lifts_closed. assumption.
      * constructor. constructor. omega. constructor.
    + unfold stableF. intros. constructor. eapply (proj1 WFTrm_up). intuition.
Qed.

Lemma etaExpand_args_Lam_tnil_pres_WFTrm:
  forall nargs cArgs,
    WFTrms cArgs 0 ->
    forall (bod:Terms->Term), stableF bod ->
    WFTrm (etaExpand_args_Lam nargs tnil bod cArgs) 0.
Proof.
  induction nargs; intros.
  - cbn. intuition. unfold stableF in H0. eapply H0.
    apply (proj1 (proj2 WFTrm_up)). assumption.
  - cbn. eapply IHnargs.
    + eapply tappend_pres_WFTrms.
      * apply WF_lifts_closed. assumption.
      * constructor. constructor. omega. constructor.
    + unfold stableF. intros. constructor. eapply (proj1 WFTrm_up). intuition.
Qed.

Lemma etaExpand_args_Lam_tnil_pres_WFTrm:
  forall nargs cArgs n,
    WFTrms cArgs n ->
    forall (bod:Terms->Term), stableF bod ->
    WFTrm (etaExpand_args_Lam nargs tnil bod cArgs) (n + nargs).
Proof.
  induction nargs; intros.
  - cbn. replace (n + 0) with n; try omega. intuition.
  - cbn. replace (n + S nargs) with (S n + nargs); try omega. eapply IHnargs.
    + eapply tappend_pres_WFTrms.
      * eapply (proj1 (proj2 lift_pres_WFTrm)). assumption.
      * constructor. constructor. omega. constructor.
    + unfold stableF. intros. constructor. eapply (proj1 WFTrm_up). intuition.
Qed.

Lemma etaExpand_args_Lam_nargs_pres_WFTrm:
  forall aArgs cArgs n,
    WFTrms aArgs n ->
    WFTrms cArgs n ->
    forall (bod:Terms->Term), stableF bod ->
    WFTrm (etaExpand_args_Lam 0 aArgs bod cArgs) n.
Proof.
  destruct aArgs; intros.
  - cbn. unfold stableF in H1. intuition.
  - cbn. constructor.
Qed.

(** etaExpand_args_Lam preserves closedness **)
Lemma etaExpand_args_Lam_pres_WFTrm:
  forall nargs aArgs cArgs n,
    WFTrms aArgs n ->
    WFTrms cArgs n ->
    forall (bod:Terms->Term), stableF bod ->
    WFTrm (etaExpand_args_Lam nargs aArgs bod cArgs) n.
Proof.
  induction nargs; destruct aArgs; intros.
  - cbn. unfold stableF in H1. intuition.
  - cbn. constructor.
  - eapply etaExpand_args_Lam_tnil_pres_WFTrm; try assumption.
  - cbn. replace (n + S nargs) with (S n + nargs); try omega.
    eapply IHnargs; try eassumption.
    + inversion_Clear H. apply (proj1 (proj2 WFTrm_up)). assumption.
    + eapply tappend_pres_WFTrms.
      * apply (proj1 (proj2 WFTrm_up)). assumption.
      * inversion_Clear H. constructor.
        apply (proj1 WFTrm_up). assumption. constructor.
Qed.

Lemma etaExpand_args_Lam_pres_WFTrm:
  forall nargs aArgs cArgs n,
    WFTrms aArgs n ->
    WFTrms cArgs n ->
    forall (bod:Terms->Term), stableF bod ->
    WFTrm (etaExpand_args_Lam nargs aArgs bod cArgs) (n + nargs).
Proof.
  induction nargs; destruct aArgs; intros.
  - cbn. replace (n + 0) with n; try omega. unfold stableF in H1. intuition.
  - cbn. constructor.
  - eapply etaExpand_args_Lam_tnil_pres_WFTrm; try assumption.
  - cbn. replace (n + S nargs) with (S n + nargs); try omega.
    eapply IHnargs; try eassumption.
    + inversion_Clear H. apply (proj1 (proj2 WFTrm_up)). assumption.
    + eapply tappend_pres_WFTrms.
      * apply (proj1 (proj2 WFTrm_up)). assumption.
      * inversion_Clear H. constructor.
        apply (proj1 WFTrm_up). assumption. constructor.
Qed.

Lemma etaExpand_args_Construct_pres_WFTrm:
  forall nargs aArgs i m n,
    WFTrms aArgs n ->
    WFTrm (etaExpand_args_Construct nargs aArgs i m) (n + nargs).
Proof.
  destruct nargs, aArgs; intros.
  - cbn. constructor. constructor.
  - cbn. constructor.
  - cbn. replace (n + S nargs) with (S n + nargs); try omega.
    eapply etaExpand_args_Lam_pres_WFTrm.
    + constructor.
    + constructor.
      * constructor. omega.
      * constructor.
    + unfold stableF. intros. constructor. constructor.
      apply (proj1 (proj2 WFTrm_up)). assumption.
  - cbn. replace (n + S nargs) with (S n + nargs); try omega.
    eapply etaExpand_args_Lam_pres_WFTrm.
    + inversion_Clear H. apply (proj1 (proj2 WFTrm_up)). assumption.
    + inversion_Clear H.  constructor. apply (proj1 WFTrm_up). assumption.
      constructor.
    + unfold stableF. intros. constructor. assumption.
Qed.

Lemma etaExpand_pres_WFTrm:
  forall aArgs npars nargs i m n,
    WFTrms aArgs n -> WFTrm (etaExpand i m aArgs npars nargs) (n + nargs).
Proof.
  induction aArgs; destruct npars; intros.
  - cbn. eapply etaExpand_args_Construct_pres_WFTrm. constructor.
  - cbn. eapply etaExpand_args_Lam_pres_WFTrm. constructor. constructor.
    unfold stableF. intros. constructor. constructor.
    apply (proj1 (proj2 WFTrm_up)). assumption.
  - cbn. eapply etaExpand_args_Construct_pres_WFTrm. assumption.
  - cbn. eapply IHaArgs. inversion_Clear H. assumption.
Qed.
**********************)      

(*** Some basic operations and properties of [Term] ***)

(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable tin: Term.


Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| IProof: forall n t it,
           Instantiate n t it -> Instantiate n (TProof t) (TProof it)
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
| IConstruct: forall n ind m1 args iargs,
                Instantiates n args iargs ->
                Instantiate n (TConstruct ind m1 args)
                            (TConstruct ind m1 iargs)
| ICase: forall n i s ts is its,
           Instantiate n s is -> InstantiateBrs n ts its ->
           Instantiate n (TCase i s ts) (TCase i is its)
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
  forall t, isLambda t -> forall n it, Instantiate n t it -> isLambda it.
Proof.
  intros t ht n it hit. destruct ht as [x0 [x1 jx]]. subst.
  inversion_Clear hit. auto.
Qed.          

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a => TApp (instantiate n t) (instantiate n a)
    | TLambda nm bod => TLambda nm (instantiate (S n) bod)
    | TCase i s ts => TCase i (instantiate n s) (instantiateBrs n ts)
    | TLetIn nm tdef bod =>
      TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TProof t => TProof (instantiate n t)
    | TConstruct i m args => TConstruct i m (instantiates n args)
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
(* Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop *)
(* with instantiates_ind' := Induction for instantiates Sort Prop *)
(* with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop. *)

Lemma instantiates_pres_tlength:
  forall n ds, tlength (instantiates n ds) = tlength ds.
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma instantiateDefs_pres_dlength:
  forall n ds, dlength ds = dlength (instantiateDefs n ds).
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma instantiates_tcons_commute:
  forall n t ts,
         (instantiates n (tcons t ts)) = 
         (tcons (instantiate n t) (instantiates n ts)).
intros n t ts. reflexivity.
Qed.

Lemma instantiates_dcons_commute:
  forall n nm t m ds,
         (instantiateDefs n (dcons nm t m ds)) = 
         (dcons nm (instantiate n t) m (instantiateDefs n ds)).
reflexivity.
Qed.
    
Lemma instantiates_tappend:
  forall ts us n,
    instantiates n (tappend ts us) =
    tappend (instantiates n ts) (instantiates n us).
Proof.
  induction ts; intros.
  - reflexivity.
  - change (tcons (instantiate n t) (instantiates n (tappend ts us)) =
            tcons (instantiate n t) (tappend (instantiates n ts)
                                             (instantiates n us))).
    rewrite IHts. reflexivity.
Qed.

Lemma instantiates_at_last:
  forall ts n t,
    tappend (instantiates n ts) (tunit (instantiate n t)) =
    instantiates n (tappend ts (tunit t)).
Proof.
  intros. rewrite instantiates_tappend. rewrite instantiates_tcons_commute.
  reflexivity.
Qed.
  
(**********
Lemma instantiate_mkApp_commute:
forall n bod arg args,
  instantiate n (mkApp bod (tcons arg args)) =
  mkApp (instantiate n bod) (tcons (instantiate n arg)
                                       (instantiates n args)).
induction bod; simpl; intros; try reflexivity.
- change
    (mkApp (instantiate n bod1) 
           (tcons (instantiate n bod2)
                     (instantiates n (tappend t (tcons arg args)))) =
     mkApp (mkApp (instantiate n bod1)
                  (tcons (instantiate n bod2)
                         (instantiates n t)))
           (tcons (instantiate n arg) (instantiates n args))).
  rewrite mkApp_idempotent. simpl. 
  rewrite instantiates_tappend. rewrite instantiates_tcons_commute.
  reflexivity.
Qed.
 *************)

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

(***
Lemma instantiate_TApp_mkApp:
  forall n fn arg args,
  instantiate n (TApp fn arg args) =
   mkApp (instantiate n fn) (instantiates n (tcons arg args)).
Proof.
  intros. cbn. reflexivity.
Qed.
 **********)

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
  - change (WFapp (TLambda nm (instantiate (S n) bod))).
    constructor.
    + apply H0. assumption.
  - change (WFapp (TLetIn nm (instantiate n dfn) (instantiate (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TApp (instantiate n fn) (instantiate n t))).
    constructor. apply H0; assumption. apply H2. assumption.
  - change (WFapp (TConstruct i m1 (instantiates n args))).
    constructor. intuition.
  - change (WFapp (TCase i (instantiate n mch) (instantiateBrs n brs))).
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
   - change (WFappBs (bcons n (instantiate n0 b)
                            (instantiateBrs n0 bs))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.       
   - change (WFappDs (dcons nm (instantiate n bod) arg
                            (instantiateDefs n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
Qed.

Lemma treverse_instantiates:
  forall n args,
  treverse (instantiates n args) = instantiates n (treverse args).
Proof.
  induction args.
  - reflexivity.
  - change
      (treverse (tcons (instantiate n t) (instantiates n args)) =
       instantiates n (treverse (tcons t args))).
    change
      (tappend (treverse (instantiates n args))
               (tunit (instantiate n t)) =
       instantiates n (tappend (treverse args) (tunit t))).
    rewrite IHargs. rewrite instantiates_tappend. reflexivity.
Qed.
     
(*****************
Lemma instantiate_noLift:
  (forall t p, WFTrm t p ->
               forall m, instantiate m (lift m t) = t) /\
  (forall ts p, WFTrms ts p ->
                forall m, instantiates m (lifts m ts) = ts) /\
  (forall ts p, WFTrmBs ts p ->
                forall m, instantiateBrs m (liftBs m ts) = ts) /\
  (forall ds p, WFTrmDs ds p ->
                forall m, instantiateDefs m (liftDs m ds) = ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try reflexivity.
  - unfold lift. case_eq (m ?= m0); intros j.
    + cbn. Compare_Prop. subst. rewrite (proj2 (Nat.compare_lt_iff _ _)).
      reflexivity. omega.
    + cbn. Compare_Prop. rewrite (proj2 (Nat.compare_gt_iff _ _)).
      reflexivity. omega.
    + cbn. Compare_Prop. erewrite (proj2 (Nat.compare_lt_iff _ _)).
      reflexivity. omega.
  - cbn. apply f_equal. apply H0. 
  - cbn. apply f_equal2. reflexivity. apply H0.
  - cbn. apply f_equal2. apply H0. apply H2.
  - change (mkApp (instantiate m (lift m fn))
                  (tcons (instantiate m (lift m t))
                         (instantiates m (lifts m ts))) =
            TApp fn t ts).
    rewrite H1. rewrite H3. rewrite H5. rewrite mkApp_cons_App.
    reflexivity. assumption.
  - change
      (TConstruct i m (instantiates m0 (lifts m0 args)) =
       TConstruct i m args).
    rewrite H0. reflexivity.
  - change
     (TCase i (instantiate m (lift m mch)) (instantiateBrs m (liftBs m brs)) =
      TCase i mch brs).
    rewrite H0. rewrite H2. reflexivity.
  - change
      (instantiate m0 (TFix (liftDs (m0 + dlength defs) defs) m) =
       TFix defs m).
    change
      (TFix (instantiateDefs (m0 + dlength (liftDs (m0 + dlength defs) defs))
                         (liftDs (m0 + dlength defs) defs)) m =
       TFix defs m).
    rewrite liftDs_pres_dlength. rewrite H0. reflexivity.
  - cbn. apply f_equal2. apply H0. apply H2.
  - cbn. apply f_equal3; try reflexivity. apply H0. apply H2.
  - cbn. apply f_equal3; try reflexivity. apply H0. apply H2.
Qed.

Lemma lift_lift:
  (forall t i k, i < S k ->
                 lift (S k) (lift i t) = lift i (lift k t)) /\
  (forall ts i k, i < S k ->
                  lifts (S k) (lifts i ts) = lifts i (lifts k ts)) /\
  (forall ts i k, i < S k ->
                  liftBs (S k) (liftBs i ts) = liftBs i (liftBs k ts)) /\
  (forall ds i k, i < S k ->
                  liftDs (S k) (liftDs i ds) = liftDs i (liftDs k ds)).
Proof.
  apply TrmTrmsBrsDefs_ind; intros; try reflexivity.
  - unfold lift at 4; unfold lift at 2.
    case_eq (n ?= i); intros; case_eq (n ?= k); intros;
    repeat Compare_Prop; subst; try omega; cbn.
    + subst. rewrite (@match_cn_Eq i); try reflexivity.
      destruct i. reflexivity. rewrite (@match_cn_Gt _ i).
      reflexivity. omega.
    + rewrite (match_cn_Lt j0); try omega.
      rewrite (@match_cn_Eq i); reflexivity.
    + rewrite (match_cn_Lt j0); try omega.
      rewrite (@match_cn_Lt n). reflexivity. omega.
    + rewrite (@match_cn_Eq k); try omega.
      destruct i. reflexivity.
      rewrite (@match_cn_Gt k). reflexivity. omega.
    + rewrite (match_cn_Lt j). rewrite (@match_cn_Gt n). reflexivity. omega.
    + rewrite (@match_cn_Gt n); try omega.
      destruct i. reflexivity.
      case_eq (n ?= i); intros; Compare_Prop; try omega. reflexivity.
  - cbn. apply f_equal. apply H. assumption. 
  - cbn. apply f_equal2. reflexivity. apply H. omega.
  - cbn. apply f_equal2.
    + apply H. assumption.
    + apply H0. omega.
  - cbn. apply f_equal3.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - cbn. apply f_equal2. reflexivity. apply H. assumption.
  - cbn. apply f_equal2.
    + apply H. assumption.
    + apply H0. assumption.
  - change
      (lift (S k) (TFix (liftDs (i + dlength d) d) n) =
       lift i (TFix (liftDs (k + dlength d) d) n)).
    change
      (TFix (liftDs (S (k + dlength (liftDs (i + dlength d) d)))
                    (liftDs (i + dlength d) d))
            n =
       lift i (TFix (liftDs (k + dlength d) d) n)).
    change
      (TFix (liftDs (S (k + dlength (liftDs (i + dlength d) d)))
                    (liftDs (i + dlength d) d))
            n =
       TFix (liftDs (i + dlength (liftDs (k + dlength d) d))
                    (liftDs (k + dlength d) d))
            n).
    apply f_equal2; try reflexivity.
    rewrite liftDs_pres_dlength. rewrite liftDs_pres_dlength. rewrite H.
    reflexivity. omega.
  - cbn. apply f_equal2. rewrite H; try omega. reflexivity.
    rewrite H0. reflexivity. omega.
  - cbn. apply f_equal3; try reflexivity.
    rewrite H; try omega. reflexivity.
    rewrite H0; try omega. reflexivity.
  - cbn. apply f_equal4; try reflexivity.
    rewrite H; try omega. reflexivity.
    rewrite H0; try omega. reflexivity.
Qed.

Lemma lift_instantiate:
  (forall t nin n,
    nin < S n -> WFTrm tin 0 ->
      lift n (instantiate nin t) = instantiate nin (lift (S n) t)) /\
  (forall ts nin n,
    nin < S n -> WFTrm tin 0 ->
    lifts n (instantiates nin ts) =
    instantiates nin (lifts (S n) ts)) /\
  (forall ts nin n,
    nin < S n -> WFTrm tin 0 ->
    liftBs n (instantiateBrs nin ts) =
    instantiateBrs nin (liftBs (S n) ts)) /\
  (forall ds nin n,
    nin < S n -> WFTrm tin 0 ->
    liftDs n (instantiateDefs nin ds) =
    instantiateDefs nin (liftDs (S n) ds)).
Proof.
  apply TrmTrmsBrsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H; try omega; try reflexivity; assumption);
  try (cbn; rewrite H, H0; try omega; try reflexivity; assumption).
  - unfold instantiate at 1. unfold lift at 2.
    case_eq (nin ?= n); intros; case_eq (n ?= S n0); intros;
    repeat Compare_Prop; unfold instantiate; try omega.
    + erewrite (proj1 WF_nolift _ _ H0); try omega.
      rewrite (proj2 (Nat.compare_eq_iff _ _)). reflexivity. assumption.
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      rewrite j. cbn. rewrite (proj2 (Nat.compare_eq_iff _ _)); reflexivity.
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; Compare_Prop; try omega.
      reflexivity.      
    + rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; Compare_Prop; try omega.
      apply f_equal. omega.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega.
      cbn. rewrite (proj2 (Nat.compare_lt_iff _ _)); try omega.
      reflexivity.
  - rewrite instantiate_TApp_mkApp.
    change (lift n (mkApp (instantiate nin t)
                          (instantiates nin (tcons t0 t1))) =
            instantiate nin (TApp (lift (S n) t)
                                  (lift (S n) t0) (lifts (S n) t1))).
    rewrite instantiate_TApp_mkApp.
    change
      (lift n (mkApp (instantiate nin t)
                     (tcons (instantiate nin t0) (instantiates nin t1))) =
       mkApp (instantiate nin (lift (S n) t))
             (instantiates nin (tcons (lift (S n) t0) (lifts (S n) t1)))).
    rewrite lift_mkApp. 
    rewrite H; try assumption. apply f_equal2; try reflexivity.
    change
      (tcons (lift n (instantiate nin t0)) (lifts n (instantiates nin t1)) =
       tcons (instantiate nin (lift (S n) t0))
              (instantiates nin (lifts (S n) t1))).
    rewrite H0; try assumption. rewrite H1; try assumption. reflexivity.
  - change
      (TFix (liftDs (n0 + dlength (instantiateDefs (nin + dlength d) d))
                  (instantiateDefs (nin + dlength d) d)) n =
       TFix (instantiateDefs (nin + dlength (liftDs (S n0 + dlength d) d))
                             (liftDs (S n0 + dlength d) d)) n).
    erewrite <- instantiateDefs_pres_dlength.
    rewrite liftDs_pres_dlength.
    apply f_equal2; try reflexivity.
    erewrite H. reflexivity. omega. eassumption.
Qed.
    
Lemma instantiate_lift:
  (forall t nin n,
    n < S nin -> WFTrm tin 0 ->
      lift n (instantiate nin t) = instantiate (S nin) (lift n t)) /\
  (forall ts nin n,
    n < S nin -> WFTrm tin 0 ->
      lifts n (instantiates nin ts) = instantiates (S nin) (lifts n ts)) /\
  (forall ts nin n,
    n < S nin -> WFTrm tin 0 ->
    liftBs n (instantiateBrs nin ts) =
    instantiateBrs (S nin) (liftBs n ts)) /\
  (forall t nin n,
    n < S nin -> WFTrm tin 0 ->
      liftDs n (instantiateDefs nin t) = instantiateDefs (S nin) (liftDs n t)).
Proof.
  apply TrmTrmsBrsDefs_ind; intros; try reflexivity;
  try (cbn; rewrite H; try omega; try reflexivity; assumption);
  try (cbn; rewrite H, H0; try omega; try reflexivity; assumption).
  - unfold instantiate at 1. unfold lift at 2.
    case_eq (nin ?= n); intros; case_eq (n ?= n0); intros;
    repeat Compare_Prop; unfold instantiate; try omega.
    + subst. rewrite match_cn_Eq; try omega.
      erewrite (proj1 WF_nolift _ _ H0); try omega. reflexivity.
    + subst. rewrite match_cn_Eq; try omega.
      erewrite (proj1 WF_nolift _ _ H0); try omega. reflexivity.
    + rewrite match_cn_Lt; try omega. cbn.
      case_eq (Nat.pred n ?= n0); intros k; repeat Compare_Prop; try omega.
      * assert (k0: S (Init.Nat.pred n) = n). omega.
        rewrite k0. reflexivity.
      * assert (k0: S (Init.Nat.pred n) = n). omega.
        rewrite k0. reflexivity.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega. cbn.
      rewrite match_cn_Eq; try omega. reflexivity.
    + rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega. cbn.
      rewrite match_cn_Lt; try omega. reflexivity.
    + rewrite match_cn_Gt; try omega. cbn. rewrite match_cn_Gt; try omega.
      reflexivity.
  - change
      (lift n (instantiate nin (TApp t t0 t1)) =
       instantiate (S nin) (TApp (lift n t) (lift n t0) (lifts n t1))).
    rewrite instantiate_TApp_mkApp. rewrite instantiate_TApp_mkApp.
    rewrite lift_mkApp. apply f_equal2.
    + apply H; try assumption.
    + change
        (tcons (lift n (instantiate nin t0)) (lifts n (instantiates nin t1)) =
         tcons (instantiate (S nin) (lift n t0))
               (instantiates (S nin) (lifts n t1))).
      rewrite H0; try rewrite H1; try assumption. reflexivity.
  - cbn. apply f_equal2; try reflexivity.
    rewrite H; try assumption.
    + rewrite <- instantiateDefs_pres_dlength. rewrite liftDs_pres_dlength.
      reflexivity.
    + rewrite <- instantiateDefs_pres_dlength. omega.
Qed.
 *****************)

(***********
Lemma instantiate_closed_null:
  (forall t p, WFTrm t p ->
               forall m, m >= p -> instantiate m t = t) /\
  (forall ts p, WFTrms ts p ->
                forall m, m >= p -> instantiates m ts = ts) /\
  (forall ts p, WFTrmBs ts p ->
                forall m, m >= p -> instantiateBrs m ts = ts) /\
  (forall ds p, WFTrmDs ds p ->
                forall m, m >= p -> instantiateDefs m ds = ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try reflexivity.
  - cbn. assert (j: m0 > m). omega.
    rewrite (proj1 (nat_compare_gt m0 m)); trivial.
  - cbn. rewrite H0; trivial.
  - cbn. rewrite H0. trivial. omega.
  - cbn. rewrite H0; try assumption. rewrite H2; try omega. trivial.
  - cbn. rewrite H1; try assumption. rewrite H3; try assumption.
    destruct fn; try reflexivity.
    + inversion H0.
    + inversion H0.
    rewrite H5; try assumption. rewrite mkApp_goodFn; trivial.
  - cbn. rewrite H0; trivial.
  - cbn. rewrite H0; try assumption. rewrite H2; trivial.
  - cbn. rewrite H0; trivial. omega.  
  - cbn. rewrite H0; trivial. rewrite H2; trivial.
  - cbn. rewrite H0; trivial. rewrite H2; trivial.
  - cbn. rewrite H0; trivial. rewrite H2; trivial.
Qed.
******************)
    
(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm: string.

Inductive PoccTrm : Term -> Prop :=
| PoLambdaBod: forall s bod, PoccTrm bod -> PoccTrm (TLambda s bod)
| PoProof: forall t, PoccTrm t -> PoccTrm (TProof t)
| PoLetInDfn: forall s dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn bod)
| PoLetInBod: forall s dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn bod)
| PoAppL: forall fn a, PoccTrm fn -> PoccTrm (TApp fn a)
| PoAppA: forall fn a, PoccTrm a -> PoccTrm (TApp fn a)
| PoConst: PoccTrm (TConst nm)
| PoCaseL: forall i mch brs, PoccTrm mch -> PoccTrm (TCase i mch brs)
| PoCaseR: forall i mch brs, PoccBrs brs -> PoccTrm (TCase i mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstri: forall m1 n args, PoccTrm (TConstruct (mkInd nm m1) n args)
| PoCnstrargs: forall i n args,
                 PoccTrms args -> PoccTrm (TConstruct i n args)
with PoccTrms : Terms -> Prop :=
| PoThd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
| PoTtl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccBrs : Brs -> Prop :=
| PoBhd_bod: forall m b bs, PoccTrm b -> PoccBrs (bcons m b bs)
| PoBtl: forall m b bs, PoccBrs bs -> PoccBrs (bcons m b bs)
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

Lemma Pocc_TCnstr:
  forall s2 m1 m2 args,
    PoccTrm (TConstruct (mkInd s2 m1) m2 args) -> nm = s2 \/ PoccTrms args.
Proof.
  intros s2 m1 m2 args h. inversion h.
  - left. reflexivity.
  - right. inversion h; assumption.
Qed.

Lemma notPocc_TCnstr:
  forall s2 m1 m2 arty,
    ~ PoccTrm (TConstruct (mkInd s2 m1) m2 arty) -> nm <> s2.
intros s2 m1 m2 arty h j. elim h. rewrite <- j. auto. 
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
  forall t arg, ~ PoccTrm (TApp t arg) -> ~ PoccTrm t /\ ~ PoccTrm arg.
intuition.
Qed.

(****************
Lemma notPocc_mkApp:
  forall t args, ~ PoccTrm (mkApp t args) ->
     ~ PoccTrm t /\ ~ PoccTrms args.
Proof.
  induction t; induction args; simpl; intros h; split; intuition;
    try (solve [inversion H]).
  inversion_Clear H. apply h. cbn.
               [apply PoAppA; assumption
                 
  try (solve [inversion_Clear H; apply h;
               [apply PoAppA; assumption |
                apply PoAppR; assumption]]).
  - destruct args.
    + cbn in h. inversion_Clear H.
      * apply h. apply PoAppA. assumption.
      * inversion H1.
    +
    + elim h.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppL. assumption.
    + apply PoAppA. assumption.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoThd. assumption.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoTtl. assumption.
Qed.
 ****************)

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
  forall i mch brs, ~ PoccTrm (TCase i mch brs) ->
                  ~ PoccTrm mch /\ ~ PoccBrs brs.
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
  forall nm bod rarg ds, ~ PoccDefs (dcons nm bod rarg ds) ->
                         ~ PoccTrm bod /\ ~ PoccDefs ds.
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

(***
(** Pocc and mkApp: what a mess! **)
Lemma Pocc_mkApp_inv_lem:
  forall fn args res, MkApp fn args res ->
                  PoccTrm res -> PoccTrm fn \/ PoccTrms args.
Proof.
  induction 1; intros h; intuition.
  - inversion_Clear H1.
    + left. apply PoAppA. assumption.
    + destruct (PoccTrms_append_invrt _ _ H2).
      * left. apply PoAppR. assumption.
      * right. assumption.
  - inversion_clear h. 
    + left. assumption.
    + right. apply PoThd. assumption.
    + right. apply PoTtl. assumption.
Qed.

Lemma eatsArgs_PoccTrm:
  forall fn tc, eatsArgs fn = Some tc -> PoccTrm tc -> PoccTrm fn.
Proof.
  intros fn tc. functional induction (eatsArgs fn); intros.
  - myInjection H. assumption.
  - myInjection H. assumption.
  - constructor. intuition.
  - discriminate.
Qed.
***)

Lemma Pocc_TApp_inv:
  forall fn arg, PoccTrm (TApp fn arg) -> PoccTrm fn \/ PoccTrm arg.
Proof.
  intros fn arg h. inversion_Clear h; intuition.
Qed.

Lemma tIn_Pocc_Poccs:
  forall t ts us, tIn t ts -> PoccTrm t -> PoccTrms (tappend ts us).
induction ts; intros us h1 h2.
- inversion h1.
- inversion h1.
  + subst. simpl. apply PoThd. assumption.
  + simpl.  apply PoTtl. apply IHts; assumption.
Qed.

(************
Lemma Pocc_fn_mkApp_lem:
  forall fn, eatsArgs fn = None ->
             forall args, PoccTrm fn -> PoccTrm (mkApp fn args).
Proof.
  intros fn. functional induction (eatsArgs fn); intros; try discriminate.
  - inversion_Clear H0.
    + specialize (IHo H args H2). pose proof (None_eatsArgs _ arg H).
      destruct args; cbn; rewrite H.
      * constructor. assumption.
      *
      * rewrite <- (mkApp_hd _ H0). rewrite <- (mkApp_hd _ H).
        inversion_Clear IHo.



        change
        (PoccTrm (mkApp (TApp fn arg) args)).
      change
        (PoccTrm
             (match eatsArgs (TApp fn arg) with
              | Some tc => tc
              | None => match args with
                        | tnil => (TApp fn arg)
                        | tcons y ys => mkApp (TApp (TApp fn arg) y) ys
                        end
              end)).





           (mkApp (TApp fn arg) args)).

      destruct args; intros.
  - cbn. destruct fn; assumption.
  - destruct (isApp_dec fn).
    + admit.
    + rewrite mkApp_goodFn.

    
  induction 1.
  - destruct args; simpl.
    + apply PoLambdaBod. assumption.
    + destruct args.
      * cbn. apply PoAppL. apply PoLambdaBod. assumption.
      * cbn. 
  - destruct args; simpl.
    + apply PoProof. assumption.
    + apply PoAppL. apply PoProof. assumption.
 - destruct args; simpl.
    + apply PoLetInDfn. assumption.
    + apply PoAppL. apply PoLetInDfn. assumption.
  - destruct args; simpl.
    + apply PoLetInBod. assumption.
    + apply PoAppL. apply PoLetInBod. assumption.
  - simpl. intros brgs. apply PoAppL. assumption.
  - simpl. intros brgs. apply PoAppA. assumption.
  - simpl. intros brgs. apply PoAppR. apply PoccTrms_tappendl. assumption.
  - destruct args; simpl.
    + apply PoConst.
    + apply PoAppL. apply PoConst.
  - destruct args; simpl.
    + apply PoCaseL. assumption.
    + apply PoAppL. apply PoCaseL. assumption.
  - destruct args; simpl.
    + apply PoCaseR. assumption.
    + apply PoAppL. apply PoCaseR. assumption.
  - destruct args; simpl.
    + apply PoFix. assumption.
    + apply PoAppL. apply PoFix. assumption.
  - intros. destruct args0; cbn. 
    + apply PoCnstri; assumption.
    + apply PoAppL. apply PoCnstri.
  - intros. destruct args0; cbn.
    + apply PoCnstrargs. assumption.
    + apply PoAppL. apply PoCnstrargs. assumption.      
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
***********************)

Lemma Instantiates_no_gen:
  (~ PoccTrm tin) ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, Instantiates n ts ss -> PoccTrms ss -> PoccTrms ts) /\
  (forall n ts ss, InstantiateBrs n ts ss -> PoccBrs ss -> PoccBrs ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstInstsBrsDefs_ind; intros; auto.
  - contradiction.
  - inversion H.
  - inversion_Clear H0.
    + constructor. intuition.
  - inversion_Clear H0.
    + constructor. intuition. 
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoLetInBod. intuition.
  - inversion_Clear H1; intuition.
  - inversion_Clear H0. constructor. apply PoCnstrargs. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoCaseR. intuition.
  - inversion_Clear H0.
    + constructor. apply H. assumption.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoTtl. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoBtl. intuition.
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoDtl. intuition. 
Qed.

Lemma instant_pres_PoccTrm:
  (forall tbod, PoccTrm tbod -> forall n, PoccTrm (instantiate n tbod)) /\
  (forall ts, PoccTrms ts -> forall n, PoccTrms (instantiates n ts)) /\
  (forall bs, PoccBrs bs -> forall n, PoccBrs (instantiateBrs n bs)) /\
  (forall (Ds:Defs), PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsBrsDefs_ind; intros; cbn; try solve [constructor; trivial].
Qed.


End PoccTrm_sec.
End Instantiate_sec.

(** etaExpand cannot be an application **)
Lemma etaExpand_args_Lam_up:
  forall nargs aArgs F cArgs u,
      etaExpand_args_Lam nargs aArgs F (tappend cArgs (tunit u)) =
      etaExpand_args_Lam (S nargs) (tcons u aArgs) F cArgs.
Proof.
  induction nargs; induction aArgs; cbn; intros; try reflexivity.
Qed.

Lemma etaExpand_args_Construct_up:
  forall nargs tlaArgs,
    nargs >= tlaArgs ->
    forall aArgs, tlaArgs = tlength aArgs ->
    forall i m u,
      etaExpand_args_Construct (S nargs) (tcons u aArgs) i m =
      etaExpand_args_Lam nargs aArgs (TConstruct i m) (tunit u).
Proof.
  unfold ge. induction 1; intros.
  - rewrite H. clear. cbn. induction aArgs; cbn; reflexivity.
  - specialize (IHle aArgs H0 i m0). destruct aArgs; cbn; reflexivity.
Qed.

(***********
Lemma isLambda_etaExpand_args_Lam_Lam:
  forall nargs aArgs F cArgs,
    let ea := (etaExpand_args_Lam
                 nargs aArgs (fun b : Terms => TLambda nAnon (F b)) cArgs) in
    isLambda ea \/ isDummy ea.
Proof.
  induction nargs; induction aArgs; cbn; intros; auto.
Qed.

Lemma isLambda_etaExpand_args_Lam_Construct:
  forall nargs aArgs i m cArgs,
    let ea := etaExpand_args_Lam nargs aArgs (TConstruct i m) cArgs in
    isLambda ea \/ isConstruct ea \/ isDummy ea.
Proof.
  induction nargs; induction aArgs; cbn; intros.
  - right. left. auto.
  - right. right. auto.
  - destruct (isLambda_etaExpand_args_Lam_Lam
                nargs tnil (TConstruct i m)
                (tappend (lifts 0 cArgs) (tunit (TRel 0)))) as [h0 | h1];
    intuition.
  - destruct (IHnargs aArgs i m cArgs) as [h0 | [h1 | h2]]; intuition.
Qed.

Lemma isLambda_etaExpand_args_Construct:
  forall nargs aArgs i m,
    let ea := (etaExpand_args_Construct nargs aArgs i m) in
    isLambda ea \/ isConstruct ea  \/ isDummy ea.
Proof.
  destruct nargs, aArgs; cbn; intros; auto.
  - destruct (isLambda_etaExpand_args_Lam_Lam
                nargs tnil (TConstruct i m) (tunit (TRel 0))) as [h | h];
      intuition.
  - destruct (isLambda_etaExpand_args_Lam_Construct
                nargs aArgs i m (tunit t)) as [h | [h|h]]; intuition.
Qed. 

Lemma isLambda_etaExpand:
  forall nargs aArgs i m npars,
    let ea := etaExpand i m aArgs npars nargs in
    isLambda ea \/ isConstruct ea \/ isDummy ea.
Proof.
  intros. unfold ea.
    functional induction (etaExpand i m aArgs npars nargs).
  - intuition.
  - cbn.
    destruct (isLambda_etaExpand_args_Lam_Lam
                nargs tnil (TConstruct i m ) tnil); intuition.
  - destruct (isLambda_etaExpand_args_Construct nargs aa i m)
      as [h0 | [h1 | h2]]; intuition.
Qed.

Lemma notIsApp_etaExpand:
  forall i m aArgs npars nargs,
    ~ isApp (etaExpand i m aArgs npars nargs).
Proof.
  intros. destruct (isLambda_etaExpand nargs aArgs i m npars)
    as [h | [h | h]]; intros j; destruct j as [y0 [y1 jy]].
  - destruct h as [x0 [x1 jx]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 [x1 [x2 jx]]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 jx]. rewrite jx in jy. discriminate.
Qed.

Goal
  forall aArgs np tin n i m na,
    instantiate tin n (etaExpand i m aArgs np na) =
    etaExpand i m (instantiates tin n aArgs) np na.
Proof.
  induction aArgs; induction np; intros.
  - cbn. case_eq na; intros.
    + cbn. reflexivity.
    + cbn.
***************************)


  
(****************************  
Lemma notIsApp_etaExpand_args_Lam:
  forall nargs aArgs F cArgs,
    ~ isApp (etaExpand_args_Lam
               nargs aArgs (fun b : Terms => TLambda nAnon (F b)) cArgs).
Proof.
  intros.
  destruct (isLambda_etaExpand_args_Lam_Lam nargs aArgs F cArgs)
    as [h | h];
    intros j; destruct j as [y0 [y1 jy]].
  - destruct h as [x0 [x1 jx]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 jx]. rewrite jx in jy. discriminate.
Qed.

(**********)
Lemma isLambda_etaExpand_args_Lam:
  forall nargs aArgs bod cArgs,
    let ea := (etaExpand_args_Lam nargs aArgs bod cArgs) in
    isLambda ea \/ isConstruct ea  \/ isWrong ea.
Proof.
  induction nargs; induction aArgs; cbn; intros; auto.


  Lemma isLambda_etaExpand_args_Construct:
  forall nargs aArgs i m cArgs,
    let ea := (etaExpand_args_Construct nargs aArgs i m cArgs) in
    isLambda ea \/ isConstruct ea  \/ isWrong ea.
Proof.
  induction nargs; induction aArgs; cbn; intros; auto.
  - destruct (IHnargs tnil i m cArgs).
    + dstrctn H. unfold etaExpand_args_Construct in j.
      destruct nargs; try discriminate.
      unfold etaExpand_args_Lam in j.
    
  - destruct (isLambda_etaExpand_args_Lam
             nargs tnil i m
             (compile.tappend (lifts 0 cArgs) (tunit (TRel 0)))) as [h0 | h1];
      auto.
  - destruct (isLambda_etaExpand_args_Lam
             nargs aArgs i m (compile.tappend cArgs (tunit t))) as [h0 | h1];
      auto.
Qed.

Lemma notIsApp_etaExpand_args_Construct:
  forall nargs aArgs i m cArgs,
    ~ isApp (etaExpand_args_Construct nargs aArgs i m cArgs).
Proof.
  intros.
  destruct (isLambda_etaExpand_args_Construct nargs aArgs i m cArgs)
    as [h | [h | h]]; intros j; destruct j as [y0 [y1 jy]].
  - destruct h as [x0 [x1 jx]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 [x1 [x2 jx]]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 jx]. rewrite jx in jy. discriminate.
Qed.

 ****************
Lemma isLambda_etaExpand:
  forall nargs aArgs i m npars,
    let ea := etaExpand i m aArgs npars nargs in
    isLambda ea \/ isConstruct ea \/ isWrong ea.
Proof.
  intros. unfold ea.
    functional induction (etaExpand i m aArgs npars nargs).
  - intuition.
  - cbn.
    destruct (pre_isLambda_etaExpand_args_Lam nargs tnil (TConstruct i m) tnil)
             as [h0 | h1]; intuition.
  - destruct (isLambda_etaExpand_args_Construct nargs aa i m tnil)
      as [h0 | [h1 | h2]]; intuition.
Qed.

Lemma notIsApp_etaExpand:
  forall i m aArgs npars nargs,
    ~ isApp (etaExpand i m aArgs npars nargs).
Proof.
  intros. destruct (isLambda_etaExpand nargs aArgs i m npars)
    as [h | [h | h]]; intros j; destruct j as [y0 [y1 jy]].
  - destruct h as [x0 [x1 jx]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 [x1 [x2 jx]]]. rewrite jx in jy. discriminate.
  - destruct h as [x0 jx]. rewrite jx in jy. discriminate.
Qed.
********************)
  
(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) : Term := instantiate arg 0 bod.

Lemma whBetaStep_pres_WFapp:
  forall bod, WFapp bod ->
              forall arg, WFapp arg -> WFapp (whBetaStep bod arg).
Proof.
  intros bod hbod arg harg. unfold whBetaStep.
  apply instantiate_pres_WFapp; assumption.
Qed.

Definition whCaseStep (cstrNbr:nat) (ts:Terms) (brs:Brs): option Term :=
  match bnth cstrNbr brs with
    | Some t => Some (mkApp t ts)
    | None => None
  end.

(****
Definition whCaseStep (cstrNbr:nat) (brs:Brs): option Term :=
  bnth cstrNbr brs.
****)
(***********
Lemma whCaseStep_pres_WFapp:
  forall (brs:Brs), WFappBs brs -> forall ts, WFapps ts -> 
  forall (n:nat) (s:Term), whCaseStep n ts brs = Some s -> WFapp s.
Proof.
  intros brs hbrs ts hts n s h. unfold whCaseStep in h.
  case_eq (bnth n brs); intros; rewrite H in h.
  - destruct p.
    destruct t; try (myInjection h; apply mkApp_pres_WFapp;
                     [assumption | eapply (bnth_pres_WFapp hbrs n); eassumption]).
    myInjection h.
    + assumption.
    + eapply (bnth_pres_WFapp hbrs n). eassumption.
  - discriminate.
Qed.
****************)

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
  intros bod dts arg hbod hdts harg.
  unfold pre_whFixStep. constructor; try assumption.
  apply fold_left_pres_WFapp; try assumption.
  intros. apply instantiate_pres_WFapp.
  assumption. constructor. assumption.
Qed.
  
