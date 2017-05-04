(*** type fields are stripped from term notations ***)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.omega.Omega.
Require Export Common.Common.  (* shared namespace *)
Require Export L2k.compile.

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
Ltac not_isApp := not_is3.
Ltac not_isLambda := not_is2.
Ltac not_isCase := not_is3.
Ltac not_isFix := not_is2.
Ltac not_isCast := not_is1.
            
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


(** Printing terms in exceptions for debugging purposes **)
Definition print_name (nm:name) : string :=
  match nm with
    | nAnon => "_"
    | nNamed s => s
  end.
Definition print_ind (i:inductive) : string :=
  match i with
    | mkInd str n => "[ind " ++ str ++ (nat_to_string n) ++ "]"
  end.
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => "(Rel " ++ (nat_to_string n) ++ ")"
    | TProof t => "(PRF " ++ print_term t ++ ")"
    | TCast t  => "(CAST " ++ print_term t ++ ")"
    | TLambda nm t => "(LAM "++ (print_name nm) ++ " [" ++ print_term t ++ "])"
    | TLetIn nm _ _ => "(LET " ++ (print_name nm) ++ ")"
    | TApp fn arg args =>
      "(" ++ (print_term fn) ++ " @ " ++ (print_term arg) ++ " _ " ++ ")"
    | TConst s => "[" ++ s ++ "]"
    | TAx => " TAx "
    | TConstruct i n _ =>
      "(CSTR " ++ (print_ind i) ++ " " ++ (nat_to_string n) ++ ")"
    | TCase i mch _ =>
      "(CASE " ++ (print_ind i) ++ " " ++ (print_term mch) ++
                 " _ " ++") "
    | TFix _ n => " (FIX " ++ (nat_to_string n) ++ ") "
    | TWrong => "TWrong"
  end.

Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (ss tt:Terms), ss = tt \/ ss <> tt) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsDefs_ind.
  - induction t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - induction t0; cross.
    destruct (H t0); [lft | rght ..].
  - induction t0; cross.
    destruct (H t0); [lft | rght ..].
  - induction t0; cross.
    destruct (name_dec n n0); destruct (H t0); [lft | rght ..]. 
  - induction t1; cross.
    destruct (name_dec n n0); destruct (H t1_1); destruct (H0 t1_2); 
    [lft | rght ..]. 
  - induction t2; cross.
    destruct (H t2_1); destruct (H0 t2_2); destruct (H1 t2); [lft | rght ..].
  - induction t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t; cross. lft.
  - induction t0; cross.
    destruct (inductive_dec i i0), (eq_nat_dec n n0); destruct (H t0);
      [lft | rght .. ].
  - induction t0; cross.
    destruct (inductive_dec i i0), (H t0), (H0 d0);
    [lft | rght .. ].
  - induction t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct t; cross. lft.
  - induction tt; cross. lft.
  - induction tt; cross. destruct (H t1); destruct (H0 tt); [lft | rght .. ].
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
    | TApp fn a args => S (TrmSize fn + TrmSize a + TrmsSize args)
    | TCase _ mch brs => S (TrmSize mch + TrmDsSize brs)
    | TFix ds n => S (TrmDsSize ds)
    | _ => S 0
  end
with TrmsSize (ts:Terms) {struct ts} : nat :=
  match ts with
    | tnil => 1
    | tcons s ss => S (TrmSize s + TrmsSize ss)
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

Definition isConstruct (t:Term) : Prop :=
  exists i n args, t = TConstruct i n args.
Lemma IsConstruct: forall i n args, isConstruct (TConstruct i n args).
intros. exists i, n, args. reflexivity.
Qed.
Hint Resolve IsConstruct.

Lemma isConstruct_dec: forall t, isConstruct t \/ ~ isConstruct t.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x0 [x1 [x2 j]]]; discriminate).
  - left. auto.
Qed.

Lemma mkEtaLams_sanityS:
  forall (xtra:nat) (body:Term), isLambda (mkEtaLams (S xtra) body).
Proof.
  intros. cbn. auto.
Qed.

(***
Lemma mkEtaLams_sanity0:
  forall (body:Term), (mkEtaLams 0 body) = body.
Proof.
  intros. cbn. auto.
Qed.
 ***)

Lemma etaExp_cnstr_sanity:
  forall (i:inductive) (x npars nargs:nat) (args:Terms),
    match (npars + nargs) - (tlength args) with
      | 0 => isConstruct (etaExp_cnstr i x npars nargs args)
      | S _ => isLambda (etaExp_cnstr i x npars nargs args)
    end.
Proof.
  intros. unfold etaExp_cnstr.
  case_eq (npars + nargs - tlength args); intros h; cbn.
  - auto.
  - intros; auto.
Qed.


Definition isCast (t:Term) : Prop := exists tm, t = TCast tm.
Lemma IsCast: forall t, isCast (TCast t).
intros. exists t. reflexivity.
Qed.
Hint Resolve IsCast.

Lemma isCast_dec: forall t, {isCast t}+{~ isCast t}.
induction t;
  try (solve [right; intros h; unfold isCast in h;
              destruct h as [tm j]; discriminate]).
left. auto.
Qed.

Definition isCase (t:Term) : Prop :=
  exists xn mch ds, t = TCase xn mch ds.

Lemma isCase_dec: forall t, {isCase t}+{~ isCase t}.
Proof.
  destruct t; try (solve[right; not_isCase]).
  left. unfold isCase. exists i, t, d. reflexivity.
Qed.
Lemma IsCase: forall xn mch ds, isCase (TCase xn mch ds).
Proof.
  intros. exists xn, mch, ds. reflexivity.
Qed.
  
Definition isApp (t:Term) : Prop :=
  exists fn arg args, t = TApp fn arg args.
Lemma IsApp: forall fn arg args, isApp (TApp fn arg args).
intros. exists fn, arg, args. reflexivity.
Qed.
Hint Resolve IsApp.


Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
destruct t; try (right; not_isApp). 
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


Definition isCanonical (t:Term) : Prop :=
  exists (i:inductive) (n:nat) (args:Terms), t = (TConstruct i n args).

Lemma IsCanonical:
  forall i n ts, isCanonical (TConstruct i n ts).
intros. unfold isCanonical. exists i, n, ts. reflexivity. 
Qed.
Hint Resolve IsCanonical.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
Proof.
  induction t;
  try (solve [right; intros h; destruct h as [x0 [x1 [x2 j]]]; discriminate]).
  - left. auto.
Qed.

(***********
Function canonicalP (t:Term) : option (nat * Terms) :=
  match t with
    | TConstruct _ r args => Some (r, args)
    | x => None
  end.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Some x -> isCanonical t.
Proof.
  induction t; simpl; intros; try discriminate. auto.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x, canonicalP t = Some x.
Proof.
  induction 1; cbn.
  - exists (n, tnil, m). reflexivity.
  - exists (n, tcons arg args, m). reflexivity.
Qed.
***************)

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
Function dnthBody (n:nat) (l:Defs) {struct l} : option (Term * nat) :=
  match l with
    | dnil => None
    | dcons _ x ix t => match n with
                           | 0 => Some (x, ix)
                           | S m => dnthBody m t
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
  destruct t; simpl; try rewrite tappend_tnil; try reflexivity.
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

Lemma mkApp_goodFn:
  forall fn t ts, ~ isApp fn -> mkApp fn (tcons t ts) = TApp fn t ts.
destruct fn; intros; try reflexivity.
- elim H. auto.
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

(*******
Lemma mkApp_character:
  forall fn args, ~ isApp (mkApp fn args) \/
   (exists fn' arg' args', mkApp fn args = TApp fn' arg' args' /\ ~ isApp fn').
Proof.
  intros fn args.
  functional induction (mkApp fn args).
  - destruct IHt.
    + left. assumption.
    + right. assumption.
  - destruct t; try (left; not_isApp). elim y.
  - destruct t. 
    + right. exists (TRel n), c, cs. intuition. isApp_inv H.
    + right. exists (TSort s), c, cs. intuition. isApp_inv H.
    + right. exists (TCast t), c, cs. intuition. isApp_inv H.
    + right. exists (TProd n t), c, cs. intuition. isApp_inv H.
    + right. exists (TLambda n t), c, cs. intuition. isApp_inv H.
    + right. exists (TLetIn n t1 t2), c, cs. intuition. isApp_inv H.
    + left. elim y.
    + right. exists (TConst s), c, cs. intuition. isApp_inv H.
    + right. exists (TInd i), c, cs. intuition. isApp_inv H.
    + right. exists (TConstruct i n n0), c, cs. intuition. isApp_inv H.
    + right. exists (TCase n t t0), c, cs. intuition. isApp_inv H.
    + right. exists (TFix d n), c, cs. intuition. isApp_inv H.
Qed.
***)

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
  - exists (TCast fn), arg, tnil. split. reflexivity.
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
  - exists TAx, arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TConstruct i n t), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase i fn d), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists TWrong, arg, tnil. cbn.  split. reflexivity.
    left. repeat split. not_isApp.
Qed.

(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaCast: forall tm, WFapp tm -> WFapp (TCast tm)
| wfaProof: forall tm, WFapp tm -> WFapp (TProof tm)
| wfaLambda: forall nm bod, WFapp bod -> WFapp (TLambda nm bod)
| wfaLetIn: forall nm dfn bod,
             WFapp dfn -> WFapp bod -> WFapp (TLetIn nm dfn bod)
| wfaApp: forall fn t ts,
           ~ (isApp fn) -> WFapp fn -> WFapp t -> WFapps ts ->
           WFapp (TApp fn t ts)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaAx: WFapp TAx
| wfaConstruct: forall i m1 args, WFapps args -> WFapp (TConstruct i m1 args)
| wfaCase: forall m mch brs,
            WFapp mch -> WFappDs brs -> WFapp (TCase m mch brs)
| wfaFix: forall defs m, WFappDs defs -> WFapp (TFix defs m)
with WFapps: Terms -> Prop :=
| wfanil: WFapps tnil
| wfacons: forall t ts, WFapp t -> WFapps ts -> WFapps (tcons t ts)
with WFappDs: Defs -> Prop :=
| wfadnil: WFappDs dnil
| wfadcons: forall nm bod arg ds,
             WFapp bod -> WFappDs ds ->
             WFappDs (dcons nm bod arg ds).
Hint Constructors WFapp WFapps WFappDs.
Scheme WFapp_ind' := Minimality for WFapp Sort Prop
  with WFapps_ind' := Minimality for WFapps Sort Prop
  with WFappDs_ind' := Minimality for WFappDs Sort Prop.
Combined Scheme WFappTrmsDefs_ind from WFapp_ind', WFapps_ind', WFappDs_ind'.

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

Lemma WFapp_mkApp_TApp:
  forall u, WFapp u -> forall t a1 args, u = (TApp t a1 args) ->
    mkApp t (tcons a1 args) = TApp t a1 args.
Proof.
  induction 1; intros; try discriminate.
  - injection H3. intros. subst. rewrite (mkApp_cons_App H). reflexivity.
Qed.

Lemma WFapp_mkApp_WFapp:
  forall u, WFapp u -> forall t args, u = mkApp t args ->
       WFapp t /\ WFapps args .
Proof.
  induction 1; intros tx argsx h;
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

Lemma lift_pres_isApp:
  forall t n, isApp (lift n t) -> isApp t.
Proof.
  induction t; cbn; intros;
  destruct H as [x0 [x1 [x2 jx]]]; try discriminate.
  - myInjection jx. auto.
Qed.

Lemma lifts_pres_WFapps:
  (forall t, WFapp t -> forall n, WFapp (lift n t)) /\
  (forall ts, WFapps ts -> forall n, WFapps (lifts n ts)) /\
  (forall ds, WFappDs ds -> forall n, WFappDs (liftDs n ds)).
Proof.
  apply WFappTrmsDefs_ind; cbn; intros; try (constructor; intuition).
  - apply H. eapply (lift_pres_isApp). eassumption.
Qed.                             

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

Lemma etaExp_cnstr_pres_WFapp:
  forall i x np na args, WFapps args -> WFapp (etaExp_cnstr i x np na args).
Proof.
  intros. unfold etaExp_cnstr. apply mkEtaLams_pres_WFapp.
  constructor. apply mkEtaArgs_pres_WFapps. assumption.   
Qed.

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
    isConstruct (etaExp_cnstr i x npars nargs args) \/
    isLambda (etaExp_cnstr i x npars nargs args).
Proof.
  intros. assert (j:= etaExp_cnstr_Sanity i x npars nargs args).
  cbn in j. destruct j as [h | h]; destruct h; intuition.
Qed.

(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfCast: forall n t, WFTrm t n -> WFTrm (TCast t) n
| wfProof: forall n t, WFTrm t n -> WFTrm (TProof t) n
| wfLambda: forall n nm bod,
            WFTrm bod (S n) -> WFTrm (TLambda nm bod) n
| wfLetIn: forall n nm dfn bod,
             WFTrm dfn n -> WFTrm bod (S n) ->
             WFTrm (TLetIn nm dfn bod) n
| wfApp: forall n fn t ts,
           ~ (isApp fn) -> WFTrm fn n -> WFTrm t n -> WFTrms ts n ->
           WFTrm (TApp fn t ts) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfAx: forall n, WFTrm TAx n
| wfConstruct: forall n i m args,
                 WFTrms args n -> WFTrm (TConstruct i m args) n
| wfCase: forall n m mch brs,
            WFTrm mch n -> WFTrmDs brs n ->
            WFTrm (TCase m mch brs) n
| wfFix: forall n defs m,
           WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
with WFTrms: Terms -> nat -> Prop :=
| wfnil: forall n, WFTrms tnil n
| wfcons: forall n t ts, WFTrm t n -> WFTrms ts n -> WFTrms (tcons t ts) n
with WFTrmDs: Defs -> nat -> Prop :=
| wfdnil: forall n, WFTrmDs dnil n
| wfdcons: forall n nm bod arg ds,
             WFTrm bod n -> WFTrmDs ds n ->
             WFTrmDs (dcons nm bod arg ds) n.
Hint Constructors WFTrm WFTrms WFTrmDs.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrms_ind' := Minimality for WFTrms Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsDefs_ind from WFTrm_ind', WFTrms_ind', WFTrmDs_ind'.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall ts n, WFTrms ts n -> WFapps ts) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsDefs_ind; intros; try (constructor; try assumption).
Qed.


(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:string.

Inductive PoccTrm : Term -> Prop :=
| PoLambdaBod: forall s bod, PoccTrm bod -> PoccTrm (TLambda s bod)
| PoCast: forall t, PoccTrm t -> PoccTrm (TCast t)
| PoProof: forall t, PoccTrm t -> PoccTrm (TProof t)
| PoLetInDfn: forall s dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn bod)
| PoLetInBod: forall s dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn bod)
| PoAppL: forall fn a args, PoccTrm fn -> PoccTrm (TApp fn a args)
| PoAppA: forall fn a args, PoccTrm a -> PoccTrm (TApp fn a args)
| PoAppR: forall fn a args, PoccTrms args -> PoccTrm (TApp fn a args)
| PoConst: PoccTrm (TConst nm)
| PoCaseL: forall n mch brs, PoccTrm mch -> PoccTrm (TCase n mch brs)
| PoCaseR: forall n mch brs, PoccDefs brs -> PoccTrm (TCase n mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstri: forall m1 n args, PoccTrm (TConstruct (mkInd nm m1) n args)
| PoCnstrargs: forall i n args,
                 PoccTrms args -> PoccTrm (TConstruct i n args)
with PoccTrms : Terms -> Prop :=
| PoThd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
| PoTtl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccDefs : Defs -> Prop :=
| PoDhd_bod: forall dn db dra ds,
           PoccTrm db -> PoccDefs (dcons dn db dra ds)
| PoDtl: forall dn db dra ds,
           PoccDefs ds -> PoccDefs (dcons dn db dra ds).
Hint Constructors PoccTrm PoccTrms PoccDefs.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poTrms_ind' := Minimality for PoccTrms Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsDefs_ind from poTrm_ind', poTrms_ind', poDefs_ind'.

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
                    ~ PoccTrm mch /\ ~ PoccDefs brs.
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
***)

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
  induction 1.
  - destruct args; simpl.
    + apply PoLambdaBod. assumption.
    + apply PoAppL. apply PoLambdaBod. assumption.
  - destruct args; simpl.
    + apply PoCast. assumption.
    + apply PoAppL. apply PoCast. assumption.
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


(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable (tin:Term).

Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| ICast: forall n t it,
           Instantiate n t it -> Instantiate n (TCast t) (TCast it)
| IProof: forall n t it,
           Instantiate n t it -> Instantiate n (TProof t) (TProof it)
| ILambda: forall n nm bod ibod,
             Instantiate (S n) bod ibod -> 
             Instantiate n (TLambda nm bod) (TLambda nm ibod)
| ILetIn: forall n nm dfn bod idfn ibod,
            Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
            Instantiate n (TLetIn nm dfn bod) (TLetIn nm idfn ibod)
| IApp: forall n t a ts it ia its,
       Instantiate n t it -> Instantiate n a ia -> Instantiates n ts its ->
       Instantiate n (TApp t a ts) (mkApp it (tcons ia its))
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IAx: forall n, Instantiate n TAx TAx
| IConstruct: forall n ind m1 args iargs,
                Instantiates n args iargs ->
                Instantiate n (TConstruct ind m1 args)
                            (TConstruct ind m1 iargs)
| ICase: forall n np s ts is its,
           Instantiate n s is -> InstantiateDefs n ts its ->
           Instantiate n (TCase np s ts) (TCase np is its)
| IFix: forall n d m id, 
          InstantiateDefs (n + dlength d) d id ->
          Instantiate n (TFix d m) (TFix id m)
| IWrong: forall n, Instantiate n TWrong TWrong
with Instantiates: nat -> Terms -> Terms -> Prop :=
| Inil: forall n, Instantiates n tnil tnil
| Icons: forall n t ts it its,
           Instantiate n t it -> Instantiates n ts its ->
           Instantiates n (tcons t ts) (tcons it its)
with InstantiateDefs: nat -> Defs -> Defs -> Prop :=
| Idnil: forall n, InstantiateDefs n dnil dnil
| Idcons: forall n nm bod rarg ds ibod ids,
            Instantiate n bod ibod ->
            InstantiateDefs n ds ids ->
            InstantiateDefs n (dcons nm bod rarg ds)
                            (dcons nm ibod rarg ids).
Hint Constructors Instantiate Instantiates InstantiateDefs.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with Instantiates_ind' := Induction for Instantiates Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstInstsDefs_ind from 
         Instantiate_ind', Instantiates_ind', InstantiateDefs_ind'.

Lemma InstantiateDefs_pres_dlength:
  forall n ds ids, InstantiateDefs n ds ids -> dlength ds = dlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiates_no_gen:
  (~ PoccTrm tin) ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, Instantiates n ts ss -> PoccTrms ss -> PoccTrms ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstInstsDefs_ind; intros; auto.
  - contradiction.
  - inversion H.
  - inversion_Clear H0.
    + constructor. intuition.
  - inversion_Clear H0.
    + constructor. intuition.
  - inversion_Clear H0.
    + constructor. intuition. 
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoLetInBod. intuition.
  - destruct (Pocc_mkApp_inv _ _ H2) as [hit | hiats]; intuition.
    inversion hiats; intuition.
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
    + apply PoDtl. intuition. 
Qed.

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a ts =>
      mkApp (instantiate n t) (tcons (instantiate n a) (instantiates n ts))
    | TLambda nm bod =>
      TLambda nm (instantiate (S n) bod)
    | TCase np s ts =>
      TCase np (instantiate n s) (instantiateDefs n ts)
    | TLetIn nm tdef bod =>
      TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TCast t => TCast (instantiate n t)
    | TProof t => TProof (instantiate n t)
    | TConstruct i m args => TConstruct i m (instantiates n args)
    | x => x
  end
with instantiates (n:nat) (args:Terms) {struct args} : Terms :=
       match args with
         | tnil => tnil
         | tcons t ts => tcons (instantiate n t) (instantiates n ts)
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

(*****
Lemma instantiate_AppConstruct:
   forall nin i n arty arg args,
     instantiate nin (TApp (TConstruct i n arty) arg args) =
     TApp (TConstruct i n arty)
          (instantiate nin arg) (instantiates nin args).
Proof.
  intros.

  reflexivity.
Qed.

Lemma instantiate_mkAppConstruct:
   forall nin i n arty arg args,
     instantiate nin (TApp (TConstruct i n arty) arg args) =
     mkApp (TConstruct i n arty) (instantiates nin (tcons arg args)).
Proof.
   reflexivity.
Qed.
 ****)

Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, Instantiates n ts its -> instantiates n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
Proof.
  apply InstInstsDefs_ind; intros; cbn; intuition; try (subst; reflexivity).
  - rewrite nat_compare_EQ. reflexivity.
  - rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
  - rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall ts n, Instantiates n ts (instantiates n ts)) /\
  (forall (ds:Defs) n, InstantiateDefs n ds (instantiateDefs n ds)).
Proof.
  apply TrmTrmsDefs_ind; intros; simpl; try (solve [constructor]);
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
  (forall (Ds:Defs), PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsDefs_ind; intros; cbn; try solve [constructor; trivial].
  - eapply Pocc_TApp_mkApp. apply PoAppL. auto.
  - eapply Pocc_TApp_mkApp. apply PoAppA. auto.
  - eapply Pocc_TApp_mkApp. apply PoAppR. auto.
Qed.

(****
Lemma instantiate_is_Const:
  forall n tbod,
    instantiate n tbod = TConst nm -> 
    (tbod = TRel n /\ tin = TConst nm) \/ (tbod = TConst nm).
Proof.
  induction tbod; intros h; simpl; intuition; try discriminate.
  - unfold instantiate in h.
    case_eq (nat_compare n n0); intros; rewrite H in h.
    + left. split. rewrite (nat_compare_eq _ _ H). reflexivity.
      * destruct tin; simpl in h; try discriminate. assumption.
    + discriminate.
    + discriminate.
  - subst. cbn in h. rewrite match_cn_Eq in h; try reflexivity.
    rewrite mkApp_tnil_ident in h. subst.
    - simpl in h.
    assert (j:= mkApp_isApp (instantiate n tbod1)
                            (instantiate n tbod2) (instantiates n t)).
    destruct j as [x0 [x1 [x2 k]]]. rewrite k in h. discriminate.
Qed.
 ****)

Lemma instantiate_TApp_mkApp:
  forall n fn arg args,
  instantiate n (TApp fn arg args) =
   mkApp (instantiate n fn) (instantiates n (tcons arg args)).
Proof.
  intros. cbn. reflexivity.
Qed.

End Instantiate_sec.
End PoccTrm_sec.

Lemma instantiate_pres_WFapp:
  (forall bod, WFapp bod ->
              forall t, WFapp t -> forall n, WFapp (instantiate t n bod)) /\
  (forall ts, WFapps ts ->
              forall t, WFapp t -> forall n, WFapps (instantiates t n ts)) /\
  (forall ds, WFappDs ds ->
              forall t, WFapp t -> forall n, WFappDs (instantiateDefs t n ds)).
Proof.
  apply WFappTrmsDefs_ind; intros;
  try (solve [unfold instantiate; constructor]).
  - destruct (lt_eq_lt_dec n m) as [[h|h]|h]; unfold instantiate.
    + rewrite (proj1 (nat_compare_lt _ _) h). constructor.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). assumption.
    + rewrite (proj1 (nat_compare_gt _ _) h). constructor.
  - cbn. constructor. apply H0. assumption.
  - cbn. constructor. apply H0. assumption.
  - change (WFapp (TLambda nm (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
  - change (WFapp (TLetIn nm (instantiate t n dfn) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (mkApp (instantiate t0 n fn) 
                         (tcons (instantiate t0 n t) (instantiates t0 n ts)))).
    apply mkApp_pres_WFapp.
    + constructor. apply H3; assumption. apply H5. assumption.
    + apply H1. assumption.
  - change (WFapp (TConstruct i m1 (instantiates t n args))).
    constructor. intuition.
  - change (WFapp (TCase m (instantiate t n mch) (instantiateDefs t n brs))).
    constructor.
    + apply H0; assumption.
    + apply H2; assumption.
   - change (WFapp (TFix (instantiateDefs t (n + dlength defs) defs) m)).
     constructor.
     + apply H0. assumption.
   - change (WFapps (tcons (instantiate t0 n t) (instantiates t0 n ts))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappDs (dcons nm (instantiate t n bod) arg
                            (instantiateDefs t n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
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
Lemma whBeta_noGen:
  forall nm t bod arg args, 
    PoccTrm nm t -> t = (whBetaStep bod arg args) ->
    PoccTrm nm bod \/ PoccTrm nm arg \/ PoccTrms nm args.
unfold whBetaStep. intros nm t bod arg args.
assert (j:= proj1 (instantiate_Instantiate arg)).

induction t.

unfold whBetaStep; simpl; induction 1; intros.
****)

Definition whCaseStep (cstrNbr:nat) (ts:Terms) (brs:Defs): option Term :=
  match dnthBody cstrNbr brs with
    | Some (t, _) => Some (mkApp t ts)
    | None => None
  end.

Lemma whCaseStep_pres_WFapp:
  forall (brs:Defs), WFappDs brs -> forall ts, WFapps ts -> 
  forall (n:nat) (s:Term), whCaseStep n ts brs = Some s -> WFapp s.
Proof.
  intros brs hbrs ts hts n s h. unfold whCaseStep in h.
  case_eq (dnthBody n brs); intros; rewrite H in h.
  - destruct p. myInjection h. apply mkApp_pres_WFapp.
    + assumption.
    + eapply (dnthBody_pres_WFapp hbrs n). eassumption.
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
  