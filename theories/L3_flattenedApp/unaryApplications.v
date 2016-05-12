(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStrippedL1" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
(******)

Require L2.L2.
Require L1.L1.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Logic.JMeq.
Require Import L3.term.
Require Import L3.program.
Require Import L3.wndEval.
Require Import L3.wcbvEval.
Require Import L3.wNorm.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.term.Term.
Definition L2Terms := L2.term.Terms.
Definition L2Defs := L2.term.Defs.

(** turn (App fn [x1;...;xn]) into (App (... (App fn x1) x2 ...) xn) **)
Function mkApp (fn:Term) (xs:Terms) : Term :=
    match xs with
      | tnil => fn
      | tcons b ys => mkApp (TApp fn b) ys
    end.

(** turn (Constructor [x1;...;xn; 0;...k]])  with arity n+k into
*** (Lam ... (Lam (Const [x1;...;xn; 0;...k])...))
**)
Function mkEta (cstr:Term) (xtraArity:nat) : Term :=
    match xtraArity with
      | 0 => cstr
      | S n => mkEta (TLambda nAnon cstr) n
    end.

Lemma mkEta_under_Lambda:
  forall n t, mkEta (TLambda nAnon t) n = TLambda nAnon (mkEta t n).
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(** Lookup constructor arity in L2 environ (to avoid mutual dependency
*** between converting L2 terms to L3 and L2 environs to L3)
**)
Section EtaExpand.
Variable p:L2.program.environ.

(** temp: here we assume the type of constructors is evaluated **)
(** when removing this; also remove L2.program.arity_from_dtyp **)
Function cnstrArity (i:inductive) (n:nat) : exception nat :=
  match i with
    | mkInd str m => L2.program.cnstrArity str m n p
  end.

(** compute list of variables for eta expanding a constructor
*** (which may already be partially applied)
**)
Function etaArgs (n:nat) : Terms :=
  match n with
    | 0 => tnil
    | S m => tcons (TRel m) (etaArgs m)
  end.

Function etaExp_cnstr (i:inductive) (n:nat) (args:Terms) : exception Term :=
  match cnstrArity i n with
    | Ret arity =>
      match nat_compare (tlength args) arity with
        | Eq => Ret (TConstruct i n args)
        | Lt => let k := arity - (tlength args)
                in Ret (mkEta (TConstruct i n (tappend args (etaArgs k))) k)
        | Gt => Exc ("more arguments than constructor arity: "
                       ++ (nat_to_string (tlength args)) ++ (" ")
                       ++ (nat_to_string arity))
      end
    | Exc x => Exc x
  end.

Function strip (t:L2Term) : exception Term :=
  match t with
    | L2.term.TProof => Ret TProof
    | L2.term.TRel n => Ret (TRel n)
    | L2.term.TSort s => Ret (TSort s)
    | L2.term.TCast s => strip s
    | L2.term.TProd nm bod => 
      match strip bod with
        | Ret sbod => Ret (TProd nm sbod)
        | x => x
      end
    | L2.term.TLambda nm bod =>
      match strip bod with
        | Ret sbod => Ret (TLambda nm sbod)
        | x => x
      end
    | L2.term.TLetIn nm dfn bod => 
      match strip dfn, strip bod with
        | Ret sdfn, Ret sbod => Ret (TLetIn nm sdfn sbod)
        | Exc s, Ret _ => Exc ("strip dfn fails:" ++ s)
        | Ret _, Exc s => Exc ("strip bod fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip dfn and strip bod fail"
      end
    | L2.term.TApp fn arg args =>
      match strip arg, strips args with
        | Ret sarg, Ret sargs =>
          match fn with 
            | L2.term.TConstruct i n => etaExp_cnstr i n (tcons sarg sargs)
            | x => match strip x with
                     | Ret sx => Ret (mkApp sx (tcons sarg sargs))
                     | x => x
                   end
          end
        | Exc s, Ret _ => Exc ("strip arg fails:" ++ s)
        | Ret _, Exc s => Exc ("strips args fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip arg and strips args fail"
      end
    | L2.term.TConst nm =>
      match L2.program.lookup nm p with
        | Some (L2.program.ecTrm _) => Ret (TConst nm)
        | Some L2.program.ecAx => Ret (TAx nm)
        | Some (L2.program.ecTyp _ _) =>
          Exc "L2.program.lookup nm p returns a type"
        | None => Exc "L2.program.lookup nm p misses"
      end
    | L2.term.TInd i => Ret (TInd i)
    | L2.term.TConstruct i n => etaExp_cnstr i n tnil
    | L2.term.TCase n mch brs =>
      match strip mch, strips brs with
        | Ret smch, Ret sbrs => Ret (TCase n smch sbrs)
        | Exc s, Ret _ => Exc ("strip mch fails:" ++ s)
        | Ret _, Exc s => Exc ("strips brs fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip mch and strips brs fail"
      end
    | L2.term.TFix ds n =>
      match stripDs ds with
        | Ret sds => Ret (TFix sds n)
        | Exc s => Exc "stripDs ds fails"
      end
   end
with strips (ts:L2Terms) : exception Terms := 
  match ts with
    | L2.term.tnil => Ret tnil
    | L2.term.tcons t ts =>
      match strip t, strips ts with
        | Ret st, Ret sts => Ret (tcons st sts)
        | Exc s, Ret _ => Exc ("strip t fails:" ++ s)
        | Ret _, Exc s => Exc ("strips ts fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip t and strips ts fail"
      end
  end
with stripDs (ts:L2Defs) : exception Defs := 
  match ts with
    | L2.term.dnil => Ret dnil
    | L2.term.dcons nm t m ds =>
      match strip t, stripDs ds with
        | Ret st, Ret sds => Ret (dcons nm st m sds)
        | Exc s, Ret _ => Exc ("strip t fails:" ++ s)
        | Ret _, Exc s => Exc ("stripDs ds fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip t and stripDs ds fail"
      end
  end.
(**
Functional Scheme strip_ind' := Induction for strip Sort Prop
with strips_ind' := Induction for strips Sort Prop
with stripDs_ind' := Induction for stripDs Sort Prop.
Combined Scheme stripStripsStripDs_ind
         from strip_ind', strips_ind', stripDs_ind'.
***)
End EtaExpand.



Function stripCnstrs (cs:list L2.program.Cnstr) : list Cnstr :=
  match cs with
    | nil => nil
    | cons (L2.program.mkCnstr str arity) cs =>
        cons (mkCnstr str arity) (stripCnstrs cs)
  end.
Function stripItyPack (its:L2.program.itypPack) : itypPack :=
  match its with
    | nil => nil
    | (L2.program.mkItyp str itps) :: itpacks =>
                  (mkItyp str (stripCnstrs itps)) :: stripItyPack itpacks
  end.
Function stripEnv (p:L2.program.environ) : exception environ :=
  match p with
    | nil => Ret nil
    | cons (nm, L2.program.ecTrm t) q =>
      match strip q t, stripEnv q with
        | Ret ts, Ret qs => Ret (cons (nm, ecTrm ts) qs)
        | Exc s, Ret _ => Exc ("strip q t fails:" ++ s)
        | Ret _, Exc s => Exc ("stripEnv q fails:" ++ s)
        | Exc s1, Exc s2 => Exc "both strip q t and stripEnv q fail"
      end
    | cons (nm, L2.program.ecTyp m ityps) q =>
      match stripEnv q with
        | Ret qs => Ret (cons (nm, ecTyp m (stripItyPack ityps)) qs)
        | x => x
      end
    | cons (nm, L2.program.ecAx) q => stripEnv q
  end.


(** start-to-L3 translations **)
Definition program_Program 
           (e:L2.program.environ) (pgm:program) : exception Program :=
  match L1.malecha_L1.program_Program pgm (Ret nil) with
    | Ret pgm => 
      match stripEnv (L2.stripEvalCommute.stripEnv (L1.program.env pgm)),
            strip e (L2.stripEvalCommute.strip (L1.program.main pgm)) with
        | Ret senv, Ret smain => Ret {| env:= senv; main:= smain |}
        | Exc s, Ret _ => Exc ("program_Program: stripEnv fails:" ++ s)
        | Ret _, Exc s => Exc ("program_Program: strip fails:" ++ s)
        | Exc s1, Exc s2 =>
          Exc "program_Program: both stripEnv and strip fail"
      end
    | Exc s => Exc s
  end.
Definition term_Term (e:L2.program.environ) (t:term) : exception Term :=
  match L1.malecha_L1.term_Term t with
    | Exc str => Exc str
    | Ret trm => strip e (L2.stripEvalCommute.strip trm)
  end.


Lemma strip_Lam_invrt:
  forall p nm bod tt,
        strip p (L2.term.TLambda nm bod) = Ret tt ->
        exists sbod, strip p bod = Ret sbod /\ tt = TLambda nm sbod.
Proof.
  induction tt; simpl; intros. 
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TRel n)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TSort s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret TProof) in H.
     destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TProd n tt)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TLambda n tt)) in H.
    destruct (strip p bod).
    + discriminate. 
    + myInjection H. exists tt. intuition.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TLetIn n tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TApp tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TConst s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TAx s)) in H.
    destruct (strip p bod); discriminate.    
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TInd i)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TConstruct i n t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TCase p0 tt t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TLambda nm sbod)
              | Exc s => Exc s end) = Ret (TFix d n)) in H.
    destruct (strip p bod); discriminate.
Qed.

Lemma strip_Prod_invrt:
  forall p nm bod tt,
        strip p (L2.term.TProd nm bod) = Ret tt ->
        exists sbod, strip p bod = Ret sbod /\ tt = TProd nm sbod.
Proof.
  induction tt; simpl; intros. 
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TRel n)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TSort s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret TProof) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TProd n tt)) in H.
    destruct (strip p bod). 
    + discriminate.
    + myInjection H. exists tt. intuition.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TLambda n tt)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TLetIn n tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TApp tt1 tt2)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TConst s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TAx s)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TInd i)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TConstruct i n t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TCase p0 tt t)) in H.
    destruct (strip p bod); discriminate.
  - change ((match strip p bod with
              | Ret sbod => Ret (TProd nm sbod)
              | Exc s => Exc s end) = Ret (TFix d n)) in H.
    destruct (strip p bod); discriminate.
Qed.

Lemma strip_Construct_invrt:
  forall p i r tt,
        strip p (L2.term.TConstruct i r) = Ret tt ->
        etaExp_cnstr p i r tnil = Ret tt.
Proof.
  induction tt; unfold strip; simpl; intros; try assumption.
Qed.
 
Lemma strip_Ind_invrt:
  forall p i tt,
        strip p (L2.term.TInd i) = Ret tt -> tt = (TInd i).
Proof.
  induction tt;  simpl; intros; try discriminate.
  myInjection H. reflexivity.
Qed.


(**** L2 and L3 agree on cbv evaluation  ****
Lemma wndEval_types_irrelevant:
  forall p pp, stripEnv p = Some pp -> 
    (forall t s, L2.wcbvEval.WcbvEval p t s ->
     forall tt, strip p t = Some tt -> 
     forall ss, strip p s = Some ss ->
          WcbvEval pp tt ss) /\
    (forall ts ss, L2.wcbvEval.WcbvEvals p ts ss ->
     forall tss, strips p ts = Some tss -> 
     forall sss, strips p ss = Some sss ->
          WcbvEvals pp tss sss).
Proof.
  intros p pp h. apply L2.wcbvEval.WcbvEvalEvals_ind; simpl; intros.
  - destruct (strip_Lam_invrt _ _ _ H) as [x [j1x j2x]].
    destruct (strip_Lam_invrt _ _ _ H0) as [y [j1y j2y]].
    subst. rewrite j1x in j1y. myInjection j1y. constructor.
  - destruct (strip_Prod_invrt _ _ _ H) as [x [j1x j2x]].
    destruct (strip_Prod_invrt _ _ _ H0) as [y [j1y j2y]].
    subst. rewrite j1x in j1y. myInjection j1y. constructor.
  - change (strip p t = Some tt) in H0. eapply H; assumption.
  - unfold strip in H. unfold strip in H0. rewrite H in H0.
    myInjection H0. clear H0. unfold etaExp_cnstr in H.
    destruct (cnstrArity p i r).
    + destruct (PeanoNat.Nat.compare (tlength tnil) n).
      * myInjection H. constructor. constructor.
      * myInjection H. clear H. rewrite <- minus_n_O.
        { induction n.
          - simpl. constructor. constructor.
          - change 
              (WcbvEval pp
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)).
            simpl. rewrite mkEta_under_Lambda. constructor. }
      * discriminate.
    + discriminate.
  - rewrite (strip_Ind_invrt H). rewrite (strip_Ind_invrt H0). constructor.
  - unfold strip in H. unfold strip in H0. myInjection H. myInjection H0.
    constructor.
  -





Qed.

***)


(***  scratch below  *****
Section FlatApp.
Variable flatApp: L2Term -> Term.
Fixpoint flatApps (ts:L2Terms) : Terms :=
  match ts with
    | L2.term.tnil => tnil
    | L2.term.tcons s ss => tcons (flatApp s) (flatApps ss)
  end.
Fixpoint flatAppDs (ts:L2Defs) : Defs :=
  match ts with
    | L2.term.dnil => dnil
    | L2.term.dcons nm bod n ds => dcons nm (flatApp bod) n (flatAppDs ds)
  end.
Fixpoint mkApp (fn:Term) (l:L2Terms) : Term :=
    match l with
      | L2.term.tnil => fn
      | L2.term.tcons b t => mkApp (TApp fn (flatApp b)) t
    end.
End FlatApp.

Function flatApp (t:L2Term) : Term :=
  match t with
    | L2.term.TRel n => TRel n
    | L2.term.TSort s => TSort s
    | L2.term.TProd nm bod => TProd nm (flatApp bod)
    | L2.term.TLambda nm bod => TLambda nm (flatApp bod)
    | L2.term.TLetIn nm dfn bod => TLetIn nm (flatApp dfn) (flatApp bod)
    | L2.term.TApp fn arg args =>
      match fn with 
        | L2.term.TConstruct i n =>
             TConstruct i n (tcons (flatApp arg) (flatApps args))
        | x => mkApp flatApp (flatApp x)
                     (tcons (flatApp arg) (flatApps flatApp args))
      end
    | L2.term.TConst nm => TConst nm
    | L2.term.TInd i => TInd i
    | L2.term.TConstruct i n => TConstruct i n tnil
    | L2.term.TCase n mch brs => TCase n (flatApp mch) (flatApps brs)
    | L2.term.TFix ds n => TFix (flatAppDs ds) n
  end.
***)
