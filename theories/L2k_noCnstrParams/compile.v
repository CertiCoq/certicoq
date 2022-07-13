(* This translates λ-box terms to the Ast used by CertiCoq. At this point the two languages are mostly 
  the same except that we map unsupported constructs to [TWrong], translate nested lists into
  specific datatypes and switch back to n-ary application nodes (hence the use of a view here and well-founded
  recursion on the size of terms, see [compile]). *)   

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith. 
Require Import Common.Common.
Require Import Coq.micromega.Lia.

From Equations Require Import Equations.
From MetaCoq.Template Require utils EtaExpand.
Require Import MetaCoq.Template.utils.bytestring.
From MetaCoq.Erasure Require Import EAst ESpineView EGlobalEnv EEtaExpanded EInduction Erasure.

Local Open Scope bs_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


Definition projection := (inductive * nat)%type.
Lemma project_dec: forall (s1 s2:projection), {s1 = s2}+{s1 <> s2}.
Proof.
  intros s1 s2. destruct s1, s2. 
  destruct (inductive_dec i i0), (eq_nat_dec n n0);
    subst; try (solve [left; reflexivity]);
  right; intros h; elim n1; injection h; intuition.
Qed.

Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term -> Term
| TConst     : kername -> Term
(* constructors fully applied: eta expand *)
| TConstruct : inductive -> nat (* cnstr no *) -> Terms (* args *) -> Term
| TCase      : inductive ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : string -> Term
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Brs : Type :=
| bnil : Brs
| bcons : list name -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
#[export] Hint Constructors Term Terms Brs Defs : core.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind
         from Trm_ind', Trms_ind', Brs_ind', Defs_ind'.
Notation tunit t := (tcons t tnil).
Notation dunit nm t m := (dcons nm t m dnil).
Notation bunit t m := (bcons t m bnil).

Fixpoint Terms_list (ts:Terms) : list Term :=
  match ts with
    | tnil => nil
    | tcons u us => cons u (Terms_list us)
  end.

Function tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Function blength (ts:Brs) : nat :=
  match ts with 
    | bnil => 0
    | bcons _ _ ts => S (blength ts)
  end.

Lemma tlength_S:
  forall ts p,
    tlength ts > p ->
    exists u us, ts = tcons u us /\ tlength us >= p.
Proof.
  induction ts; intros.
  - cbn in H. lia.
  - cbn in H. case_eq ts; intros; subst.
    + exists t, tnil. auto. cbn in H. assert (j:p = 0). lia. subst.
      intuition.
    + exists t, (tcons t0 t1). intuition.
Qed.

Function tappend (ts1 ts2:Terms) : Terms :=
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

Lemma tappend_tcons:
  forall ts u us,
    tappend ts (tcons u us) = tappend (tappend ts (tunit u)) us.
Proof.
  intros. rewrite <- tappend_assoc. apply f_equal2; reflexivity.
Qed.

Lemma tappend_mk_canonical:
  forall ts s ss, exists u us, (tappend ts (tcons s ss)) = tcons u us.
Proof.
  destruct ts; intros s ss; simpl.
  - exists s, ss. reflexivity.
  - exists t, (tappend ts (tcons s ss)). reflexivity.
Qed.

Lemma tappend_last:
  forall us u, exists ts t, tcons u us = tappend ts (tunit t).
Proof.
  intros.
  induction us; intros.
  - exists tnil, u. reflexivity.
  - dstrctn IHus. destruct x.
    + cbn in j. myInjection j. exists (tunit y), t. reflexivity.
    + cbn in j. myInjection j. exists (tcons t0 (tcons t x)), y.
      reflexivity.
Qed.

Lemma tappend_pres_tlength:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; intros.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Lemma tappend_tunit_inject:
  forall ts us t u, tappend ts (tunit t) = tappend us (tunit u) ->
                    ts = us /\ t = u.
Proof.
  induction ts; induction us; intros.
  - cbn in H.  myInjection H. intuition.
  - cbn in H. myInjection H. destruct us.
    + cbn in H0. discriminate.
    + cbn in H0. discriminate.
  - cbn in H. myInjection H. destruct ts.
    + cbn in H0. discriminate.
    + cbn in H0. discriminate.
  - cbn in H. myInjection H. specialize (IHts _ _ _ H0).
    destruct IHts. subst. intuition.
Qed.
    
Fixpoint tdrop n ts : Terms :=
  match n, ts with
  | 0, us => us
  | S m, tnil => tnil
  | S m, tcons _ us => tdrop m us
  end.

(** reversing Terms **)
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
  - cbn. rewrite IHts. rewrite tappend_pres_tlength. cbn. lia.
Qed.
  
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ ts => S (dlength ts)
  end.

Definition isApp (t:Term) : Prop :=
  exists fn arg, t = TApp fn arg.
Lemma IsApp: forall fn arg, isApp (TApp fn arg).
  intros. exists fn, arg. reflexivity.
Qed.
Global Hint Resolve IsApp : core.

Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
  destruct t; try (right; not_isApp). left. auto.
Qed.

(** lift a Term over a new binding **)
Function lift (n:nat) (t:Term) : Term :=
  match t with
    | TRel m => TRel (match m ?= n with
                        | Lt => m
                        | _ => S m
                      end)
    | TProof => TProof
    | TLambda nm bod => TLambda nm (lift (S n) bod)
    | TLetIn nm df bod => TLetIn nm (lift n df) (lift (S n) bod)
    | TApp fn arg => TApp (lift n fn) (lift n arg)
    | TConstruct i x args => TConstruct i x (lifts n args)
    | TCase i mch brs => TCase i (lift n mch) (liftBs n brs)
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
         | bcons m b bs => bcons m (lift (List.length m + n) b) (liftBs n bs)
       end
with liftDs n (ds:Defs) : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm u j es => dcons nm (lift n u) j (liftDs n es)
       end.
Functional Scheme lift_ind' := Induction for lift Sort Prop
with lifts_ind' := Induction for lifts Sort Prop
with liftBs_ind' := Induction for liftBs Sort Prop
with liftDs_ind' := Induction for liftDs Sort Prop.
Combined Scheme liftLiftsliftBsLiftDs_ind
         from lift_ind', lifts_ind', liftBs_ind', liftDs_ind'.

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

Section Def.

Import TermSpineView.

Fixpoint TmkApps (u : Term) (v : Terms) :=
  match v with
  | tnil => u
  | tcons t v => TmkApps (TApp u t) v
  end.

Fixpoint list_terms (l : list Term) : Terms :=
   match l with
   | [] => tnil
   | t :: ts => tcons t (list_terms ts)
   end.

Fixpoint list_Brs (l : list _) : Brs :=
  match l with
  | [] => bnil
  | (x,t) :: ts => bcons x t (list_Brs ts)
  end.

Fixpoint list_Defs (l : list (def Term)) : Defs :=
  match l with
  | [] => dnil
  | t :: ts => dcons t.(dname) t.(dbody) t.(rarg) (list_Defs ts) 
  end.
  
Section Compile.
  Import MCList (map_InP, In_size).

  Lemma size_pos x : 0 < size x.
  Proof.
    destruct x; cbn; auto with arith.
  Qed.

  Equations? compile (t: term) : Term 
  by wf t (fun x y : EAst.term => size x < size y) :=
  | e with TermSpineView.view e := {
    | tRel n => TRel n
    | tBox => TProof
    | tLambda nm bod => TLambda nm (compile bod)
    | tLetIn nm dfn bod => TLetIn nm (compile dfn) (compile bod)
    | tApp fn args napp nnil => TmkApps (compile fn) (list_terms (map_InP args (fun x H => compile x)))
    | tConst nm => TConst nm
    | tConstruct i m args => TConstruct i m (list_terms (map_InP args (fun x H => compile x)))
    | tCase i mch brs =>
      let brs' := map_InP brs (fun x H => (List.rev (fst x), compile (snd x))) in
      TCase (fst i) (compile mch) (list_Brs brs')
    | tFix mfix idx => 
      let mfix' := map_InP mfix (fun d H => {| dname := dname d; dbody := compile d.(dbody); rarg := d.(rarg) |}) in
      TFix (list_Defs mfix') idx
    | tProj p bod := TWrong "Proj"; (* Impossible, no projections at this stage *)
    | tCoFix mfix idx => TWrong "TCofix"
    | tVar _ => TWrong "Var"
    | tEvar _ _ => TWrong "Evar" }.
  Proof.
    all: try (cbn; lia).
    - rewrite size_mkApps. cbn. destruct args; try congruence. cbn. lia.
    - rewrite size_mkApps. cbn. destruct args; try congruence. cbn. 
      eapply (In_size id size) in H; unfold id in H; cbn in H. 
      change (fun x => size x) with size in H.
      pose proof (size_pos fn). lia.
    - eapply (In_size id size) in H; unfold id in H; cbn in H.
      now change (fun x => size x) with size in H.
    - cbn. eapply (In_size snd size) in H. cbn in H. lia.
    - eapply (In_size dbody size) in H. cbn in H. lia.
  Qed.

  End Compile.
End Def.

Global Hint Rewrite @MCList.map_InP_spec : compile.

Tactic Notation "simp_compile" "in" hyp(H) := simp compile in H; try rewrite <- !compile_equation_1 in H.
Ltac simp_compile := simp compile; try rewrite <- !compile_equation_1.

Definition compile_global_decl d :=
  match d with
  | InductiveDecl m =>
    let Ibs := ibodies_itypPack m.(ind_bodies) in
    ecTyp Term 0 Ibs
  | ConstantDecl {| cst_body := Some t |} =>
    ecTrm (compile t)
  | ConstantDecl {| cst_body := None |} =>
    ecAx Term
  end.

Fixpoint compile_ctx (t : global_context) :=
  match t with
  | [] => []
  | (n, decl) :: rest => 
    (n, compile_global_decl decl) :: compile_ctx rest
  end.

Definition compile_program (p : Ast.Env.program) : Program Term :=
  let p := run_erase_program p (assume_that_we_only_erase_on_welltyped_programs p) in
  {| main := compile (snd p) ; env := compile_ctx (fst p) |}.

Definition program_Program (p: Ast.Env.program) : Program Term :=
  compile_program p.