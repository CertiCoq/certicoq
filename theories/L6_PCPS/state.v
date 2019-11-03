Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.ctx
        L6.List_util L6.functions L6.cps_show.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Strings.String Coq.Strings.Ascii.
Require Import Common.AstCommon.
Require Import ExtLib.Structures.Monads.

Import ListNotations Nnat MonadNotation.

Require Import compcert.lib.Maps.

Open Scope monad_scope.
Open Scope string.

(** *  Unified state for L6 transformations *)
(* Takes care of fresh names for binders, types and constructors, the original name environment,
   and debugging utils *)

Section CompM.
  Context {S : Type}. (* Transformation-specific state *)

  Record comp_data : Type :=  mkCompData { next_var : var;
                                           nect_ctor_tag : ctor_tag;
                                           next_ind_tag : ind_tag;
                                           next_fun_tag : fun_tag;
                                           cenv : ctor_env;
                                           fenv : fun_env; (* Maps fun_tag's to (number of args,  list (arg no)) *)
                                           nenv : name_env;
                                           log : list string;
                                         }.


  (* Copied from Common.exceptionMonad because of notation overlap *)
  Inductive error (A : Type) : Type :=
    Err : string -> error A | Ret : A -> error A.

  (* Copied from L6.hoare because of notation overlap *)
  Fixpoint mapM {M : Type -> Type} {A B : Type} `{Monad M} (f : A -> M B)
          (l : list A)  : M (list B) :=
  match l with
      | [] => ret []
      | x :: xs =>
      let sx' := f x in
      x' <- sx';;
      xs' <- mapM f xs ;;
      ret (x' :: xs')
  end.
  
  Fixpoint sequence {M : Type -> Type} {A : Type} `{Monad M}
          (l : list (M A))  : M (list A) :=
  match l with
      | [] => ret []
      | x :: xs =>
      x' <- x ;;
          xs' <- sequence xs ;;
          ret (x' :: xs')
  end.

  Global Arguments Err {_} _.
  Global Arguments Ret {_} _.

  Global Instance MonadError : Monad error.
  Proof.
    constructor.
    - (* ret *)
      intros T t. exact (Ret t).

    - (* bind *)
      intros T U [s | r] m2.
      exact (Err s).
      exact (m2 r).
  Defined.
  
  Record stateErr S t : Type := mkStateErr { runStateErr : S -> error t * S }.
  
  Global Instance stateErrMonad S : Monad (stateErr S).
  Proof.
    constructor.
    - (* ret *)
      intros T t. constructor. intros s. exact (Ret t, s).
    - (* bind *)
      intros t u [m1] f1. constructor. intros s.
      destruct (m1 s) as [[err|r] s']. 
      exact (Err err, s').
      eapply f1. exact r. exact s'.
  Defined.      

  Definition get {St : Type} : stateErr St St :=
    mkStateErr St St (fun s => (Ret s, s)).

  Definition put {St : Type} (s : St) : stateErr St unit :=
    mkStateErr St unit (fun s' => (Ret tt, s)).

  Definition fail_with {St A : Type} (str : string) : stateErr St A :=
    mkStateErr St A (fun s => (Err str, s)).
  
  Definition compM := stateErr (comp_data * S).
  
  (* Get the environment name *)
  Definition get_name_env (_ : unit) : compM name_env :=
    s <- get ;;
    ret (nenv (fst s)).

  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var *)
  Definition get_name (old_var : var) (suff : string) : compM var :=
    p <- get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := add_entry names n old_var suff in
    put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  Definition get_names_lst (old : list var) (suff : string) : compM (list var) :=
    mapM (fun o => get_name o suff) old.

  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var *)
  Definition get_named (s : name) : compM var :=
    p <- get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := M.set n s names in
    put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  Definition get_named_lst (s : list name) : compM (list var) := mapM get_named s.

  (** Get a fresh name, and create a new pretty name *)
  Definition get_name_no_suff (name : string) : compM var :=
    p <- get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := add_entry_str names n name in
    put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  (* Get the next fresh record tag of a fresh type *)
  Definition make_record_ctor_tag (n : N) : compM ctor_tag :=
    p <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := {| ctor_name := nAnon
                ; ctor_ind_name := nAnon
                ; ctor_ind_tag := i
                ; ctor_arity := n
                ; ctor_ordinal := 0%N
                |} : ctor_ty_info in
    let e' := ((M.set c inf e) : ctor_env) in
    put (mkCompData x (c+1)%positive (i+1)%positive f e' fenv names log, st) ;;
    ret c.

  (* Register a constructor tag of some type i *)
  Definition register_record_ctor_tag (c : ctor_tag) (i : ind_tag) (n : N) : compM unit :=
    p <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := {| ctor_name := nAnon
                ; ctor_ind_name := nAnon
                ; ctor_ind_tag := i
                ; ctor_arity := n
                ; ctor_ordinal := 0%N
                |} : ctor_ty_info in
    let e' := ((M.set c inf e) : ctor_env) in
    put (mkCompData x c i f e' fenv names log, st).

  (* Get the pretty name of a binder *)
  Definition get_pp_name (x : var) : compM string :=
    nenv <- get_name_env tt ;;
    ret (show_tree (show_var nenv x)).

  (* Get the pretty name of a list of binders *)
  Definition get_pp_names_list (xs : list var) : compM (list string) := mapM get_pp_name xs.

  (* Log a new message *)
  Definition log_msg (msg : string) : compM unit :=
    s <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := s in
    put (mkCompData x c i f e fenv names (msg :: log)%string, st).

  Definition chr_newline : ascii := Eval compute in ascii_of_nat 10.
  Definition newline : string := (String chr_newline EmptyString).

  Definition log_to_string (log : list string) : string :=
    (concat newline ("Debug messages" :: (List.rev log)))%string.

  (* Access the transformation specific state *)
  Definition get_state (_ : unit) : compM S :=
    s <- get ;;
    ret (snd s).

  (* Access the transformation specific state *)
  Definition put_state (st : S) : compM unit :=
    s <- get ;;
    put (fst s, st).

  (** Get a fresh function tag and register it in fun_env *)
  Definition get_ftag (arity : N) : compM fun_tag :=
    p <- get ;;
    let '(mkCompData x c i f e fenv names log, st) := p in
    put (mkCompData x c i (f + 1)%positive e (M.set f (arity, (fromN (0%N) (BinNat.N.to_nat arity))) fenv) names log, st) ;;
    ret f.

  Definition run_compM {A} (m: compM A) (st : comp_data) (s : S)
    : error A * (comp_data * S) := runStateErr _ _ m (st, s).

  Definition pack_data := mkCompData.

  (* Returns the name environment and the log *)
  Definition get_result (d : comp_data) : name_env * string := (nenv d, log_to_string (log d)).

  Definition triple {A} (pre : comp_data -> S -> Prop) (m : compM A)
             (post : comp_data -> S -> A -> comp_data -> S -> Prop) : Prop :=
    forall st s, pre st s ->
      let '(x, (st', s')) := run_compM m st s in
      match x with
      | Err _ => True
      | Ret x => post st s x st' s'
      end.
  
  Notation "{{ p }} e {{ q }}" :=
    (triple p e q) (at level 90, e at next level).
  
  (* Extensional equality *) 
  Definition st_eq {A} (m1 m2 : compM A) :=
    forall st s, run_compM m1 st s = run_compM m2 st s.
  
  Instance triple_Proper {A} : Proper (Logic.eq ==> st_eq ==> Logic.eq ==> iff) (@triple A).
  Proof.
    intros P1 P2 Heq1 m1 m2 Hfeq P3 P4 Heq2; subst; split; intros H.
    - intros s HP2. rewrite <- Hfeq. eapply H.
    - intros s HP2. rewrite  Hfeq. eapply H.
  Qed.
  
  Instance bind_Proper_l {A B} : Proper (st_eq ==> Logic.eq ==> st_eq)
                                          (@bind compM (stateErrMonad (comp_data * S)) A B).
  Proof. 
    intros [m1] [m2] Hfeq f1 f2 Heq m; subst.
    unfold run_compM.
    unfold st_eq, run_compM in Hfeq.
    unfold bind, stateErrMonad.
    unfold runStateErr in Hfeq.
    intros s.
    unfold runStateErr.
    specialize Hfeq with (st := m) (s := s).
    rewrite Hfeq.
    reflexivity.
  Qed.
  
  Instance bind_Proper_r {A B} : Proper (Logic.eq ==> (fun f1 f2 => forall x, st_eq (f1 x) (f2 x)) ==> st_eq)
                                          (@bind compM (stateErrMonad (comp_data * S)) A B).
  Proof. 
    intros m1 [fm2] Hfeq f1 f2 Heq m; subst; intros s.
    unfold run_compM.
    unfold bind, stateErrMonad.
    unfold st_eq, run_compM in Heq.
    unfold runStateErr at 1 3.
    destruct (fm2 (m, s)), e, p; auto.
  Qed.
  
  Instance st_eq_Proper_l {A} : Proper (st_eq ==> Logic.eq ==> iff) (@st_eq A).
  Proof. 
    intros m1 m2 Heq1 m3 m4 Heq2; subst.
    split; intros Heq st s. now rewrite <- Heq1, Heq. now rewrite Heq1, Heq. 
  Qed.
  
  Instance st_eq_Proper_r {A} : Proper (Logic.eq ==> st_eq ==> iff) (@st_eq A).
  Proof. 
    intros m1 m2 Heq1 m3 m4 Heq2; subst.
    split; intros Heq st s. now rewrite <- Heq2, Heq. now rewrite Heq2, Heq. 
  Qed.
  
  (** * Monad Laws *)
  
  Lemma left_id {A B} (x : A) (f : A -> compM B) :
    st_eq (bind (ret x) f) (f x).
  Proof.
    intros m1. reflexivity.
  Qed.
  
  Lemma right_id {A} : forall (m : compM A), st_eq (bind m ret) m.
  Proof.
    intros [fm] [fm1] s.
    unfold bind, ret, stateErrMonad.
    unfold run_compM; simpl.
    destruct (fm _), e; reflexivity.
  Qed.
  
  Lemma assoc {A B C} : forall (m : compM A) (f : A -> compM B)  (g : B -> compM C),
    st_eq (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
  Proof.
    intros [fm] f g st s. unfold bind, stateErrMonad, run_compM, runStateErr.
    destruct (fm (st, s)), e; try reflexivity.
    destruct (f a).
    destruct (runStateErr0 p).
    destruct e; try reflexivity.
  Qed.

  (** * Usefull lemmas about triples *)

  Definition Pre := comp_data -> S -> Prop.
  Definition Post A := comp_data -> S -> A -> comp_data -> S ->  Prop.

  Ltac destruct_compM :=
    let e := fresh "e" in
    let p := fresh "p" in
    destruct (run_compM _ _ _) as [e p]; destruct e, p.

  Ltac destruct_compM_eqn eqn :=
    let e := fresh "e" in
    let p := fresh "p" in
    destruct (run_compM _ _ _) as [e p] eqn:eqn; destruct e, p.

  Lemma pre_strenghtening {A} (P P' : Pre) (Q : Post A) e :  
    (forall st s, P' st s -> P st s) ->
    {{ P }} e {{ Q }} ->
    {{ P' }} e {{ Q }}.
  Proof.
    intros H. unfold triple. intros; eauto. eapply H0. eauto.
  Qed.
  
  Lemma post_weakening {A} (P : Pre) (Q Q' : Post A) e :  
    (forall st s x st' s', P st s -> Q st s x st' s' -> Q' st s x st' s') ->
    {{ P }} e {{ Q }} ->
    {{ P }} e {{ Q' }}.
  Proof.
    intros H. unfold triple. intros.
    specialize H0 with (st := st) (s := s).
    destruct_compM; try apply H; auto.
  Qed.

  Lemma triple_consequence : forall {A} (P P' : Pre) (Q Q' : Post A) (e : compM A),
    {{P}} e {{Q}} ->
    (forall st s, P' st s -> P st s) ->
    (forall st s x st' s', P st s -> Q st s x st' s' -> Q' st s x st' s') ->
    {{P'}} e {{Q'}}.
  Proof. intros. eapply pre_strenghtening; [|eapply post_weakening]; eauto. Qed.

  Lemma pre_eq_state_lr : forall {A} (P : Pre) (Q : Post A) (e : compM A),
    (forall st s, P st s ->
             {{fun st' s' => st = st' /\ s = s'}}
               e
             {{fun st' s' a st1 s1 => st = st' /\ s = s' -> Q st' s' a st1 s1}}) ->
    {{P}} e {{Q}}.
  Proof.
    unfold triple; intros.
    specialize H with (st := st) (s := s).
    specialize H with (st0 := st) (s0 := s).
    destruct_compM; auto.
  Qed.

  Lemma pre_post_copy : forall {A} (P : Pre) (Q : Post A) (e : compM A),
    {{P}} e {{fun st s a st1 s1 => P st s /\ Q st s a st1 s1}} <->
    {{P}} e {{Q}}.
  Proof.
    unfold triple; split; intros;
      destruct_compM_eqn Heq; try split; auto;
      specialize H with (st := st) (s := s); rewrite Heq in H; firstorder.
  Qed.
  
  Lemma pre_post_mp_l {A} (P : Pre) (Q : Post A) e :
    {{ fun st s => True }} e {{ fun st s x st' s' => P st s -> Q st s x st' s' }} ->
    {{ fun st s => P st s }} e {{ fun st s x st' s' => Q st s x st' s' }}.
  Proof.
    intros H.
    eapply post_weakening; [| eapply pre_strenghtening; [| eassumption ] ];
    simpl; eauto. 
  Qed.
  
  (* Works if triple is True on failure
  Lemma pre_post_mp_r {A} (P : Pre) (Q : Post A) e :
    {{ fun st s => P st s }} e {{ fun st s x st' s' => Q st s x st' s' }} ->
    {{ fun st s => True }} e {{ fun st s x st' s' => P st s -> Q st s x st' s' }}.
  Proof. 
    unfold triple.
    intros H st s HP'.
    specialize (H st s).
    destruct_compM; auto.
  Abort. *)
  
  Lemma pre_eq_state_l {A} (P : Pre) (Q : Post A) e :
    (forall st s, P st s -> {{ fun st' s' => st = st' /\ s = s' }} e {{ Q }}) ->
    {{ P }} e {{ Q }}.
  Proof.
    intros H st s HP. specialize (H st s HP). 
    unfold triple in H. eapply H. auto. 
  Qed.
  
  Lemma pre_eq_state_r {A} (P : Pre) (Q : Post A) e :
    {{ P }} e {{ Q }} ->
    (forall st s, P st s -> {{ fun st' s' => st = st' /\ s = s' }} e {{ Q }}).
  Proof.
    intros H st s HP.  intros st' s' [Hst Hs]; subst. eapply H; auto.
  Qed.
  
  Lemma post_eq_l {A} (P : Pre) (Q : Post A) e st1 s1 x st2 s2 :
    {{ P }} e {{ fun st1' s1' x' st2' s2' => st1 = st1' /\ s1 = s1' /\ x = x' /\ st2 = st2' /\ s2 = s2'  }} ->
    Q st1 s1 x st2 s2 ->
    {{ P }} e {{ Q }}.
  Proof.
    intros H HQ st s HP. specialize (H st s HP). 
    unfold triple in H. destruct_compM; auto.
    intuition; subst; auto.
  Qed.
  
  (* Works if triple is False on fail
  Lemma post_eq_r {A} (P : Pre) (Q : Post A) e st1 s1 x st2 s2 :
    {{ P }} e {{ Q }} ->
    {{ P }} e {{ fun st1' s1' x' st2' s2' => st1 = st1' /\ s1 = s1' /\ x = x' /\ st2 = st2' /\ s2 = s2' }} ->
    P st1 s1 ->
    Q st1 s1 x st2 s2.
  Proof.
    intros H H' HP. specialize (H st1 s1 HP). specialize (H' st1 s1 HP). 
    destruct_compM; [contradiction|intuition; subst; auto].
  Qed. *)
  
  Lemma post_conj {A} (P : Pre) (Q1 Q2 : Post A) e :
    {{ P }} e {{ Q1 }} ->
    {{ P }} e {{ Q2 }} ->
    {{ P }} e {{ fun st s x st' s' => Q1 st s x st' s' /\ Q2 st s x st' s' }}.
  Proof.
    unfold triple. intros.
    specialize (H st s); specialize (H0 st s).
    destruct_compM; auto.
  Qed.
  
  Lemma post_trivial {A} (P : Pre)  (e : compM A) :
    {{ P }} e {{ fun _ _ _ _ _ => True }}.
  Proof.
    unfold triple. intros; destruct_compM; auto.
  Qed.
  
  Lemma frame_rule {A} (P : Pre) (Post : Post A) (P' : Pre) (e : compM A) :
    {{ P }} e {{ Post }} ->
    {{ fun st s => P' st s /\ P st s }} e {{ fun st s x st' s' => P' st s /\ Post st s x st' s' }}.
  Proof.
    unfold triple. intros.
    specialize (H st s). destruct_compM; [auto|intuition].
  Qed.
  
  Lemma frame_rule_trivial_pre {A} (Q : Post A) (P : Prop) (e : compM A) :
    (P -> {{ fun _ _ => True }} e {{ Q }}) ->
    {{ fun _ _ => P }} e {{ fun st s x st' s' => P /\ Q st s x st' s' }}.
  Proof.
    intros H. unfold triple in *; intros. specialize (H H0 st s).
    destruct_compM; auto.
  Qed.
  
  Lemma frame_rule_trivial {A} (P : Pre) (e : compM A) :
    {{ P }} e {{ fun st s _ _ _ => P st s }}.
  Proof.
    eapply post_weakening; [| eapply pre_strenghtening;
                              [| eapply frame_rule with (P0 := (fun _ _ => True));
                                 eapply post_trivial]]; simpl in *.
    intros. destruct H0; eauto.
    intros; eauto.
  Qed.
  
  Lemma pre_existential {A B} (P : B -> Pre) (Q : Post A) e :
    (forall b, {{ P b }} e {{ Q }}) ->
    ({{ fun st s => exists b, P b st s }} e {{ Q }}).
  Proof.
    intros Hb st s [b' Hre]. eapply Hb. eassumption.
  Qed.    
  
  Lemma pre_curry_r {A} (P : Pre) (Q : Post A) (P' : Prop) e :
    (P' -> {{ P }} e {{ Q }}) ->
    {{ fun st s => P st s /\ P' }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; eauto.
  Qed.
  
  Lemma pre_curry_l {A} (P : Pre) (Q : Post A) (P' : Prop) e :
    (P' -> {{ P }} e {{ Q }}) ->
    {{ fun st s => P' /\ P st s }} e {{ Q }}.
  Proof.
    intros Hyp st s [Hpre HP]. eapply Hyp; eauto.
  Qed.
  
  Lemma post_mp {A} (P : Pre) (Q Q' : Post A) (e : compM A) :
    {{ P }} e {{ Q' }} ->
    {{ P }} e {{ fun st s r st' s' => Q' st s r st' s' -> Q st s r st' s' }} ->
    {{ P }} e {{ Q }}.
  Proof.
    unfold triple. 
    intros Ht1 Ht2 st s HPre. specialize (Ht1 st s HPre); specialize (Ht2 st s HPre).
    destruct_compM; auto.
  Qed.
  
  Lemma pre_transfer_r {A} (P : Pre) (Q : Post A) (e : compM A) :
    {{ P }} e {{ fun st s x st' s' => Q st s x st' s' }} -> 
    {{ P }} e {{ fun st s x st' s' => P st s /\ Q st s x st' s' }}.
  Proof. 
    intros.
    eapply pre_strenghtening with (P0 := fun st s => P st s /\ P st s). 
    now firstorder. eapply frame_rule. eassumption.
  Qed.
  
  Lemma pre_strenghtening_true {A} (P : Pre) (Q : Post A) e :
    {{ fun _ _ => True }} e {{ Q }} -> 
    {{ P }} e {{ Q }}.
  Proof. 
    intros.
    eapply pre_strenghtening; [| eassumption ].
    now firstorder.
  Qed.
  
  
  (** * Lemmas about monadic combinators *)
  
  Lemma return_triple {A} (x : A) (P : Pre) (Q : Post A) :
    (forall st s, P st s -> Q st s x st s) ->
    {{ P }} (ret x) {{ Q }}.
  Proof.
    unfold triple. auto.
  Qed.
  
  Lemma bind_triple {A B} (m : compM A) (f : A -> compM B)
        (P : Pre) (Q : Post B) (Q' : Post A) :
    {{ P }} m {{ Q' }} ->
    (forall (x : A) st s, {{ Q' st s x }} f x {{ fun _ _ x' st' s' => Q st s x' st' s' }}) -> 
    {{ P }} bind m f {{ Q }}.
  Proof.
    simpl. unfold triple; simpl. 
    intros H1 H2 st s HP.
    pose (Hm := H1 st s HP).
    destruct m as [fm].
    unfold run_compM; simpl.
    destruct (fm (st, s)) eqn:Heq_fm, p, e; auto.
    unfold run_compM in Hm; simpl in Hm; rewrite Heq_fm in Hm.
    eapply H2; auto.
  Qed.

  Lemma bind_triple' : forall {A B} (m : compM A) (f : A -> compM B) (P : Pre)
    (Q : Post B) (Q' : Post A),
    {{P}} m {{fun st s x st' s' => P st s /\ Q' st s x st' s'}} ->
    (forall (x : A) st s, {{fun st' s' => P st s /\ Q' st s x st' s'}} f x {{fun _ _ => Q st s}}) ->
    {{P}} bind m f {{Q}}.
  Proof. intros; eapply bind_triple; eauto. Qed.
  
  Lemma get_triple : {{ fun _ _ => True }} get {{ fun st s x st' s' => x = (st, s) /\ st = st' /\ s = s' }}.
  Proof. unfold triple; intros. simpl. eauto. Qed.
  
  Lemma put_triple x : {{ fun _ _ => True }} put x {{ fun _ _ _ st' s' => x = (st', s') }}.
  Proof. unfold triple; intros. simpl. destruct x. eauto. Qed.
  
  Lemma sequence_triple {A} (P : Pre) (P' : A -> Prop) (l : list (compM A)) :
    Forall (fun e => {{ P }} e {{ fun  _ _ e' st' s' => P' e' /\ P st' s' }}) l -> 
    {{ P }} sequence l {{fun _ _ l' st' s' => Forall P' l' /\ P st' s' }}.
  Proof.     
    induction l; intros Hall.
    - inv Hall. apply return_triple.     
      intros i Hp. split; eauto.
    - inv Hall. eapply bind_triple.
      eassumption. 
      intros x st s. eapply bind_triple.
      eapply frame_rule. eapply IHl; eassumption.
      intros x' st' s'. eapply return_triple.
      intros st'' s'' [HP [Hall Hpre]]. split; eauto.
  Qed.
  
  Lemma map_sequence_triple {A} (P : Pre) (P' : A -> A -> Prop) (f : A -> compM A) (l : list A) :
    Forall (fun e => {{ P }} f e {{ fun _ _ e' st' s' => P' e e' /\ P st' s' }}) l ->  
    {{ P }} sequence (map f l) {{fun _ _ l' st' s' => Forall2 P' l l' /\ P st' s' }}.
  Proof.     
    induction l; intros Hall.
    - inv Hall. apply return_triple.     
      intros i Hp. split; eauto.
    - inv Hall. eapply bind_triple.
      eassumption. 
      intros x st s. eapply bind_triple.
      eapply frame_rule. eapply IHl; eassumption.
      intros x' st' s'. eapply return_triple.
      intros st'' s'' [HP [Hall Hpre]]. split; eauto.
  Qed.
  
  Opaque triple bind ret.

End CompM.
