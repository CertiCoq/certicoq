Require Import Common.compM Common.Pipeline_utils.
Require Import L6.cps L6.cps_util L6.set_util L6.identifiers L6.ctx
        L6.List_util L6.functions L6.cps_show L6.Ensembles_util L6.tactics.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Strings.String Coq.Strings.Ascii
        Coq.Sets.Ensembles.
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

  Record comp_data : Set  :=  mkCompData { next_var : var;
                                           nect_ctor_tag : ctor_tag;
                                           next_ind_tag : ind_tag;
                                           next_fun_tag : fun_tag;
                                           cenv : ctor_env;
                                           fenv : fun_env; (* Maps fun_tag's to (number of args,  list (arg no)) *)
                                           nenv : name_env;
                                           log : list string;
                                         }.
  
  (* TODO: better name? *)
  Definition compM' := compM unit (comp_data * S).
  
  (* Get the environment name *)
  Definition get_name_env (_ : unit) : compM' name_env :=
    s <- compM.get ;;
    ret (nenv (fst s)).

  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var *)
  Definition get_name (old_var : var) (suff : string) : compM' var :=
    p <- compM.get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := add_entry names n old_var suff in
    compM.put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.


  Definition add_entry_from_map (nenv nenv_old:name_env)
             (x : var) (x_origin : var) (suff : String.string) : name_env :=
    match M.get x_origin nenv_old  with
  | Some (BasicAst.nNamed s) => M.set x (BasicAst.nNamed (String.append s suff)) nenv
  | Some BasicAst.nAnon => M.set x (BasicAst.nNamed (String.append "anon" suff)) nenv
  | None => M.set x (BasicAst.nNamed (String.append "anon" suff)) nenv
  end.


  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var.
      The old name is found in the old name environment, passed as argument.  *)
  (* This is useful when we are alpha-renaming all variables of the program so we want to
     constuct a new name environment. *)
  Definition get_name' (old_var : var) (suff : string) (nenv_old : name_env) : compM' var :=
    p <- compM.get ;;
    let '(mkCompData n c i f e fenv nenv log, st) := p in
    let nenv' := add_entry_from_map nenv nenv_old n old_var suff in
    compM.put (mkCompData ((n+1)%positive) c i f e fenv nenv' log, st) ;;
    ret n.

  
  Definition get_names_lst (old : list var) (suff : string) : compM' (list var) :=
    mapM (fun o => get_name o suff) old.

  Definition get_names_lst' (old : list var) (suff : string) (nenv_old : name_env) : compM' (list var) :=
    mapM (fun o => get_name' o suff nenv_old) old.

  
  (** Get a fresh name, and register a pretty name by appending a suffix to the pretty name of the old var *)
  Definition get_named (s : name) : compM' var :=
    p <- compM.get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := M.set n s names in
    compM.put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  Definition get_named_lst (s : list name) : compM' (list var) := mapM get_named s.

  
  (** Get a fresh name, and create a new pretty name *)
  Definition get_named_str (name : string) : compM' var :=
    p <- compM.get ;;
    let '(mkCompData n c i f e fenv names log, st) := p in
    let names' := add_entry_str names n name in
    compM.put (mkCompData ((n+1)%positive) c i f e fenv names' log, st) ;;
    ret n.

  (* Get the next fresh record tag of a fresh type *)
  Definition make_record_ctor_tag (n : N) : compM' ctor_tag :=
    p <- compM.get ;;
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := {| ctor_name := nAnon
                ; ctor_ind_name := nAnon
                ; ctor_ind_tag := i
                ; ctor_arity := n
                ; ctor_ordinal := 0%N
                |} : ctor_ty_info in
    let e' := ((M.set c inf e) : ctor_env) in
    compM.put (mkCompData x (c+1)%positive (i+1)%positive f e' fenv names log, st) ;;
    ret c.

  (* Register a constructor tag of some type i *)
  Definition register_record_ctor_tag (c : ctor_tag) (i : ind_tag) (n : N) : compM' unit :=
    p <- compM.get ;;
    let '(mkCompData x c i f e fenv names log, st) := p  in
    let inf := {| ctor_name := nAnon
                ; ctor_ind_name := nAnon
                ; ctor_ind_tag := i
                ; ctor_arity := n
                ; ctor_ordinal := 0%N
                |} : ctor_ty_info in
    let e' := ((M.set c inf e) : ctor_env) in
    compM.put (mkCompData x c i f e' fenv names log, st).

  (* Get the pretty name of a binder *)
  Definition get_pp_name (x : var) : compM' string :=
    nenv <- get_name_env tt ;;
    ret (show_tree (show_var nenv x)).

  (* Get the pretty name of a list of binders *)
  Definition get_pp_names_list (xs : list var) : compM' (list string) := mapM get_pp_name xs.

  (* Log a new message *)
  Definition log_msg (msg : string) : compM' unit :=
    s <- compM.get ;;
    let '(mkCompData x c i f e fenv names log, st) := s in
    compM.put (mkCompData x c i f e fenv names (msg :: log)%string, st).

  (* Access the transformation specific state *)
  Definition get_state (_ : unit) : compM' S :=
    s <- compM.get ;;
    ret (snd s).

  (* Access the transformation specific state *)
  Definition put_state (st : S) : compM' unit :=
    s <- compM.get ;;
    compM.put (fst s, st).

  (** Get a fresh function tag and register it in fun_env *)
  Definition get_ftag (arity : N) : compM' fun_tag :=
    p <- compM.get ;;
    let '(mkCompData x c i f e fenv names log, st) := p in
    compM.put (mkCompData x c i (f + 1)%positive e (M.set f (arity, (fromN (0%N) (BinNat.N.to_nat arity))) fenv) names log, st) ;;
    ret f.

  Definition run_compM {A} (m: compM' A) (st : comp_data) (s : S)
    : error A * (comp_data * S) := runState m tt (st, s).

  Definition pack_data := mkCompData.

  (* Returns the name environment and the log *)
  Definition get_result (d : comp_data) : name_env * string := (nenv d, log_to_string (log d)).
  
End CompM.

(* Lemmas about [get_name] and [get_names_lst] *)

Definition Range (x1 x2 : positive) : Ensemble var := fun z => (x1 <= z < x2)%positive.

Lemma Disjoint_Range (x1 x2 x1' x2' : positive) :
  (x2 <= x1')%positive ->
  Disjoint _ (Range x1 x2) (Range x1' x2').
Proof.
  intros Hleq. constructor. intros x Hin. inv Hin.
  unfold Range, Ensembles.In in *. simpl in *. zify. omega.
Qed.    

Lemma Range_Subset (x1 x2 x1' x2' : positive) :
  (x1 <= x1')%positive ->
  (x2' <= x2)%positive ->
  Range x1' x2' \subset Range x1 x2.
Proof.
  intros H1 H2. intros z Hin. unfold Range, Ensembles.In in *.
  inv Hin. zify. omega.
Qed.
          
Lemma fresh_Range S (x1 x2 : positive) :
  identifiers.fresh S x1 ->
  Range x1 x2 \subset S.
Proof.
  intros Hin z Hin'. inv Hin'. eapply Hin. eassumption.
Qed.

Opaque bind ret. 

(** Spec for [get_name] *)
Lemma get_name_spec A S y str :
  {{ fun _ (s : comp_data * A) => identifiers.fresh S (next_var (fst s)) }}
    get_name y str
  {{ fun (r: unit) s x s' =>
       x \in S /\
       x \in Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) < next_var (fst s'))%positive /\
       identifiers.fresh (S \\ [set x]) (next_var (fst s'))      
  }}.  
Proof. 
  eapply pre_post_mp_l.
  eapply bind_triple. now eapply get_triple.  
  intros [[] w1] [[] w2].
  eapply pre_post_mp_l. simpl.
  eapply bind_triple. now eapply put_triple.
  intros x [r3 w3].
  eapply return_triple. 
  intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
  split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. omega.
  simpl. split. zify; omega.
  intros z Hin. constructor. eapply H; eauto. zify. omega.
  intros Hc. inv Hc. zify; omega.
Qed.

Lemma get_names_lst_spec A S ns str :
  {{ fun _ (s : comp_data * A) => identifiers.fresh S (next_var (fst s)) }}
    get_names_lst ns str
  {{ fun (r: unit) s xs s' =>
       NoDup xs /\ List.length xs = List.length ns /\
       FromList xs \subset S /\
       FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) <= next_var (fst s'))%positive /\
       identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.  
Proof.
  unfold get_names_lst. revert S; induction ns; intros S.
  - simpl. eapply return_triple.
    intros. repeat normalize_sets. split; eauto.
    sets. now constructor. split; eauto.
    split. now sets. split. sets. split. reflexivity. eassumption.
  - simpl. eapply bind_triple. eapply get_name_spec.
    intros x w.
    eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHns.
    intros xs w'. eapply return_triple. intros. destructAll.
    repeat normalize_sets. split; [| split; [| split; [| split; [| split ]]]].
    + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
    + simpl. congruence.
    + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
    + eapply Union_Included. eapply Singleton_Included.
      eapply Range_Subset; [| | eassumption ]. reflexivity. zify. omega.
      eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. reflexivity.
    + zify; omega.
    + rewrite <- Setminus_Union. eassumption.
Qed.

(** Spec for [get_name] *)
Lemma get_name'_spec A S y str old_m :
  {{ fun _ (s : comp_data * A) => identifiers.fresh S (next_var (fst s)) }}
    get_name' y str old_m
  {{ fun (r: unit) s x s' =>
       x \in S /\
       x \in Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) < next_var (fst s'))%positive /\
       identifiers.fresh (S \\ [set x]) (next_var (fst s'))      
  }}.  
Proof. 
  eapply pre_post_mp_l.
  eapply bind_triple. now eapply get_triple.  
  intros [[] w1] [[] w2].
  eapply pre_post_mp_l. simpl.
  eapply bind_triple. now eapply put_triple.
  intros x [r3 w3].
  eapply return_triple. 
  intros ? [r4 w4] H2. inv H2. intros [H1 H2]. inv H1; inv H2. intros.
  split. eapply H. reflexivity. split. unfold Range, Ensembles.In. simpl. zify. omega.
  simpl. split. zify; omega.
  intros z Hin. constructor. eapply H; eauto. zify. omega.
  intros Hc. inv Hc. zify; omega.
Qed.

Lemma get_names_lst'_spec A S ns str old_m :
  {{ fun _ (s : comp_data * A) => identifiers.fresh S (next_var (fst s)) }}
    get_names_lst' ns str old_m
  {{ fun (r: unit) s xs s' =>
       NoDup xs /\ List.length xs = List.length ns /\
       FromList xs \subset S /\
       FromList xs \subset Range (next_var (fst s)) (next_var (fst s')) /\
       (next_var (fst s) <= next_var (fst s'))%positive /\
       identifiers.fresh (S \\ FromList xs) (next_var (fst s')) }}.  
Proof.
  unfold get_names_lst. revert S; induction ns; intros S.
  - simpl. eapply return_triple.
    intros. repeat normalize_sets. split; eauto.
    sets. now constructor. split; eauto.
    split. now sets. split. sets. split. reflexivity. eassumption.
  - simpl. eapply bind_triple. eapply get_name'_spec.
    intros x w.
    eapply bind_triple. eapply frame_rule. eapply frame_rule. eapply frame_rule. eapply IHns.
    intros xs w'. eapply return_triple. intros. destructAll.
    repeat normalize_sets. split; [| split; [| split; [| split; [| split ]]]].
    + constructor; eauto. intros Hc. eapply H4 in Hc. inv Hc. now eauto.
    + simpl. congruence.
    + eapply Union_Included. sets. eapply Included_trans. eapply H4. sets.
    + eapply Union_Included. eapply Singleton_Included.
      eapply Range_Subset; [| | eassumption ]. reflexivity. zify. omega.
      eapply Included_trans. eassumption. eapply Range_Subset. zify; omega. reflexivity.
    + zify; omega.
    + rewrite <- Setminus_Union. eassumption.
Qed.


Lemma get_state_spec A :
  {{ fun _ (s : comp_data * A) => True }}
    get_state tt
  {{ fun (r: unit) s x s' => x = snd s /\ s = s' }}.
Proof.
  unfold get_state. eapply bind_triple.
  - eapply get_triple.
  - intros x w. eapply return_triple. firstorder.
    subst. reflexivity.
Qed.

Lemma put_state_spec A st :
  {{ fun _ (s : comp_data * A) => True }}
    put_state st
  {{ fun (r: unit) s _ s' => fst s' = fst s /\ snd s' = st }}.
Proof.
  unfold get_state. eapply bind_triple.
  - eapply get_triple.
  - intros x w. simpl. eapply pre_curry_l. intros Heq; subst. 
    eapply pre_post_mp_l. eapply post_weakening.
    2:{ eapply put_triple. } firstorder. simpl in *. subst. reflexivity.
    simpl in *. subst. reflexivity.
Qed.
