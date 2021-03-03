Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import L6.Ensembles_util L6.map_util L6.List_util.
Require Import L6.state L6.alpha_conv L6.identifiers L6.functions L6.shrink_cps L6.stemctx.
Require Import L6.Prototype.
Require Import L6.cps L6.rename L6.scoping L6.cps_proto L6.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

Unset Strict Unquote Universe Mode.

(** * Shrink rewrites *)

(** Known constructor values *)

(* (x ↦ Con c ys) ∈ C *)
Definition known_ctor {A} x c ys (C : exp_c A exp_univ_exp) : Prop :=
  exists D E, C = D >:: Econstr3 x c ys >++ E.

(** Occurrence counts *)

Definition count_var (x_in x : var) : nat := if (x_in =? x)%positive then 1 else 0.
Definition total : list nat -> nat := fold_right plus 0.
Definition count_vars x_in (xs : list var) : nat := total (map (count_var x_in) xs).
Definition count_ces' (count_exp : var -> exp -> nat) x_in (ces : list (ctor_tag * _)) : nat :=
  total (map (fun '(_, e) => count_exp x_in e) ces).
Definition count_fds' (count_exp : var -> exp -> nat) x_in : fundefs -> nat :=
  fix go fds :=
    match fds with
    | Fcons f t xs e fds => count_exp x_in e + go fds
    | Fnil => 0
    end.
Fixpoint count_exp x_in e {struct e} : nat :=
  match e with
  | Econstr x c ys e => count_vars x_in ys + count_exp x_in e
  | Ecase x ces => count_var x_in x + count_ces' count_exp x_in ces
  | Eproj x c n y e => count_var x_in y + count_exp x_in e
  | Eletapp x f ft ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Efun fds e => count_fds' count_exp x_in fds + count_exp x_in e
  | Eapp f ft xs => count_var x_in f + count_vars x_in xs
  | Eprim x p ys e => count_vars x_in ys + count_exp x_in e
  | Ehalt x => count_var x_in x
  end.
Definition count_ces := count_ces' count_exp.
Definition count_fds := count_fds' count_exp.

Inductive shrink_step : exp -> exp -> Prop :=
(* Case folding *)
| shrink_cfold : forall (C : frames_t exp_univ_exp _) x c ys e ces,
  known_ctor x c ys C /\ In (c, e) ces ->
  shrink_step (C ⟦ Ecase x ces ⟧) (C ⟦ Rec e ⟧)
(* Projection folding *)
| shrink_pfold : forall (C : frames_t exp_univ_exp _) x c ys y y' t n e,
  known_ctor x c ys C /\ nthN ys n = Some y' ->
  shrink_step (C ⟦ Eproj y t n x e ⟧) (C ⟦ Rec (rename_all_ns (M.set y y' (M.empty _)) e) ⟧)
(* Dead variable elimination *)
| shrink_dead_constr1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
  count_exp x e = 0 ->
  shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_constr2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ e ⟧))
| shrink_dead_proj1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  count_exp x e = 0 ->
  shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_proj2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ e ⟧))
| shrink_dead_prim1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  count_exp x e = 0 ->
  shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_prim2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ e ⟧)).

(** * Known constructors *)

Definition ctx_map := M.tree (ctor_tag * list var).
Definition R_ctors {A} (C : exp_c A exp_univ_exp) (ρ : ctx_map) : Prop :=
  forall x c ys, M.get x ρ = Some (c, ys) -> known_ctor x c ys C.

Instance Preserves_R_ctors : Preserves_R (@R_ctors).
Proof.
  intros A B fs fs_ok f [ρ Hρ]; destruct f; lazymatch goal with
  | |- Param (@R_ctors) (e_map (fun fs => fs >:: Econstr3 ?x' ?c' ?ys') fs) =>
    rename x' into x, c' into c, ys' into ys
  | _ =>
    exists ρ; unerase; intros x' c' ys' Hget'; specialize (Hρ x' c' ys' Hget');
    destruct Hρ as [D [E Hctx]];
    match goal with |- known_ctor _ _ _ (_ >:: ?f) => exists D, (E >:: f); now subst fs end
  end.
  exists (M.set x (c, ys) ρ); unerase; intros x' c' ys' Hget'; cbn in *.
  destruct (Pos.eq_dec x' x); [subst; rewrite M.gss in Hget'; inv Hget'; now exists fs, <[]>|].
  rewrite M.gso in Hget' by auto; destruct (Hρ x' c' ys' Hget') as [D [E Hctx]].
  exists D, (E >:: Econstr3 x c ys); now subst fs.
Defined.
Extraction Inline Preserves_R_ctors.

(** * Occurrence counts *)

Definition c_map : Set := M.tree positive.

Section Census.

Context
  (* Update to occurrence counts *)
  (upd : option positive -> option positive)
  (* Delayed renaming *)
  (σ : r_map).

Definition census_var (x : var) (δ : c_map) : c_map :=
  let x := apply_r σ x in
  match upd (M.get x δ) with
  | Some n => M.set x n δ
  | None => M.remove x δ
  end.
Definition census_list {A} (census : A -> c_map -> c_map) (xs : list A) (δ : c_map) :=
  fold_right census δ xs.
Definition census_vars := census_list census_var.
Definition census_ces' (census_exp : exp -> c_map -> c_map) : list (ctor_tag * _) -> _ -> _ :=
  census_list (fun '(c, e) δ => census_exp e δ).
Definition census_fds' (census_exp : exp -> c_map -> c_map) :=
  fix go fds δ :=
    match fds with
    | Fcons f t xs e fds => census_exp e (go fds δ)
    | Fnil => δ
    end.
Fixpoint census_exp (e : exp) (δ : c_map) {struct e} : c_map :=
  match e with
  | Econstr x c ys e => census_vars ys (census_exp e δ)
  | Ecase x ces => census_var x (census_ces' census_exp ces δ)
  | Eproj x c n y e => census_var y (census_exp e δ)
  | Eletapp x f ft ys e => census_var f (census_vars ys (census_exp e δ))
  | Efun fds e => census_fds' census_exp fds (census_exp e δ)
  | Eapp f ft xs => census_var f (census_vars xs δ)
  | Eprim x p ys e => census_vars ys (census_exp e δ)
  | Ehalt x => census_var x δ
  end.
Definition census_ces := census_ces' census_exp.
Definition census_fds := census_fds' census_exp.

(** (census e δ)(x) = upd^(|σe|x)(δ(x)) *)

Lemma iter_fuse {A} n m (f : A -> A) x : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof.
  revert m; induction n as [|n IHn]; [reflexivity|intros; cbn].
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x); now rewrite IHn.
Qed.

Lemma census_var_corresp' x_in x δ :
  M.get x (census_var x_in δ) = Nat.iter (count_var x (apply_r σ x_in)) upd (M.get x δ).
Proof.
  unfold census_var, count_var in *; cbn in *.
  destruct (Pos.eqb_spec x (apply_r σ x_in)); cbn in *.
  - subst; destruct (upd (M.get (apply_r σ x_in) δ)) as [n|] eqn:Hn; now rewrite ?M.gss, ?M.grs.
  - destruct (upd (M.get (apply_r σ x_in) δ)) as [n'|] eqn:Hn; now rewrite ?M.gso, ?M.gro by auto.
Qed.

Fixpoint census_vars_corresp' xs x δ :
  M.get x (census_vars xs δ) = Nat.iter (count_vars x (apply_r_list σ xs)) upd (M.get x δ).
Proof.
  destruct xs as [|x' xs]; [reflexivity|cbn].
  change (fold_right census_var δ xs) with (census_vars xs δ).
  change (total (map _ ?xs)) with (count_vars x xs).
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x).
  change (map (apply_r σ) xs) with (apply_r_list σ xs).
  now rewrite <- iter_fuse, <- census_vars_corresp', <- census_var_corresp'.
Qed.

(* TODO: move to proto_util *)
Definition rename_all_ces σ ces : list (ctor_tag * exp) :=
  map (fun '(c, e) => (c, rename_all_ns σ e)) ces.

Ltac collapse_primes :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' census_exp) with census_ces in *;
  change (census_fds' census_exp) with census_fds in *;
  change (map (fun '(c, e) => (c, rename_all_ns ?σ e))) with (rename_all_ces σ) in *;
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x);
  change (total (map (fun '(_, e) => count_exp ?x e) ?ces)) with (count_ces x ces) in *;
  change (count_fds' count_exp) with count_fds in *.

Fixpoint census_exp_corresp' e x δ {struct e} :
  M.get x (census_exp e δ) = Nat.iter (count_exp x (rename_all_ns σ e)) upd (M.get x δ).
Proof.
  destruct e; cbn; collapse_primes; try solve [
    now rewrite <- ?iter_fuse, <- ?census_exp_corresp', <- ?census_vars_corresp', <- ?census_var_corresp'].
  - rename l into ces, v into x, x into x_in.
    enough (Hces : forall x δ,
             let count := count_ces x (rename_all_ces σ ces) in
             M.get x (census_ces ces δ) = Nat.iter count upd (M.get x δ)).
    { now rewrite <- iter_fuse, <- Hces, <- census_var_corresp'. }
    clear - census_exp_corresp'.
    induction ces as [|[c e] ces IHces]; [reflexivity|cbn; intros x δ; collapse_primes].
    now rewrite <- iter_fuse, <- IHces, <- census_exp_corresp'.
  - rename f into fds.
    enough (Hfds : forall x δ,
             let count := count_fds x (rename_all_fun_ns σ fds) in
             M.get x (census_fds fds δ) = Nat.iter count upd (M.get x δ)).
    { now rewrite <- iter_fuse, <- census_exp_corresp', <- Hfds. } 
    clear - census_exp_corresp'.
    induction fds as [f ft xs e fds IHfds|]; [cbn; intros x δ; collapse_primes|reflexivity].
    now rewrite <- iter_fuse, <- IHfds, <- census_exp_corresp'.
Qed.

Lemma census_ces_corresp' ces : forall x δ,
  M.get x (census_ces ces δ) = Nat.iter (count_ces x (rename_all_ces σ ces)) upd (M.get x δ).
Proof.
  induction ces as [|[c e] ces IHces]; [reflexivity|cbn; intros x δ; collapse_primes].
  now rewrite <- iter_fuse, <- IHces, <- census_exp_corresp'.
Qed.

End Census.

Ltac collapse_primes :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' (census_exp ?upd ?σ)) with (census_ces upd σ) in *;
  change (census_fds' (census_exp ?upd ?σ)) with (census_fds upd σ) in *;
  change (map (fun '(c, e) => (c, rename_all_ns ?σ e))) with (rename_all_ces σ) in *;
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x);
  change (total (map (fun '(_, e) => count_exp ?x e) ?ces)) with (count_ces x ces) in *;
  change (count_fds' count_exp) with count_fds in *;
  change (count_ces' count_exp) with count_ces in *;
  change (map (apply_r ?σ) ?xs) with (apply_r_list σ xs) in *;
  change (total (map (count_var ?x) ?xs)) with (count_vars x xs) in *.

(** Some convenient specializations *)

Definition succ_upd n :=
  match n with
  | Some n => Some (Pos.succ n)
  | None => Some 1
  end%positive.

Definition pred_upd n :=
  match n with
  | Some 1 | None => None
  | Some n => Some (Pos.pred n)
  end%positive.

Notation census_exp_succ := (census_exp succ_upd).
Notation census_exp_pred := (census_exp pred_upd).
Notation census_ces_succ := (census_ces succ_upd).
Notation census_ces_pred := (census_ces pred_upd).

Definition nat_of_count n :=
  match n with
  | Some n => Pos.to_nat n
  | None => 0
  end.

Lemma nat_of_count_succ_upd n : nat_of_count (succ_upd n) = S (nat_of_count n).
Proof. destruct n as [n|]; cbn; zify; lia. Qed.

Lemma nat_of_count_iter_succ_upd n c : nat_of_count (Nat.iter n succ_upd c) = n + nat_of_count c.
Proof.
  induction n as [|n IHn]; [reflexivity|unfold Nat.iter in *; cbn].
  now rewrite nat_of_count_succ_upd, IHn.
Qed.

Lemma nat_of_count_pred_upd n : nat_of_count (pred_upd n) = nat_of_count n - 1.
Proof.
  destruct n; cbn; [|auto].
  destruct (Pos.eq_dec p 1)%positive; subst; [reflexivity|].
  match goal with
  | |- nat_of_count ?e = _ =>
    assert (Heqn : e = Some (Pos.pred p)) by (now destruct p)
  end.
  rewrite Heqn; cbn; lia.
Qed.

Lemma nat_of_count_iter_pred_upd n c : nat_of_count (Nat.iter n pred_upd c) = nat_of_count c - n.
Proof.
  induction n as [|n IHn]; [cbn; lia|unfold Nat.iter in *; cbn].
  now rewrite nat_of_count_pred_upd, IHn.
Qed.

Definition get_count (x : var) δ := nat_of_count (M.get x δ).

Lemma census_exp_succ_corresp e x σ δ :
  get_count x (census_exp_succ σ e δ) = count_exp x (rename_all_ns σ e) + get_count x δ.
Proof. unfold get_count; now rewrite census_exp_corresp', nat_of_count_iter_succ_upd. Qed.

Lemma census_exp_pred_corresp e x σ δ :
  get_count x (census_exp_pred σ e δ) = get_count x δ - count_exp x (rename_all_ns σ e).
Proof. unfold get_count; now rewrite census_exp_corresp', nat_of_count_iter_pred_upd. Qed.

Lemma census_ces_pred_corresp ces x σ δ :
  get_count x (census_ces_pred σ ces δ) = get_count x δ - count_ces x (rename_all_ces σ ces).
Proof. unfold get_count; now rewrite census_ces_corresp', nat_of_count_iter_pred_upd. Qed.

(** * Occurrence counts for one-hole contexts *)

Definition count_frame {A B} (x_in : var) (f : exp_frame_t A B) : nat. refine(
  match f with
  | pair_ctor_tag_exp0 e => count_exp x_in e
  | pair_ctor_tag_exp1 c => 0
  | cons_prod_ctor_tag_exp0 ces => count_ces x_in ces
  | cons_prod_ctor_tag_exp1 (_, e) => count_exp x_in e
  | Fcons0 ft xs e fds => count_exp x_in e + count_fds x_in fds
  | Fcons1 f xs e fds => count_exp x_in e + count_fds x_in fds
  | Fcons2 f ft e fds => count_exp x_in e + count_fds x_in fds
  | Fcons3 f ft xs fds => count_fds x_in fds
  | Fcons4 f ft xs e => count_exp x_in e
  | Econstr0 c ys e => count_vars x_in ys + count_exp x_in e
  | Econstr1 x ys e => count_vars x_in ys + count_exp x_in e
  | Econstr2 x c e => count_exp x_in e
  | Econstr3 x c ys => count_vars x_in ys
  | Ecase0 ces => count_ces x_in ces
  | Ecase1 x => count_var x_in x
  | Eproj0 c n y e => count_var x_in y + count_exp x_in e
  | Eproj1 x n y e => count_var x_in y + count_exp x_in e
  | Eproj2 x c y e => count_var x_in y + count_exp x_in e
  | Eproj3 x c n e => count_exp x_in e
  | Eproj4 x c n y => count_var x_in y
  | Eletapp0 f ft ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Eletapp1 x ft ys e => count_vars x_in ys + count_exp x_in e
  | Eletapp2 x f ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Eletapp3 x f ft e => count_var x_in f + count_exp x_in e
  | Eletapp4 x f ft ys => count_var x_in f + count_vars x_in ys
  | Efun0 e => count_exp x_in e
  | Efun1 fds => count_fds x_in fds
  | Eapp0 ft xs => count_vars x_in xs
  | Eapp1 f xs => count_var x_in f + count_vars x_in xs
  | Eapp2 f ft => count_var x_in f
  | Eprim0 p ys e => count_vars x_in ys + count_exp x_in e
  | Eprim1 x ys e => count_vars x_in ys + count_exp x_in e
  | Eprim2 x p e => count_exp x_in e
  | Eprim3 x p ys => count_vars x_in ys
  | Ehalt0 => 0
  end).
Defined.

Fixpoint count_ctx {A B} (x_in : var) (C : exp_c A B) {struct C} : nat :=
  match C with
  | <[]> => 0
  | C >:: f => count_ctx x_in C + count_frame x_in f
  end.

Definition count {A} x : univD A -> nat :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => count_exp x e
  | exp_univ_list_prod_ctor_tag_exp => fun ces => count_ces x ces
  | exp_univ_fundefs => fun fds => count_fds x fds
  | exp_univ_exp => fun e => count_exp x e
  | exp_univ_var => fun y => count_var x y
  | exp_univ_fun_tag => fun _ => 0
  | exp_univ_ctor_tag => fun _ => 0
  | exp_univ_prim => fun _ => 0
  | exp_univ_N => fun _ => 0
  | exp_univ_list_var => fun xs => count_vars x xs
  end.

(* TODO: Merge with uncurry_proto and move to util *)
Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Lemma count_frame_app A B (f : exp_frame_t A B) e x :
  match A with
  | exp_univ_var
  | exp_univ_fun_tag
  | exp_univ_ctor_tag
  | exp_univ_prim
  | exp_univ_N
  | exp_univ_list_var => True
  | _ => count x (frameD f e) = count_frame x f + count x e
  end.
Proof.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct A', f; try solve [discriminate|exact I];
  destruct B'; try solve [discriminate|reflexivity].
  - destruct e as [c e]; cbn. change (total _) with (count_ces x l); lia.
  - cbn; change (count_fds' count_exp) with count_fds; lia.
  - cbn; lia.
Qed.

Lemma count_ctx_app' : forall n A B (C : exp_c A B) e x,
  frames_len C = n ->
  match A with
  | exp_univ_var
  | exp_univ_fun_tag
  | exp_univ_ctor_tag
  | exp_univ_prim
  | exp_univ_N
  | exp_univ_list_var => True
  | _ => count x (C ⟦ e ⟧) = count_ctx x C + count x e
  end.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros A B C e x Hlen.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct C as [|A AB B f C]; [subst; cbn; now destruct A|].
  clearpose HAB' AB' AB.
  destruct A', f; try solve [discriminate|exact I]; destruct AB'; try discriminate;
  cbn in Hlen; rewrite framesD_cons; assert (Hlt : frames_len C < n) by (cbn; lia);
  specialize IHn with (m := frames_len C) (C := C) (x := x);
  specialize (IHn Hlt); lazy iota in IHn; rewrite IHn by reflexivity;
  match type of HA' with ?T = _ => rewrite (@count_frame_app T) end; cbn; lia.
Qed.

Corollary count_ctx_app : forall (C : exp_c exp_univ_exp exp_univ_exp) e x,
  count_exp x (C ⟦ e ⟧) = count_ctx x C + count x e.
Proof. intros; now apply (@count_ctx_app' (frames_len C) exp_univ_exp exp_univ_exp). Qed.

Corollary count_ctx_fds_app : forall (C : exp_c exp_univ_fundefs exp_univ_exp) fds x,
  count_exp x (C ⟦ fds ⟧) = count_ctx x C + count x fds.
Proof. intros; now apply (@count_ctx_app' (frames_len C) exp_univ_fundefs exp_univ_exp). Qed.

(* TODO: move to proto_util *)
Lemma var_eq_dec : forall x y : var, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Lemma count_var_neq : forall (x y : var), x <> y -> count_var x y = 0. 
Proof. unfold count_var; intros x y Hne; cbn; destruct (Pos.eqb_spec x y); congruence. Qed.

(** * State variable *)

Definition S_shrink {A} (C : exp_c A exp_univ_exp) (e : univD A) (δ : c_map) : Prop :=
  well_scoped (C ⟦ e ⟧) /\ (forall x, get_count x δ = count_exp x (C ⟦ e ⟧)).

Instance Preserves_S_up_shrink : Preserves_S_up (@S_shrink).
Proof. intros A B fs fs_ok f x δ; exact δ. Defined.
Instance Preserves_S_dn_shrink : Preserves_S_dn (@S_shrink).
Proof. intros A B fs fs_ok f x δ; exact δ. Defined.
Extraction Inline Preserves_S_up_shrink Preserves_S_dn_shrink.

Definition R_shrink : forall {A}, exp_c A exp_univ_exp -> _ -> Prop := @R_ctors.

(** * Delayed renaming *)

(* TODO: move to proto_util *)

Definition domain' (σ : r_map) := domain (fun x => M.get x σ).

Lemma empty_domain' : domain' (M.empty _) <--> Empty_set _.
Proof.
  split; unfold domain', domain; [|inversion 1].
  intros x [y Hxy]; now rewrite M.gempty in Hxy.
Qed.

Lemma domain'_set : forall x y σ, domain' (M.set x y σ) \subset x |: domain' σ.
Proof.
  clear; intros x y σ arb; unfold domain', domain, Ensembles.In; cbn.
  intros [z Hz]. destruct (Pos.eq_dec arb x); [subst; rewrite M.gss in Hz; inv Hz; now left|].
  now (right; rewrite M.gso in Hz by auto).
Qed.

Lemma image''_set : forall x y σ, image'' (M.set x y σ) \subset y |: image'' σ.
Proof.
  clear; intros x y σ arb; unfold image'', domain, Ensembles.In; cbn.
  intros [z Hz]. destruct (Pos.eq_dec z x); [subst; rewrite M.gss in Hz; inv Hz; now left|].
  now (right; rewrite M.gso in Hz by auto).
Qed.

(* TODO: move to proto_util *)
Definition bound {A} : univD A -> Ensemble cps.var :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => bound_var e
  | exp_univ_list_prod_ctor_tag_exp => fun ces => bound_var_ces ces
  | exp_univ_fundefs => fun fds => bound_var_fundefs fds
  | exp_univ_exp => fun e => bound_var e
  | exp_univ_var => fun _ => Empty_set _
  | exp_univ_fun_tag => fun _ => Empty_set _
  | exp_univ_ctor_tag => fun _ => Empty_set _
  | exp_univ_prim => fun _ => Empty_set _
  | exp_univ_N => fun _ => Empty_set _
  | exp_univ_list_var => fun _ => Empty_set _
  end.

Definition D_rename {A} (e : univD A) (σ : r_map) : Prop :=
  Disjoint _ (domain' σ) (bound e) /\ 
  Disjoint _ (image'' σ) (bound e).

Definition rename {A} (σ : r_map) : univD A -> univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(c, e) => (c, rename_all_ns σ e)
  | exp_univ_list_prod_ctor_tag_exp => fun ces => map (fun '(c, e) => (c, rename_all_ns σ e)) ces
  | exp_univ_fundefs => fun fds => rename_all_fun_ns σ fds
  | exp_univ_exp => fun e => rename_all_ns σ e
  | exp_univ_var => fun x => apply_r σ x
  | exp_univ_fun_tag => fun ft => ft
  | exp_univ_ctor_tag => fun c => c
  | exp_univ_prim => fun p => p
  | exp_univ_N => fun n => n
  | exp_univ_list_var => fun xs => apply_r_list σ xs
  end.

(* TODO: move to proto_util *)
Lemma apply_r_id x : apply_r (M.empty _) x = x.
Proof. unfold apply_r; cbn; now rewrite M.gempty. Qed.

Fixpoint apply_r_list_id xs {struct xs} : apply_r_list (M.empty _) xs = xs.
Proof.
  destruct xs as [|x xs]; [reflexivity|cbn].
  change (map _ xs) with (apply_r_list (M.empty _) xs).
  now rewrite apply_r_empty, apply_r_list_id.
Qed.

(* TODO: move to proto_util *)
Fixpoint rename_all_id e {struct e} : rename_all_ns (M.empty _) e = e.
Proof.
  destruct e; cbn; try now rewrite ?apply_r_list_id, ?apply_r_id, ?rename_all_id, ?apply_r_empty.
  Guarded.
  - rewrite apply_r_empty; f_equal; induction l as [|[c e] ces IHces]; [reflexivity|cbn].
    now rewrite IHces, rename_all_id.
  - rewrite rename_all_id; f_equal; induction f as [f ft xs e_body fds IHfds|]; [cbn|reflexivity].
    now rewrite IHfds, rename_all_id.
Qed.

Instance Delayed_D_rename : Delayed (@D_rename).
Proof.
  unshelve econstructor.
  - intros A e [σ Hσ]; exact (rename σ e).
  - intros A e; exists (M.empty _); unfold D_rename; rewrite empty_domain', empty_image; eauto with Ensembles_DB.
  - cbn; intros; destruct A; cbn in *;
      repeat match goal with |- context [let '_ := ?e in _] => destruct e end;
      rewrite ?apply_r_empty, ?apply_r_id, ?apply_r_list_id, ?rename_all_id; auto;
      try (apply MCList.map_id_f; intros []; cbn; now rewrite rename_all_id).
    pose proof (rename_all_id (Efun e (Ehalt 1%positive))) as rename_all_fun_id.
    now inversion rename_all_fun_id.
Defined.
Extraction Inline Delayed_D_rename.

(** * Functional definition *)

(** Case folding helpers *)

Fixpoint find_case (c : ctor_tag) (ces : list (ctor_tag * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if c =? c' then Some e else find_case c ces
  end%positive.

Lemma find_case_spec c e ces :
  find_case c ces = Some e -> exists ces1 ces2,
  ~ In c (map fst ces1) /\ ces = ces1 ++ (c, e) :: ces2.
Proof.
  induction ces as [|[c' e'] ces IHces]; [inversion 1|cbn].
  destruct (Pos.eqb_spec c c'); intros Heq; [inv Heq|].
  - exists [], ces; split; auto.
  - destruct (IHces Heq) as [ces1 [ces2 [Hnotin Hces12]]].
    exists ((c', e') :: ces1), ces2; cbn; subst ces; split; auto.
    intros [Heq'|Hin]; [now inv Heq'|auto].
Qed.

Lemma find_case_In c e ces : find_case c ces = Some e -> In (c, e) ces.
Proof.
  intros H; destruct (find_case_spec c e ces H) as [ces1 [ces2 [Hnotin Hces]]]; subst ces.
  apply in_or_app; right; now left.
Qed.

Fixpoint census_case_pred σ (c : ctor_tag) (ces : list (ctor_tag * exp)) δ :=
  match ces with
  | [] => δ
  | (c', e) :: ces =>
    if (c =? c')%positive
    then census_ces pred_upd σ ces δ
    else census_case_pred σ c ces (census_exp_pred σ e δ)
  end.

Lemma total_cons x xs : total (x :: xs) = x + total xs. Proof. reflexivity. Qed.
Lemma total_app xs ys : total (xs ++ ys) = total xs + total ys.
Proof. induction xs as [|x xs IHxs]; cbn; auto; rewrite IHxs; lia. Qed.

(* TODO: move to proto_util *)
Lemma In_ces_bound : forall c e ces, In (c, e) ces -> bound_var e \subset bound_var_ces ces.
Proof.
  induction ces as [|[c' e'] ces IHces]; [inversion 1|].
  destruct 1 as [Heq|Hne]; [inv Heq|]; cbn; eauto with Ensembles_DB.
Qed.

Fixpoint census_case_pred_spec n σ x δ ces ces1 c e ces2 {struct ces1} :
  ~ In c (map fst ces1) ->
  ces = ces1 ++ (c, e) :: ces2 ->
  get_count x δ = n + count_ces x (rename_all_ces σ ces) ->
  get_count x (census_case_pred σ c ces δ) = n + count_exp x (rename_all_ns σ e).
Proof.
  destruct ces1 as [|[c' e'] ces1]; intros Hin Heq Hget; cbn in Heq; subst ces.
  - unfold census_case_pred; fold census_case_pred. rewrite Pos.eqb_refl.
    cbn in Hget; collapse_primes; rewrite census_ces_pred_corresp, Hget; lia.
  - unfold count_ces, count_ces', rename_all_ces in Hget.
    repeat rewrite ?total_cons, ?total_app, ?map_cons, ?map_app in *; collapse_primes.
    unfold census_case_pred; fold census_case_pred.
    destruct (Pos.eqb_spec c c') as [Hc|Hc].
    { cbn in Hc; inv Hc; contradiction Hin; now left. }
    rewrite census_case_pred_spec with (n := n) (ces1 := ces1) (e := e) (ces2 := ces2); auto.
    + now cbn in Hin.
    + unfold count_ces, count_ces', rename_all_ces.
      repeat rewrite ?total_cons, ?total_app, ?map_cons, ?map_app in *; collapse_primes.
      rewrite census_exp_pred_corresp, Hget; lia.
Qed.

Notation census_var_pred := (census_var pred_upd).
Lemma census_var_pred_corresp x_in x σ δ :
  get_count x (census_var_pred σ x_in δ) = get_count x δ - count_var x (apply_r σ x_in).
Proof. unfold get_count; now rewrite census_var_corresp', nat_of_count_iter_pred_upd. Qed.

Notation census_vars_pred := (census_vars pred_upd).
Lemma census_vars_pred_corresp xs x σ δ :
  get_count x (census_vars_pred σ xs δ) = get_count x δ - count_vars x (apply_r_list σ xs).
Proof. unfold get_count; now rewrite census_vars_corresp', nat_of_count_iter_pred_upd. Qed.

(** Proj folding helpers *)

(* Substitute y for x in δ *)
Definition census_subst (y x : var) (δ : c_map) :=
  match M.get x δ with
  | None => δ
  | Some n =>
    match M.get y δ with
    | None => M.set y n (M.remove x δ)
    | Some m => M.set y (n + m)%positive (M.remove x δ)
    end
  end.

(* TODO: move to Ensembles_util or identifiers *)
Lemma occurs_free_Efun_nil : forall e, occurs_free (cps.Efun cps.Fnil e) <--> occurs_free e.
Proof. intros; split; repeat (normalize_occurs_free || normalize_sets); eauto with Ensembles_DB. Qed.

Lemma bound_var_Efun_nil : forall e, bound_var (cps.Efun cps.Fnil e) <--> bound_var e.
Proof. intros; split; repeat (normalize_bound_var || normalize_sets); eauto with Ensembles_DB. Qed.

Lemma census_subst_dom : forall (y x : var) (δ : c_map),
  x <> y ->
  get_count x (census_subst y x δ) = 0.
Proof.
  clear; intros y x δ Hne; unfold get_count, census_subst.
  destruct (M.get x δ) as [x'|] eqn:Hgetx; [|now rewrite Hgetx].
  destruct (M.get y δ) as [y'|] eqn:Hgety; (rewrite M.gso by now cbn); now rewrite M.grs.
Qed.

Lemma census_subst_ran : forall (y x : var) (δ : c_map),
  x <> y ->
  get_count y (census_subst y x δ) = get_count x δ + get_count y δ.
Proof.
  clear; intros y x δ Hne; unfold get_count, census_subst.
  destruct (M.get x δ) as [x'|] eqn:Hgetx; [|reflexivity].
  destruct (M.get y δ) as [y'|] eqn:Hgety;
  rewrite M.gss; cbn; lia.
Qed.

Lemma census_subst_neither : forall (z y x : var) (δ : c_map),
  x <> y -> z <> x -> z <> y ->
  get_count z (census_subst y x δ) = get_count z δ.
Proof.
  clear; intros z y x δ Hne Hz1 Hz2; unfold get_count, census_subst.
  destruct (M.get x δ) as [x'|] eqn:Hgetx; [|reflexivity].
  destruct (M.get y δ) as [y'|] eqn:Hgety; (rewrite M.gso by now cbn); now rewrite M.gro by now cbn.
Qed.

Lemma count_var_subst_dom : forall (y x : var) (x_in : var),
  x <> y -> count_var x (apply_r (M.set x y (M.empty _)) x_in) = 0.
Proof.
  clear; intros y x x_in Hne; unfold apply_r, apply_r, count_var; cbn.
  (assert (x <> y) by congruence); destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; now destruct (Pos.eqb_spec x y).
  - rewrite M.gso by auto; rewrite M.gempty. now destruct (Pos.eqb_spec x x_in).
Qed.

Lemma count_vars_subst_dom : forall (xs : list var) (y x : var),
  x <> y -> count_vars x (apply_r_list (M.set x y (M.empty _)) xs) = 0. 
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_dom by auto; rewrite IHxs by auto; auto.
Qed.

Fixpoint count_exp_subst_dom (y x : var) (e : exp) {struct e} :
  x <> y ->
  count_exp x (rename_all_ns (M.set x y (M.empty _)) e) = 0.
Proof.
  intros Hne; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_dom by auto
    |rewrite count_var_subst_dom by auto
    |rewrite count_vars_subst_dom by auto]; auto.
  - induction l as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
    now rewrite IHces, count_exp_subst_dom by auto.
  - clear e; rewrite Nat.add_0_r; induction f as [f ft xs e fds IHfds|]; cbn in *; auto; collapse_primes.
    now rewrite IHfds, count_exp_subst_dom by auto.
Qed.

Lemma count_var_subst_ran : forall (y x : var) (x_in : var),
  x <> y -> count_var y (apply_r (M.set x y (M.empty _)) x_in) = count_var x x_in + count_var y x_in.
Proof.
  clear; intros y x x_in Hne; unfold apply_r, apply_r, count_var; cbn.
  (assert (x <> y) by congruence); destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; cbn.
    destruct (Pos.eqb_spec y y), (Pos.eqb_spec x x), (Pos.eqb_spec y x); subst; auto; congruence.
  - rewrite M.gso by auto; rewrite M.gempty.
    destruct (Pos.eqb_spec y x_in), (Pos.eqb_spec x x_in); subst; auto; congruence.
Qed.

Lemma count_vars_subst_ran : forall (xs : list var) (y x : var),
  x <> y -> count_vars y (apply_r_list (M.set x y (M.empty _)) xs) = count_vars x xs + count_vars y xs.
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_ran by auto; rewrite IHxs by auto; lia.
Qed.

Fixpoint count_exp_subst_ran (y x : var) (e : exp) {struct e} :
  x <> y -> count_exp y (rename_all_ns (M.set x y (M.empty _)) e) = count_exp x e + count_exp y e.
Proof.
  intros Hne; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_ran by auto
    |rewrite count_var_subst_ran by auto
    |rewrite count_vars_subst_ran by auto]; auto; try lia.
  - rename l into ces, v into x'. enough (Hces :
      count_ces y (rename_all_ces (@M.set cps.var x y (M.empty cps.var)) ces) =
      count_ces x ces + count_ces y ces) by lia.
    induction ces as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
    now rewrite IHces, count_exp_subst_ran by auto.
  - rename f into fds. enough (Hfds :
      count_fds y (rename_all_fun_ns (@M.set cps.var x y (M.empty cps.var)) fds) =
      count_fds x fds + count_fds y fds) by lia.
    clear e; induction fds as [|[f ft xs e] fds IHfds]; cbn in *; auto; collapse_primes.
    now rewrite IHfds, count_exp_subst_ran by auto.
Qed.

Lemma count_var_subst_neither : forall (z y x : var) (x_in : var),
  x <> y -> z <> x -> z <> y ->
  count_var z (apply_r (M.set x y (M.empty _)) x_in) = count_var z x_in.
Proof.
  clear; intros z y x x_in Hne Hz1 Hz2; unfold apply_r, apply_r, count_var; cbn.
  destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; cbn; destruct (Pos.eqb_spec z y), (Pos.eqb_spec z x); subst; auto; congruence.
  - rewrite M.gso by auto; now rewrite M.gempty.
Qed.

Lemma count_vars_subst_neither : forall (xs : list var) (z y x : var),
  x <> y -> z <> x -> z <> y ->
  count_vars z (apply_r_list (M.set x y (M.empty _)) xs) = count_vars z xs.
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_neither by auto; rewrite IHxs by auto; lia.
Qed.

Fixpoint count_exp_subst_neither (z y x : var) (e : exp) {struct e} :
  x <> y -> z <> x -> z <> y ->
  count_exp z (rename_all_ns (M.set x y (M.empty _)) e) = count_exp z e.
Proof.
  intros Hne Hz1 Hz2; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_neither by auto
    |rewrite count_var_subst_neither by auto
    |rewrite count_vars_subst_neither by auto]; auto; try lia.
  - f_equal; induction l as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
  - f_equal; clear e; induction f as [|[f ft xs e] fds IHfds]; cbn in *; auto; collapse_primes.
Qed.

Lemma known_ctor_in_used_c {A} x c ys (C : exp_c A _) : known_ctor x c ys C -> x \in used_c C.
Proof. intros [D [E Heq]]; subst; rewrite !used_c_comp; cbn; left; right; now left. Qed.

(* Count = 0 --> dead variable *)

Lemma plus_zero_and n m : n + m = 0 -> n = 0 /\ m = 0. Proof. lia. Qed.

Lemma not_In_Setminus' {A} (S1 S2 : Ensemble A) x : ~ x \in S1 -> ~ x \in (S1 \\ S2).
Proof. rewrite not_In_Setminus; tauto. Qed.

Lemma count_dead_var x y : count_var x y = 0 -> ~ x \in [set y].
Proof. unfold count_var; cbn; destruct (Pos.eqb_spec x y); inversion 1; now inversion 1. Qed.

Fixpoint count_dead_vars x xs :
  count_vars x xs = 0 -> ~ x \in FromList xs.
Proof.
  destruct xs as [|x' xs]; [intros; inversion 1|cbn in *].
  change (total _) with (count_vars x xs).
  intros H; apply plus_zero_and in H; destruct H as [Hx Hxs].
  intros [Heq|Hin]; [subst; unfold count_var in Hx; now rewrite Pos.eqb_refl in Hx|].
  now apply (count_dead_vars x xs Hxs).
Qed.

Fixpoint count_dead_exp x e :
  count_exp x e = 0 -> ~ x \in occurs_free e.
Proof.
  destruct e; cbn in *; collapse_primes; repeat normalize_occurs_free; intros H;
    repeat match goal with
    | H : _ + _ = 0 |- _ => apply plus_zero_and in H; destruct H
    | H : count_var _ _ = 0 |- _ => apply count_dead_var in H; cbn in *
    | H : count_vars _ _ = 0 |- _ => apply count_dead_vars in H; cbn in *
    | H : count_exp ?x ?e = 0 |- _ => apply (count_dead_exp x e) in H; cbn in *
    | |- ~ _ \in (_ :|: _) => rewrite Union_demorgan; split
    | |- ~ x \in (_ \\ _) => apply not_In_Setminus'
    end; auto.
  - induction l as [|[c e] ces IHces]; cbn; [inversion 1; subst; now contradiction H|].
    change (total _) with (count_ces x ces); normalize_occurs_free; rewrite !Union_demorgan.
    rename H0 into Hcount; cbn in Hcount; change (total _) with (count_ces x ces) in Hcount.
    apply plus_zero_and in Hcount; destruct Hcount as [He Hces]; split; [|split]; auto.
    Guarded.
  - induction f as [f ft xs e_body fds IHfds|]; cbn; [|inversion 1; subst; now contradiction H].
    change (total _) with (count_fds x fds); normalize_occurs_free; rewrite !Union_demorgan.
    rename H into Hcount; cbn in Hcount; change (total _) with (count_fds x fds) in Hcount.
    apply plus_zero_and in Hcount; destruct Hcount as [He Hfds]; split; apply not_In_Setminus'; auto.
    Guarded.
Qed.

(** Shrink rewriter *)

Lemma used_var_count_zero x y :
  ~ x \in [set y] -> count_var x y = 0.
Proof.
  intros. apply not_In_Singleton in H. assert (Hne : x <> y) by congruence.
  now apply count_var_neq in Hne.
Qed.

Lemma used_vars_count_zero x xs :
  ~ x \in FromList xs -> count_vars x xs = 0.
Proof.
  induction xs as [|x' xs IHxs]; auto; cbn in *; normalize_roundtrips.
  intros Hor; apply Decidable.not_or in Hor; destruct Hor as [Hor1 Hor2]; collapse_primes.
  rewrite IHxs, used_var_count_zero; auto; cbn; now apply not_In_Singleton.
Qed.

Fixpoint used_exp_count_zero x e :
  ~ x \in used_vars e -> count_exp x e = 0.
Proof.
  destruct e; cbn in *; repeat normalize_used_vars; rewrite ?Union_demorgan;
  intros H; try solve [repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : ~ ?x \in [set ?y] |- _ => apply (used_var_count_zero x y) in H
  | H : ~ ?x \in FromList _ |- _ => apply (used_vars_count_zero x) in H
  | H : ~ ?x \in used_vars _ |- _ => apply (used_exp_count_zero x) in H
  end; collapse_primes; try solve [clear used_exp_count_zero; lia]].
  Guarded.
  - rewrite used_vars_Ecase, Union_demorgan in H; destruct H as [H1 H2].
    apply (used_var_count_zero) in H1; rewrite H1; cbn; clear H1.
    induction l as [|[c e] ces IHces]; auto; cbn in *; collapse_primes.
    change (~ ?S ?x) with (~ x \in S) in *.
    rewrite Union_demorgan in H2; destruct H2 as [H1 H2].
    apply (used_exp_count_zero x) in H1; rewrite H1; clear used_exp_count_zero.
    now rewrite IHces by auto.
  - destruct H.
    apply used_exp_count_zero in H0.
    rewrite H0, Nat.add_0_r; clear H0; induction f as [f ft xs e' fds IHfds|]; auto.
    cbn in *; collapse_primes; normalize_used_vars; rewrite !Union_demorgan in H.
    decompose [and] H; clear H.
    rewrite IHfds by auto.
    apply (used_exp_count_zero x) in H3; rewrite H3; reflexivity.
Qed.

Lemma used_ces_count_zero x ces :
  ~ x \in used_ces ces -> count_ces x ces = 0.
Proof.
  induction ces as [|[c e] ces IHces]; auto; cbn in *; change (~ ?S ?x) with (~ x \in S) in *; intros H.
  rewrite Union_demorgan in H; destruct H as [H1 H2]; collapse_primes.
  now rewrite used_exp_count_zero, IHces by auto.
Qed.

Lemma used_fds_count_zero x fds :
  ~ x \in used_vars_fundefs fds -> count_fds x fds = 0.
Proof.
  induction fds as [|[c e] fds IHfds]; auto; cbn in *; intros H.
  normalize_used_vars. rewrite ?Union_demorgan in H; decompose [and] H; clear H; collapse_primes.
  apply (used_exp_count_zero x) in H3; rewrite H3.
  rewrite IHfds; auto.
Qed.

Lemma used_frame_count_zero {A B} y (f : exp_frame_t A B) :
  ~ y \in used_frame f -> count_frame y f = 0.
Proof.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct A', f; try solve [discriminate|exact O];
  destruct B'; try solve [discriminate|reflexivity]; cbn in *;
  repeat match goal with |- context [let '_ := ?e in _] => destruct e end;
  normalize_roundtrips;
  change (~ In ?x ?xs) with (~ (FromList xs) x);
  change (~ ?S ?x) with (~ x \in S) in *; rewrite ?Union_demorgan; intros H;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : ~ ?x \in [set ?y] |- _ => apply (used_var_count_zero x y) in H
  | H : ~ ?x \in FromList _ |- _ => apply (used_vars_count_zero x) in H
  | H : ~ ?x \in used_vars _ |- _ => apply (used_exp_count_zero x) in H
  | H : ~ ?x \in used_ces _ |- _ => apply (used_ces_count_zero x) in H
  | H : ~ ?x \in used_vars_fundefs _ |- _ => apply (used_fds_count_zero x) in H
  end; cbn in *; auto; try lia.
Qed.

(* Move above to where other count_ctx ops are defined *)
Lemma count_ctx_comp' : forall n A AB B (C : exp_c AB B) (D : exp_c A AB) x,
  frames_len D = n ->
  match A with
  | exp_univ_var
  | exp_univ_fun_tag
  | exp_univ_ctor_tag
  | exp_univ_prim
  | exp_univ_N
  | exp_univ_list_var => True
  | _ => count_ctx x (C >++ D) = count_ctx x C + count_ctx x D
  end.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros A AB B C D x Hlen.
  clearpose HA' A' A; clearpose HAB' AB' AB.
  destruct D as [|A AAB AB f D]; [subst; cbn; now destruct A|].
  clearpose HAAB' AAB' AAB.
  destruct A', f; try solve [discriminate|exact I]; destruct AAB'; try discriminate;
  cbn in Hlen; assert (Hlt : frames_len D < n) by (cbn; lia);
  specialize IHn with (m := frames_len D) (C := C) (D := D) (x := x);
  specialize (IHn Hlt eq_refl); lazy iota in IHn; cbn in *; rewrite IHn; lia.
Qed.

Lemma used_c_count_zero' : forall n A B y (C : exp_c A B),
  frames_len C = n ->
  ~ y \in used_c C -> count_ctx y C = 0.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros A B y C Hlen.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct C as [|A AB B f C]; [subst; cbn; now destruct A|].
  clearpose HAB' AB' AB.
  destruct A', f; try solve [discriminate|exact I]; destruct AB'; try discriminate;
  change (?C >:: ?f) with (C >++ <[f]>); rewrite !used_c_comp, Union_demorgan;
  intros [HC Hf]; unfold used_c in Hf; normalize_sets; apply used_frame_count_zero in Hf;
  cbn; try (unfold count_ctx at 2; rewrite Hf);
  cbn in Hlen; assert (Hlt : frames_len C < n) by (cbn; lia);
  specialize IHn with (m := frames_len C) (C := C);
  specialize (IHn Hlt _ eq_refl HC); try rewrite IHn; auto.
Qed.

Lemma nthN_map {A B} n (f : A -> B) x (xs : list A) :
  nthN xs n = Some x -> nthN (map f xs) n = Some (f x).
Proof.
  revert n; induction xs; [cbn; congruence|cbn]; intros n.
  destruct (N.eq_dec n 0)%N; [subst; inversion 1; auto|].
  match goal with |- ?lhs = Some _ -> _ => assert (H : lhs = nthN xs (n - 1)) by (now destruct n) end.
  rewrite H; clear H; intros Heq.
  match goal with |- ?lhs = _ => assert (H : lhs = nthN (map f xs) (n - 1)) by (now destruct n) end.
  rewrite H; clear H.
  rewrite IHxs; auto.
Qed.

(** Projection folding facts *)

(* Borrow lemmas from Olivier's proof *)
Require Import L6.shrink_cps_correct.

Lemma rename_corresp y y' e :
  Disjoint _ [set y] (bound_var e) ->
  rename_all_ns (M.set y y' (M.empty cps.var)) e = rename.rename y' y e.
Proof.
  intros Hbv; unfold rename.rename.
  rewrite (proj1 (Disjoint_dom_rename_all_eq _)); auto.
  now rewrite Dom_map_set, Dom_map_empty; normalize_sets.
Qed.

Lemma proj_fold_y' (C : frames_t exp_univ_exp exp_univ_exp) D E x c ys y y' t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  C = D >:: Econstr3 x c ys >++ E ->
  nthN ys n = Some y' ->
  y' \in bound_stem_ctx ![D] :|: occurs_free (C ⟦ Eproj y t n x e ⟧).
Proof.
  intros Hscope HC Hnth. rewrite HC, !frames_compose_law, !framesD_cons, app_exp_c_eq in Hscope.
  apply well_scoped_fv in Hscope.
  rewrite HC, !frames_compose_law, !framesD_cons, app_exp_c_eq.
  apply Hscope; cbn; constructor.
  now eapply nthN_In.
Qed.

Lemma proj_fold_y_unbound (C : frames_t exp_univ_exp exp_univ_exp) x y t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  ~ y \in bound_var e.
Proof.
  intros Hscope; rewrite app_exp_c_eq in Hscope.
  apply well_scoped_inv in Hscope.
  destruct Hscope as [Huniq _]; cbn in *; inv Huniq; auto.
Qed.

Lemma proj_fold_y'_unbound (C : frames_t exp_univ_exp exp_univ_exp) x c ys y y' t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  known_ctor x c ys C ->
  nthN ys n = Some y' ->
  ~ y' \in bound_var e.
Proof.
  intros Hscope [D [E HC]] Hnth.
  pose (Hy' := HC); clearbody Hy'; eapply proj_fold_y' in Hy'; try eassumption.
  rewrite HC, !frames_compose_law, !framesD_cons, app_exp_c_eq in Hscope.
  inv Hy'.
  + destruct Hscope as [Huniq _]; rewrite (proj1 (ub_app_ctx_f _)) in Huniq. 
    destruct Huniq as [_ [_ Hdis]]; cbn in Hdis; normalize_bound_var_in_ctx.
    rewrite app_exp_c_eq in Hdis; cbn in Hdis; normalize_roundtrips; rewrite bound_var_app_ctx in Hdis.
    intros Hy'; destruct Hdis as [Hdis]; contradiction (Hdis y'); split.
    * now apply bound_stem_var.
    * normalize_bound_var; left; right; now left.
  + destruct Hscope as [_ Hdis]; rewrite bound_var_app_ctx in Hdis; intros Hy'.
    rewrite frames_compose_law with (fs := D >:: _), framesD_cons with (fs := D) in H.
    rewrite app_exp_c_eq in H.
    destruct Hdis as [Hdis]; contradiction (Hdis y'); split; auto.
    right; cbn; normalize_bound_var; rewrite app_exp_c_eq; cbn; normalize_roundtrips.
    rewrite bound_var_app_ctx; normalize_bound_var.
    cbn in Hy'; left; right; now left.
Qed.

Lemma proj_fold_x_ne_y (C : frames_t exp_univ_exp exp_univ_exp) x c ys y y' t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  known_ctor x c ys C -> nthN ys n = Some y' ->
  x <> y.
Proof.
  intros Hscope [D [E HC]] Hnth; rewrite HC, frames_compose_law, app_exp_c_eq in Hscope.
  apply well_scoped_inv in Hscope; cbn in Hscope.
  rewrite app_exp_c_eq in Hscope; apply well_scoped_inv in Hscope; cbn in Hscope.
  intros Heq; subst y; destruct Hscope as [_ Hdis]; cbn in Hdis; destruct Hdis as [Hdis].
  contradiction (Hdis x); normalize_bound_var; normalize_occurs_free; split; auto.
Qed.

Lemma proj_fold_y_ne_y' (C : frames_t exp_univ_exp exp_univ_exp) x c ys y y' t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  known_ctor x c ys C -> nthN ys n = Some y' ->
  y <> y'.
Proof.
  intros HWS [D [E Heq]] Hnth; unfold Rec.
  pose (Hy' := Heq); clearbody Hy'; eapply proj_fold_y' in Hy'; try eassumption.
  rewrite Heq, !frames_compose_law, !framesD_cons in HWS.
  intros Heq_y; subst y'.
  clearpose HP P (C ⟦ Eproj y t n x e ⟧).
  rewrite In_or_Iff_Union in Hy'; destruct Hy' as [Hy_stem|Hy_free].
  - assert (Hnuniq : ~ unique_bindings P). {
      rewrite HP, Heq, !frames_compose_law, !framesD_cons, app_exp_c_eq, (proj1 (ub_app_ctx_f _)).
      intros [HuniqD [Huniqs [Hdis]]]; contradiction (Hdis y); constructor.
      + now apply bound_stem_var.
      + cbn; normalize_bound_var; normalize_roundtrips.
        rewrite app_exp_c_eq; cbn; normalize_roundtrips; rewrite bound_var_app_ctx; normalize_bound_var.
        left; right; now right. }
    apply Hnuniq; rewrite HP, Heq, frames_compose_law, framesD_cons.
    apply HWS.
  - destruct HWS as [Huniq [Hdis]]; contradiction (Hdis y); constructor.
    + cbn; normalize_roundtrips.
      rewrite !app_exp_c_eq; cbn; normalize_roundtrips; rewrite bound_var_app_ctx; normalize_bound_var.
      normalize_roundtrips; rewrite bound_var_app_ctx; normalize_bound_var.
      right; left; now right.
    + rewrite Heq, frames_compose_law, framesD_cons in Hy_free; apply Hy_free.
Qed.

Definition map_ext_eq σ1 σ2 := (forall x, apply_r σ1 x = apply_r σ2 x).

Lemma apply_r_eq σ1 σ2 x :
  map_ext_eq σ1 σ2 -> apply_r σ1 x = apply_r σ2 x.
Proof. intros H; apply H. Qed.

Lemma apply_r_list_eq σ1 σ2 xs :
  map_ext_eq σ1 σ2 -> apply_r_list σ1 xs = apply_r_list σ2 xs.
Proof.
  induction xs as [|x xs IHxs]; auto; intros Heq; simpl.
  now erewrite apply_r_eq, IHxs by eauto.
Qed.

Fixpoint rename_eq σ1 σ2 e {struct e} :
  map_ext_eq σ1 σ2 -> rename_all_ns σ1 e = rename_all_ns σ2 e.
Proof.
  destruct e; intros Heq;
    try solve [simpl; now erewrite ?apply_r_eq, ?apply_r_list_eq, ?rename_eq by eauto].
  - simpl; collapse_primes; erewrite apply_r_eq by eauto; f_equal.
    clear v; induction l as [|[c e] ces IHces]; auto; simpl.
    now erewrite rename_eq, IHces by eauto.
  - simpl; collapse_primes; erewrite rename_eq by eauto; f_equal.
    clear e; induction f as [f ft xs e fds IHfds|]; auto; simpl.
    now erewrite rename_eq, IHfds by eauto.
Qed.

Definition fused σ1 σ2 σ := (forall x, apply_r σ1 (apply_r σ2 x) = apply_r σ x).

Lemma apply_r_fuse σ1 σ2 σ x :
  fused σ1 σ2 σ -> apply_r σ1 (apply_r σ2 x) = apply_r σ x.
Proof. intros H; apply H. Qed.

Lemma apply_r_list_fuse σ1 σ2 σ xs :
  fused σ1 σ2 σ -> apply_r_list σ1 (apply_r_list σ2 xs) = apply_r_list σ xs.
Proof.
  induction xs as [|x xs IHxs]; auto; intros Hfuse; simpl.
  now erewrite apply_r_fuse, IHxs by eauto.
Qed.

Fixpoint rename_fuse σ1 σ2 σ e {struct e} :
  fused σ1 σ2 σ -> rename_all_ns σ1 (rename_all_ns σ2 e) = rename_all_ns σ e.
Proof.
  destruct e; intros Hfuse;
    try solve [simpl; now erewrite ?apply_r_fuse, ?apply_r_list_fuse, ?rename_fuse by eauto].
  - simpl; collapse_primes; erewrite apply_r_fuse by eauto; f_equal.
    clear v; induction l as [|[c e] ces IHces]; auto; simpl.
    now erewrite rename_fuse, IHces by eauto.
  - simpl; collapse_primes; erewrite rename_fuse by eauto; f_equal.
    clear e; induction f as [f ft xs e fds IHfds|]; auto; simpl.
    now erewrite rename_fuse, IHfds by eauto.
Qed.

Lemma disjoint_fuse x y σ :
  ~ x \in domain' σ ->
  ~ x \in image'' σ ->
  fused (M.set x y (M.empty _)) σ (M.set x y σ).
Proof.
  intros Hdom Hran; intros arb; unfold apply_r, apply_r; cbn.
  destruct (@cps.M.get cps.M.elt arb σ) as [arb'|] eqn:Harb.
  - assert (Hran' : arb' <> x). {
      intros H; subst arb'; contradiction Hran; now unfold Ensembles.In, image''. }
    assert (Hdom' : arb <> x). {
      intros H; subst arb; contradiction Hdom; now unfold Ensembles.In, domain', domain. }
    rewrite !M.gso, M.gempty; auto.
    cbn in *. now replace (M.get arb σ) with (Some arb').
  - destruct (Pos.eq_dec arb x) as [Heq|Hne].
    + subst arb; rewrite !M.gss. replace (σ ! x) with (@None cps.var) by auto. now rewrite M.gss.
    + replace (M.get arb σ) with (@None cps.var). rewrite !M.gso, M.gempty by auto.
      now replace (M.get arb σ) with (@None cps.var).
Qed.

Lemma proj_fold_preserves_fv (C : frames_t exp_univ_exp exp_univ_exp) x c ys y y' t n e :
  well_scoped (C ⟦ Eproj y t n x e ⟧) ->
  known_ctor x c ys C -> nthN ys n = Some y' ->
  occurs_free (C ⟦ rename_all_ns (M.set y y' (M.empty _)) e ⟧)
    \subset occurs_free (C ⟦ Eproj y t n x e ⟧).
Proof.
  intros Hscope Hknown Hnth; destruct Hknown as [D [E Heq]] eqn:Hknown_eq; rewrite Heq in *.
   rewrite !frames_compose_law, !framesD_cons, !app_exp_c_eq.
   apply grw_preserves_fv; constructor; cbn; repeat normalize_roundtrips.
   cbn in *; unfold cps.var, cps.M.elt in *. rewrite rename_corresp; [apply Constr_proj|].
   - (* x bound in Econstr x c ys *)
     intros Hbound; rewrite frames_compose_law with (fs := D >:: _), framesD_cons with (fs := D) in Hscope.
     rewrite app_exp_c_eq in Hscope.
     apply well_scoped_inv in Hscope; cbn in Hscope.
     destruct Hscope as [Huniq _]; cbn in Huniq; inv Huniq.
     contradiction H1; rewrite app_exp_c_eq; cbn; normalize_roundtrips.
     change (?S ?x) with (x \in S). rewrite bound_var_app_ctx; left.
     now apply bound_stem_var.
   - (* y' occurs free in (Eproj ...) *)
     intros Hbound; rewrite frames_compose_law with (fs := D >:: _), framesD_cons with (fs := D) in Hscope.
     rewrite app_exp_c_eq in Hscope.
     apply well_scoped_inv in Hscope; cbn in Hscope.
     destruct Hscope as [_ Hdis]; cbn in Hdis; normalize_bound_var_in_ctx; normalize_occurs_free_in_ctx.
     rewrite app_exp_c_eq in Hdis; cbn in Hdis; normalize_roundtrips; rewrite bound_var_app_ctx in Hdis.
     destruct Hdis as [Hdis]; contradiction (Hdis y'); split.
     + left; left; now apply bound_stem_var.
     + left. unfold Ensembles.In, FromList. eapply nthN_In; eauto.
   - change (~ y' \in bound_var e).
     rewrite <- Heq in *; clear Hknown_eq.
     eapply proj_fold_y'_unbound; eauto.
   - intros Hbound; rewrite frames_compose_law with (fs := D >:: _), framesD_cons with (fs := D) in Hscope.
     rewrite app_exp_c_eq in Hscope; apply well_scoped_inv in Hscope; cbn in Hscope.
     destruct Hscope as [_ Hdis]; cbn in Hdis; clear Hknown_eq.
     normalize_bound_var_in_ctx; normalize_occurs_free_in_ctx.
     destruct Hdis as [Hdis]; subst y'; contradiction (Hdis x); split.
     + rewrite app_exp_c_eq; cbn; normalize_roundtrips; rewrite bound_var_app_ctx; normalize_bound_var.
       now right.
     + left; unfold Ensembles.In, FromList. eapply nthN_In; eauto.
   - rewrite <- Heq in *; clear Hknown_eq.
     eapply proj_fold_y_ne_y'; eauto.
   - apply Hnth.
   - apply Disjoint_Singleton_l. eapply proj_fold_y_unbound; eauto.
Qed.

Fixpoint rename_all_preserves_bound σ e {struct e} :
  bound_var (rename_all_ns σ e) <--> bound_var e.
Proof.
  destruct e; cbn; collapse_primes; repeat normalize_bound_var;
  rewrite ?rename_all_preserves_bound; eauto with Ensembles_DB.
  - rewrite bound_var_Ecase; collapse_primes.
    induction l as [|[c e] ces IHces]; cbn; repeat normalize_bound_var; eauto with Ensembles_DB.
  - enough (Hfds : bound_var_fundefs (rename_all_fun_ns σ f) <--> bound_var_fundefs f) by now rewrite Hfds.
    clear e; induction f as [f ft xs e fds IHfds|]; cbn;
      repeat normalize_bound_var; collapse_primes; eauto with Ensembles_DB.
Qed.

Definition rw_shrink :
  rewriter exp_univ_exp true tt shrink_step _ (@D_rename) _ (@R_shrink) _ (@S_shrink).
Proof.
  mk_rw; try lazymatch goal with |- ExtraVars _ -> _ => clear | |- ConstrDelay _ -> _ => clear end.
  - (* Case folding *) intros _ R C C_ok x ces d r s success failure.
    destruct r as [ρ Hρ] eqn:Hr, d as [σ Hσ] eqn:Hd; unfold delayD, D_rename, Delayed_D_rename in *.
    pose (x0 := apply_r σ x); specialize success with (x0 := x0).
    destruct (M.get x0 ρ) as [[c ys]|] eqn:Hctor; [|cond_failure].
    specialize success with (c := c) (ys := ys).
    destruct (find_case c ces) as [e|] eqn:Hfind; [|cond_failure]; apply find_case_spec in Hfind.
    specialize success with (e := e) (e0 := @rename exp_univ_exp σ e).
    specialize success with (ces0 := @rename exp_univ_list_prod_ctor_tag_exp σ ces).
    cond_success success; unshelve eapply success.
    + exists σ; clear - Hfind Hσ; cbn in *; destruct Hσ as [Hdom Hran].
      rewrite bound_var_Ecase in *.
      assert (In (c, e) ces). { 
        destruct Hfind as [ces1 [ces2 [Hnotin Hces]]]; subst ces.
        apply in_or_app; right; now left. }
      split; (eapply Disjoint_Included_r; [eapply In_ces_bound; eauto|]; eauto).
    + unerase; split; auto.
      destruct Hfind as [ces1 [ces2 [Hnotin Hces]]].
      assert (Hfind' : In (c, e) ces) by (subst ces; apply in_or_app; right; now left).
      apply in_map with (f := @rename exp_univ_prod_ctor_tag_exp σ) in Hfind'; now cbn in Hfind'.
    + reflexivity. + reflexivity. + exact r.
    + (* Update counts *)
      destruct s as [δ Hs] eqn:Hs_eq;
      exists (census_case_pred σ c ces (census_var pred_upd σ x δ));
      unerase; split; [split|].
      * (* UB(C[σ(Ecase x ces)]) ==> UB(C[σ(e)]) because (c, e) ∈ ces *)
        destruct Hs as [[Huniq Hdisj] ?]. clear Hs_eq.
        rewrite !app_exp_c_eq in Huniq.
        rewrite (proj1 (ub_app_ctx_f _)) in Huniq.
        destruct Huniq as [HuniqC Huniqdis].
        destruct Hfind as [ces1 [ces2 [Hnotin Hces12]]].
        rewrite Hces12 in Huniqdis; cbn in Huniqdis.
        rewrite !map_app in Huniqdis; cbn in Huniqdis; collapse_primes.
        destruct Huniqdis as [Huniq Hdis].
        rewrite unique_bindings_Ecase_app in Huniq.
        destruct Huniq as [_ [Huniq Hdis']].
        inv Huniq.
        rewrite app_exp_c_eq, (proj1 (ub_app_ctx_f _)).
        split; [|split]; auto.
        rewrite bound_var_Ecase_app, bound_var_Ecase_cons in Hdis.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis]]; eauto with Ensembles_DB.
      * (* BV(C[σ(e)]) ⊆ BV(C[σ(Ecase x ces)]) and ditto for FV
            And already have BV(C[σ(Ecase x es)]) # FV(C[σ(Ecase x ces)]) *)
        destruct Hfind as [ces1 [ces2 [Hnotin Heq]]].
        destruct Hs as [[Huniq Hdis] ?]; eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis]].
        -- rewrite !app_exp_c_eq, !bound_var_app_ctx; cbn.
           subst ces; rewrite !map_app; cbn; collapse_primes.
           rewrite bound_var_Ecase_app, bound_var_Ecase_cons; eauto with Ensembles_DB.
        -- rewrite !app_exp_c_eq. apply occurs_free_exp_ctx; cbn.
           subst ces; rewrite !map_app; cbn; collapse_primes.
           rewrite occurs_free_Ecase_app; eauto with Ensembles_DB.
      * intros arb; rewrite count_ctx_app; unfold count, rename.
        destruct Hfind as [ces1 [ces2 [Hnotin Hces]]].
        eapply census_case_pred_spec; eauto.
        rewrite census_var_pred_corresp.
        destruct Hs as [[Huniq Hdis] Hδ]; rewrite Hδ, count_ctx_app; cbn; collapse_primes; lia.
  - (* Projection folding *) intros _ R C C_ok e y t n x d r s success failure.
    destruct r as [ρ Hρ] eqn:Hr, d as [σ Hσ] eqn:Hd; unfold delayD, D_rename, Delayed_D_rename in *.
    clearpose Hx0 x0 (apply_r σ x); specialize success with (x0 := x0).
    destruct (M.get x0 ρ) as [[c ys]|] eqn:Hctor; [|cond_failure].
    specialize success with (c := c) (ys := ys).
    destruct (nthN ys n) as [y'|] eqn:Hy'; [|cond_failure].
    specialize success with (y0 := y) (t0 := t) (n0 := n) (y' := y').
    specialize success with (e0 := @rename exp_univ_exp σ e).
    cond_success success; unshelve eapply success.
    + exists (M.set y y' σ); cbn in *; destruct Hσ as [Hdom Hran].
      clear Hd; repeat normalize_bound_var_in_ctx.
      apply Disjoint_Union in Hdom; apply Disjoint_Union in Hran.
      destruct Hdom as [Hdom_e Hdomy], Hran as [Hran_e Hrany].
      split.
      * eapply Disjoint_Included_l; [apply domain'_set|]; apply Union_Disjoint_l; [|auto].
        apply Disjoint_Singleton_l.
        rewrite <- rename_all_preserves_bound with (σ := σ).
        destruct s as [s Hs]; unerase; destruct Hs as [HWS ?].
        rewrite app_exp_c_eq in HWS; apply well_scoped_inv in HWS.
        destruct HWS as [Huniq _]; clear - Huniq; cbn in Huniq.
        now inv Huniq.
      * eapply Disjoint_Included_l; [apply image''_set|]; apply Union_Disjoint_l; [|auto].
        apply Disjoint_Singleton_l.
        rewrite <- rename_all_preserves_bound with (σ := σ).
        destruct s as [s Hs]; unerase; destruct Hs as [HWS ?].
        inv Hx0. eapply proj_fold_y'_unbound; eauto.
    + unerase; split; auto; apply in_map with (f := @rename exp_univ_prod_ctor_tag_exp σ) in Hfind; now cbn in Hfind.
    + subst x0; reflexivity.
    + (* y ∉ dom σ ∪ ran σ because y ∈ BV(Eproj y t n x e).
         So (y ↦ y') ∘ σ = σ[y ↦ y'] *) cbn.
      assert (~ y \in domain' σ). {
        clear - Hσ; destruct Hσ as [[Hσ] _]; cbn in *; repeat normalize_bound_var_in_ctx.
        intros Hin; contradiction (Hσ y); constructor; auto. }
      assert (~ y \in image'' σ). {
        clear - Hσ; destruct Hσ as [_ [Hσ]]; cbn in *; repeat normalize_bound_var_in_ctx.
        intros Hin; contradiction (Hσ y); constructor; auto. }
      apply rename_fuse, disjoint_fuse; auto.
    + exact r.
    + (* Update counts *)
      destruct s as [δ Hs] eqn:Hs_eq;
      exists (census_var_pred σ x (census_subst y' y δ)).
      unerase; split; [split|].
      * (* UB(C[(σe)[y'/y]])
              ⟸ UB(C[σe]) (BV((σe)[y'/y]) = BV(σe) by rename_all_preserves_bound)
              ⟸ UB(C[Eproj y t n (σx) (σe)])
              ⟸ UB(C[σ(Eproj y t n x e)]) *)
        destruct Hs as [[Huniq Hdis] ?]; clear Hs_eq.
        rewrite !app_exp_c_eq, (proj1 (ub_app_ctx_f _)) in Huniq.
        destruct Huniq as [HuniqC [Huniq Hdis']].
        rewrite !app_exp_c_eq, (proj1 (ub_app_ctx_f _)).
        split; [|split]; auto.
        -- apply unique_bindings_rename_all_ns.
           cbn in *; now inv Huniq.
        -- unfold Rec; rewrite rename_all_preserves_bound.
           eapply Disjoint_Included_r; [|apply Hdis'].
           cbn; normalize_bound_var; eauto with Ensembles_DB.
      * destruct Hs as [HWS ?].
        pose (HWS' := HWS); clearbody HWS'; destruct HWS as [Huniq Hdis].
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis]].
        -- unfold Rec; rewrite !app_exp_c_eq, !bound_var_app_ctx, rename_all_preserves_bound.
           cbn; normalize_bound_var; eauto with Ensembles_DB.
        -- unfold Rec, rename; cbn; collapse_primes.
           subst x0; apply proj_fold_preserves_fv with (c := c) (ys := ys); auto.
      * intros arb; rewrite count_ctx_app, census_var_pred_corresp.
        pose (Hρ' := Hρ x0 c ys Hctor).
        assert (Hneq : y <> y'). {
          subst x0; eapply proj_fold_y_ne_y'; try (exact Hρ' || exact Hy').
          clear Hs_eq; destruct Hs as [HWS _]; cbn in HWS; apply HWS. }
        assert (Hy_notin_C : count_ctx y C = 0). {
          assert (Hy : ~ y \in used_c C). {
            clear Hs_eq; destruct Hs as [HWS ?].
            rewrite app_exp_c_eq in HWS.
            eapply (proj1 well_scoped_mut') in HWS.
            destruct HWS as [[Hdis] ?]; intros Hyin; contradiction (Hdis y).
            constructor; [|rewrite isoABA; auto].
            cbn; normalize_bound_var; now right. }
          now apply used_c_count_zero' with (n := frames_len C) (C := C) in Hy. }
        unfold count, Rec, rename.
        destruct Hs as [HWS Hδ].
        destruct (var_eq_dec arb y); [|destruct (var_eq_dec arb y')].
        -- subst arb; rewrite census_subst_dom, count_exp_subst_dom, Hy_notin_C by auto; lia.
        -- subst arb; rewrite census_subst_ran, count_exp_subst_ran by auto.
           rewrite !Hδ, !count_ctx_app, Hy_notin_C; cbn; collapse_primes.
           assert (Hyx : y <> apply_r σ x). {
             assert (HWS' : well_scoped (rename_all_ns σ (Eproj y t n x e))). {
               clear Hs_eq; rewrite app_exp_c_eq in HWS.
               now apply well_scoped_inv in HWS. }
             intros Heqy; destruct HWS' as [? [Hdis]]; contradiction (Hdis y).
             cbn; normalize_bound_var; normalize_occurs_free.
             constructor; [now right|].
             unfold apply_r in Heqy; cbn in Heqy; inv Heqy; now left. }
           rewrite count_var_neq at 1 by auto; lia.
        -- rewrite census_subst_neither, count_exp_subst_neither, Hδ, count_ctx_app by auto.
           cbn; collapse_primes; lia.
  - (* Top down dead constr *) intros _ R C C_ok e x c ys d r s success failure.
    destruct s as [δ Hδ] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (c0 := c) (ys0 := apply_r_list σ ys).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    Ltac solve_σ_bvs Hσ Hd := 
      clear Hd; cbn in Hσ; normalize_bound_var_in_ctx;
      destruct Hσ as [Hdom Hran];
      repeat match goal with H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H end;
      auto.
    Ltac solve_count Hδ Hs Hcount :=
      clear Hs; match goal with
      | |- count_exp ?x _ = 0 =>
        unfold S_shrink in *; unerase; destruct Hδ as [HWS Hδ];
        specialize (Hδ x); rewrite count_ctx_app in Hδ; unfold get_count in Hδ; rewrite Hcount in Hδ; cbn in Hδ;
        unfold rename; lia
      end.
    + exists σ. (* Follows from BV(e) ⊆ BV(Econstr x c ys e) *) solve_σ_bvs Hσ Hd.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + reflexivity. + reflexivity. + exact r.
    + (* Upate counts *)
      exists (census_vars_pred σ ys δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      Ltac solve_uniq Hs WS :=
        clear Hs; destruct WS as [Huniq _]; rewrite app_exp_c_eq in Huniq|-*;
        rewrite (proj1 (ub_app_ctx_f _)); cbn in Huniq; collapse_primes;
        rewrite (proj1 (ub_app_ctx_f _)) in Huniq; destruct Huniq as [HuniqC [HuniqE Hdis]];
        unfold Rec; split; [|split]; auto;
        [cbn; now inv HuniqE
        |DisInc Hdis; eauto with Ensembles_DB; cbn; normalize_bound_var; eauto with Ensembles_DB].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      Ltac solve_dead_disj Hs WS Hδ Hcount x σ e :=
        clear Hs; destruct WS as [_ Hdis];
        let Hnotin := fresh "Hnotin" in
        let Hcountzero := fresh "Hcountzero" in
        assert (Hnotin : ~ x \in occurs_free (rename_all_ns σ e)) by
          (assert (Hcountzero : count_exp x (rename_all_ns σ e) = 0) by
            (specialize (Hδ x); unfold get_count in Hδ; rewrite Hcount, count_ctx_app in Hδ; cbn in Hδ; lia);
            now apply count_dead_exp);
        DisInc Hdis;
        [rewrite !app_exp_c_eq, !bound_var_app_ctx; cbn; normalize_bound_var;
         eauto with Ensembles_DB
        |rewrite !app_exp_c_eq; apply occurs_free_exp_ctx; cbn in *;
         normalize_occurs_free; eapply Included_trans;
          [apply Included_Setminus; [apply Disjoint_Singleton_r, Hnotin|apply Included_refl]|];
          eauto with Ensembles_DB].
      * (* BV(C[σe]) ⊆ BV(C[σ(Econstr x c ys e)])
           FV(C[σe]) ⊆ FV(C[σ(Econstr x c ys e)]) because x is dead *)
        solve_dead_disj Hs WS Hδ Hcount x σ e.
      * unfold Rec; intros arb; rewrite census_vars_pred_corresp, Hδ, !count_ctx_app; cbn; lia.
  - (* Bottom up dead constr *) intros _ R C C_ok x c ys e r s success failure.
    destruct s as [δ Hδ] eqn:Hs; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + exact r.
    + (* Update counts *)
      exists (census_vars_pred (M.empty _) ys δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      Ltac solve_dead_disj_bu Hs WS Hδ Hcount x e :=
        clear Hs; destruct WS as [_ Hdis];
        let Hnotin := fresh "Hnotin" in
        let Hcountzero := fresh "Hcountzero" in
        assert (Hnotin : ~ x \in occurs_free e) by
          (assert (Hcountzero : count_exp x e = 0) by
            (specialize (Hδ x); unfold get_count in Hδ; rewrite Hcount, count_ctx_app in Hδ; cbn in Hδ; lia);
            now apply count_dead_exp);
        DisInc Hdis;
        [rewrite !app_exp_c_eq, !bound_var_app_ctx; cbn; normalize_bound_var;
         eauto with Ensembles_DB
        |rewrite !app_exp_c_eq; apply occurs_free_exp_ctx; cbn in *;
         normalize_occurs_free; eapply Included_trans;
          [apply Included_Setminus; [apply Disjoint_Singleton_r, Hnotin|apply Included_refl]|];
          eauto with Ensembles_DB].
      * (* BV(C[e]) ⊆ BV(C[Econstr x c ys e])
           FV(C[e]) ⊆ FV(C[Econstr x c ys e]) because x dead *)
        solve_dead_disj_bu Hs WS Hδ Hcount x e.
      * unfold Rec; intros arb; rewrite census_vars_pred_corresp, apply_r_list_id, Hδ, !count_ctx_app; cbn; lia.
  - (* Top down dead proj *) intros _ R C C_ok e x t n y d r s success failure.
    destruct s as [δ Hδ] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (t0 := t) (n0 := n) (y0 := apply_r σ y).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(e) ⊆ BV(Eproj x c ys e) *) solve_σ_bvs Hσ Hd.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + reflexivity. + reflexivity. + exact r.
    + (* Update counts *)
      exists (census_var_pred σ y δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      * (* BV(C[σe]) ⊆ BV(C[σ(Eproj x t n y e)])
           FV(C[σe]) = FV(C[σe]) \\ {x} (because x is dead)
                     ⊆ FV(C[σ(Eproj x t n y e)]) *)
        solve_dead_disj Hs WS Hδ Hcount x σ e.
      * unfold Rec; intros arb; rewrite census_var_pred_corresp, Hδ, !count_ctx_app; cbn; lia.
  - (* Bottom up dead proj *) intros _ R C C_ok x t n y e r s success failure.
    destruct s as [δ Hδ] eqn:Hs; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + exact r.
    + (* Update counts *)
      exists (census_var_pred (M.empty _) y δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      * (* BV(C[e]) ⊆ BV(C[Eproj x t n y e])
           FV(C[e]) ⊆ FV(C[Eproj x t n y e]) because x dead *)
        solve_dead_disj_bu Hs WS Hδ Hcount x e.
      * unfold Rec; intros arb; rewrite census_var_pred_corresp, apply_r_id, Hδ, !count_ctx_app; cbn; lia.
  - (* Top down dead prim *) intros _ R C C_ok e x p ys d r s success failure.
    destruct s as [δ Hδ] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (p0 := p) (ys0 := apply_r_list σ ys).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(e) ⊆ BV(Eprim x p ys e) *) solve_σ_bvs Hσ Hd.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + reflexivity. + reflexivity. + exact r.
    + (* Update counts *)
      exists (census_vars_pred σ ys δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      * (* BV(C[σe]) ⊆ BV(C[σ(Eprim x p ys e)])
           FV(C[σe]) = FV(C[σe]) \\ {x} (because x is dead)
                     ⊆ FV(C[σ(Eprim x p ys e)]) *)
        solve_dead_disj Hs WS Hδ Hcount x σ e.
      * unfold Rec; intros arb; rewrite census_vars_pred_corresp, Hδ, !count_ctx_app; cbn; lia.
  - (* Bottom up dead prim *) intros _ R C C_ok x p ys e r s success failure.
    destruct s as [δ Hδ] eqn:Hs; unfold delayD, Delayed_D_rename, D_rename in *.
    destruct (M.get x δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) solve_count Hδ Hs Hcount.
    + exact r.
    + (* Update counts *)
      exists (census_vars_pred (M.empty _) ys δ); unerase; unfold S_shrink in *; destruct Hδ as [WS Hδ]; split; [split|].
      * (* Follows from Huniq *) solve_uniq Hs WS.
      * (* BV(C[e]) ⊆ BV(C[Eprim x p ys e])
           FV(C[e]) ⊆ FV(C[Eprim x p ys e]) because x dead *)
        solve_dead_disj_bu Hs WS Hδ Hcount x e.
      * unfold Rec; intros arb; rewrite census_vars_pred_corresp, apply_r_list_id, Hδ, !count_ctx_app; cbn; lia.
  Ltac unfold_delayD := unfold delayD, Delayed_D_rename, D_rename in *.
  Ltac solve_delayD :=
    cbn in *; repeat normalize_bound_var_in_ctx;
    eauto with Ensembles_DB.
  - (* Rename a pair *) intros _ R c e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k c); [exists σ; split; auto|]; reflexivity.
  - (* Rename empty list *) intros _ R [σ ?] k; cbn in *; exact (k eq_refl).
  - (* Rename cons case arms *) intros _ R [c e] ces [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply k; [exists σ; split|exists σ; split|]; [solve_delayD..|reflexivity].
  - (* Rename cons function definitions *) intros _ R f ft xs e fds [σ [Hdom Hran]] k.
    unshelve eapply (k f ft xs); [exists σ; split|exists σ; split|]; [..|reflexivity];
      cbn in *; repeat normalize_bound_var_in_ctx;
      (eapply Disjoint_Included_r; [|eassumption]; eauto with Ensembles_DB).
  - (* Rename Fnil *) intros _ R [σ [Hdom Hran]] k; apply k; reflexivity.
  - (* Rename constr binding *) intros _ R x c ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x c (apply_r_list σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename case expression *) intros _ R x ces [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k (apply_r σ x)); [exists σ|]; [..|reflexivity].
    cbn in *; rewrite !bound_var_Ecase in *; now split.
  - (* Rename proj binding *) intros _ R x t n y e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x t n (apply_r σ y)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename letapp *) intros _ R x f ft ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x (apply_r σ f) ft (apply_r_list σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename bundle definition *) intros _ R fds e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply k; [exists σ|exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename cps app *) intros _ R f ft ys [σ [Hdom Hran]] k; unfold_delayD.
    now apply (k (apply_r σ f) ft (apply_r_list σ ys)).
  - (* Rename prim binding *) intros _ R x p ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x p (apply_r_list σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename halt *) intros _ R x [σ [Hdom Hran]] k; unfold_delayD; exact (k (apply_r σ x) eq_refl).
Defined.
