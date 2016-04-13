Require Import Arith BinNat List Omega.
Require Import cps.

Import ListNotations.

Inductive exp_ctx : Type :=
| Hole_c : exp_ctx
| Econstr_c : var -> type -> tag -> list var -> exp_ctx -> exp_ctx
| Eproj_c  : var -> type -> N -> var -> exp_ctx -> exp_ctx
| Eprim_c : var -> type -> prim -> list var -> exp_ctx -> exp_ctx
| Ecase_c : var -> list (tag * exp) -> tag ->
            exp_ctx -> list (tag * exp) -> exp_ctx  
| Efun1_c : fundefs -> exp_ctx -> exp_ctx
| Efun2_c : fundefs_ctx -> exp -> exp_ctx
with fundefs_ctx :=
     | Fcons1_c:  var -> type -> list var -> exp_ctx -> fundefs -> fundefs_ctx
     | Fcons2_c:  var -> type -> list var -> exp -> fundefs_ctx -> fundefs_ctx.

Inductive app_ctx: exp_ctx -> exp -> exp -> Prop :=
| Hole_ac: forall e, app_ctx Hole_c e e
| Constr_ac : forall x t k c ys e ce,
                app_ctx c e ce ->        
                app_ctx (Econstr_c x t k ys c) e (Econstr x t k ys ce)
| Proj_ac : forall x t n y e c ce, 
              app_ctx c e ce ->        
              app_ctx (Eproj_c x t n y c) e (Eproj x t n y ce)
| Case_ac : forall x te t e te' c ce,
              app_ctx c e ce ->
              app_ctx (Ecase_c x te t c te') e
                      (Ecase x (te ++ (t, ce) :: te')) 
| Prim_ac : forall x t f ys e c ce, 
              app_ctx c e ce ->        
              app_ctx (Eprim_c x t f ys c) e (Eprim x t f ys ce)
| Fun1_ac : forall c e ce fds,
              app_ctx c e ce ->
              app_ctx (Efun1_c fds c) e (Efun fds ce)
| Fun2_ac : forall e cfds cfdse e',
              app_f_ctx cfds e cfdse ->          
              app_ctx (Efun2_c cfds e') e (Efun cfdse e')
with app_f_ctx : fundefs_ctx -> exp -> fundefs -> Prop :=
     | Fcons1_ac : forall c e ce f t ys fds,
                     app_ctx c e ce -> 
                     app_f_ctx (Fcons1_c f t ys c fds) e (Fcons f t ys ce fds)
     | Fcons2_ac: forall e cfdse f cfds ys e' t, 
                    app_f_ctx cfds e cfdse -> 
                    app_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons f t ys e' cfdse).

Hint Constructors app_ctx app_f_ctx.

Fixpoint app_ctx_f (c:exp_ctx) (e:exp) : exp :=
  match c with
    | Hole_c => e
    | Econstr_c x t k ys c => Econstr x t k ys (app_ctx_f c e)
    | Eproj_c x t n y c => Eproj x t n y (app_ctx_f c e)
    | Ecase_c x te t c te' =>
      Ecase x (te ++ (t, app_ctx_f c e) :: te')
    | Eprim_c x t f ys c => Eprim x t f ys (app_ctx_f c e)
    | Efun1_c fds c => Efun fds (app_ctx_f c e)
    | Efun2_c cfds e' => Efun (app_f_ctx_f cfds e) e' 
  end
with app_f_ctx_f (c: fundefs_ctx) (e:exp) : fundefs :=
       match c with
         | Fcons1_c f t ys c fds => Fcons f t ys (app_ctx_f c e) fds
         | Fcons2_c f t ys e' cfds => Fcons f t ys e' (app_f_ctx_f cfds e)
       end.

Inductive  comp_ctx: exp_ctx -> exp_ctx -> exp_ctx -> Prop :=
| Hole_cc: forall e, comp_ctx Hole_c e e
| Constr_cc : forall x t k c ys e ce,
                comp_ctx c e ce ->
                comp_ctx (Econstr_c x t k ys c) e (Econstr_c x t k ys ce)
| Proj_cc : forall x t n y e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eproj_c x t n y c) e (Eproj_c x t n y ce)
| Case_cc : forall x te t c te' c' cc,
              comp_ctx c c' cc ->
              comp_ctx (Ecase_c x te t c te') c' (Ecase_c x te t cc te')
| Prim_cc : forall x t f ys e c ce,
              comp_ctx c e ce ->
              comp_ctx (Eprim_c x t f ys c) e (Eprim_c x t f ys ce)
| Fun1_cc : forall c e ce fds,
              comp_ctx c e ce ->
              comp_ctx (Efun1_c fds c) e (Efun1_c fds ce)
| Fun2_cc : forall e cfds cfdse e',
              comp_f_ctx cfds e cfdse ->
              comp_ctx (Efun2_c cfds e') e (Efun2_c cfdse e')
with comp_f_ctx : fundefs_ctx -> exp_ctx -> fundefs_ctx -> Prop :=
     | Fcons1_cc :
         forall c e ce f t ys fds,
           comp_ctx c e ce ->
           comp_f_ctx (Fcons1_c f t ys c fds) e (Fcons1_c f t ys ce fds)
     | Fcons2_cc:
         forall e cfdse f cfds ys e' t,
           comp_f_ctx cfds e cfdse ->
           comp_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons2_c f t ys e' cfdse).

Fixpoint comp_ctx_f (c1:exp_ctx) (c2:exp_ctx) : exp_ctx :=
  match c1 with
    | Hole_c => c2
    | Econstr_c x t k ys c => Econstr_c x t k ys (comp_ctx_f c c2)
    | Eproj_c x t n y c => Eproj_c x t n y (comp_ctx_f c c2)
    | Ecase_c x te t c te' => Ecase_c x te t (comp_ctx_f c c2) te'
    | Eprim_c x t f ys c => Eprim_c x t f ys (comp_ctx_f c c2)
    | Efun1_c fds c => Efun1_c fds (comp_ctx_f c c2)
    | Efun2_c cfds e' => Efun2_c (comp_f_ctx_f cfds c2) e'
  end
with comp_f_ctx_f (c: fundefs_ctx) (c2:exp_ctx) : fundefs_ctx :=
       match c with
         | Fcons1_c f t ys c fds =>
           Fcons1_c f t ys (comp_ctx_f c c2) fds
         | Fcons2_c f t ys e' cfds =>
           Fcons2_c f t ys e' (comp_f_ctx_f cfds c2)
       end.

Notation "c '|[' e ']|' " := (app_ctx_f c e)  (at level 28, no associativity)
                             : ctx_scope.
Notation "f '<[' e ']>'" := (app_f_ctx_f f e)  (at level 28, no associativity)
                            : ctx_scope.

Scheme ctx_exp_mut := Induction for exp_ctx Sort Prop
                      with ctx_fundefs_mut := Induction for fundefs_ctx Sort Prop.

Lemma exp_fundefs_ctx_mutual_ind :
  forall (P : exp_ctx -> Prop) (P0 : fundefs_ctx -> Prop),
    P Hole_c ->
    (forall (v : var) (t : type) (t0 : tag) (l : list var) (e : exp_ctx),
       P e -> P (Econstr_c v t t0 l e)) ->
    (forall (v : var) (t : type) (n : N) (v0 : var) (e : exp_ctx),
       P e -> P (Eproj_c v t n v0 e)) ->
    (forall (v : var) (t : type) (p : prim) (l : list var) (e : exp_ctx),
       P e -> P (Eprim_c v t p l e)) ->
    (forall (v : var) (l : list (tag * exp)) (t : tag) (e : exp_ctx),
       P e -> forall l0 : list (tag * exp), P (Ecase_c v l t e l0)) ->
    (forall (f4 : fundefs) (e : exp_ctx), P e -> P (Efun1_c f4 e)) ->
    (forall f5 : fundefs_ctx, P0 f5 -> forall e : exp, P (Efun2_c f5 e)) ->
    (forall (v : var) (t : type) (l : list var) (e : exp_ctx),
       P e -> forall f6 : fundefs, P0 (Fcons1_c v t l e f6)) ->
    (forall (v : var) (t : type) (l : list var) 
            (e : exp) (f7 : fundefs_ctx), P0 f7 -> P0 (Fcons2_c v t l e f7)) ->
    (forall e : exp_ctx, P e) /\ (forall f : fundefs_ctx, P0 f).
Proof.
  intros. split.
  apply (ctx_exp_mut P P0); assumption.
  apply (ctx_fundefs_mut P P0); assumption.
Qed.

(** name the induction hypotheses only *)
Ltac exp_fundefs_ctx_induction IH1 IH2 :=
  apply exp_fundefs_ctx_mutual_ind;
  [ | intros ? ? ? ? ? IH1 
    | intros ? ? ? ? ? IH1
    | intros ? ? ? ? ? IH1
    | intros ? ? ? ? IH1
    | intros ? ? IH1
    | intros ? IH2 ?
    | intros ? ? ? ? IH1 ?
    | intros ? ? ? ? ? IH2 ].

(** alternative definition of subterms relation in function of 
    applicative contexts *)
Definition subterm_e' (e':exp) (e:exp): Prop :=
  exists c, Hole_c <> c /\ app_ctx c e' e.

Definition subterm_or_eq' (e':exp) (e:exp) : Prop :=
  exists c, app_ctx c e' e.

(** theorems about app and comp *)
Lemma app_ctx_f_correct:
  forall c e e',
    app_ctx_f c e  = e' <-> app_ctx c e e'
    with app_f_ctx_f_correct:
           forall cf e e',
             app_f_ctx_f cf e = e' <-> app_f_ctx cf e e'.
Admitted.

Lemma comp_ctx_f_correct:
  forall c c' cc',
    comp_ctx_f c c'  = cc' <-> comp_ctx c c' cc'
    with comp_f_ctx_f_correct:
           forall cf cf' ccf',
             comp_f_ctx_f cf cf' = ccf' <-> comp_f_ctx cf cf' ccf'.
Admitted.

Lemma app_ctx_f_fuse :
  forall c c' e,
    app_ctx_f c (app_ctx_f c' e) = app_ctx_f (comp_ctx_f c c') e.
Admitted. 

Lemma app_ctx_fuse:
  forall (c c' : exp_ctx) (e1 e2 e3 : exp),
    app_ctx c e1 e2 ->
    app_ctx c' e2 e3 ->
    app_ctx (comp_ctx_f c' c) e1 e3.
Proof.
  intros c c' e1 e2 e3 H1 H2. rewrite <- app_ctx_f_correct.
  rewrite <- app_ctx_f_fuse.
  rewrite <- app_ctx_f_correct in H1, H2. rewrite H1. eauto.
Qed.
