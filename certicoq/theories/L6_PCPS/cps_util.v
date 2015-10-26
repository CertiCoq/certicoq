Require Maps.
Import Nnat.
Require Import Arith BinNat String List Omega Program Psatz.
Require Import CpdtTactics.
Require Import cps.

(* useful definitions and proof for L6 - cps language *)
(* 
 SUBTERM - proper subterm relation

 CTX     - applicative contexts 

 OCCUR   - number of occurence of variables

 BINDING - list of variable binding, unique binding property
 
 OTHER  - unclassified fact about cps/cps.v

 *)

 Ltac destructAll :=
   match goal with
     | [ H : _ /\ _ |- _] => destruct H; destructAll
     | [ H : exists E, _ |- _ ] => destruct H; destructAll
     | _ => subst
   end.


Definition var_dec := M.elt_eq.

Section SUBTERM.



  Inductive subterm_e: exp -> exp -> Prop :=
    (* immediate *)
    | subterm_constr: forall x t c ys e,  subterm_e e (Econstr x t c ys e)
    | subterm_proj: forall v t n y e, subterm_e e (Eproj v t n y e)
    | subterm_prim: forall x t f ys e, subterm_e e (Eprim x t f ys e)
    (* remote *)
    | subterm_constr': forall x t c ys e e', subterm_e e' e -> subterm_e e' (Econstr x t c ys e)
    | subterm_proj': forall v t n y e e', subterm_e e' e -> subterm_e e' (Eproj v t n y e)
    | subterm_prim': forall x t f ys e e', subterm_e e' e -> subterm_e e' (Eprim x t f ys e)
  (* in fdefs *)
    | subterm_fds: forall e' fds e,
        subterm_fds_e e' fds ->
        subterm_e e' (Efun fds e)
  with subterm_fds_e: exp -> fundefs -> Prop :=
       | subterm_cons: forall e f t ys fds', subterm_fds_e e (Fcons f t ys e fds')
       | subterm_cons': forall e' e f t ys fds', subterm_e e' e -> subterm_fds_e e' (Fcons f t ys e fds')
       | subterm_cons_fds: forall e' fds' f t ys e , subterm_fds_e e' fds' -> subterm_fds_e e' (Fcons f t ys e fds').


  Inductive subfds_fds: fundefs -> fundefs -> Prop :=
  | subfds_cons': forall fds' fds f t ys e,  subfds_fds fds' fds -> subfds_fds fds' (Fcons f t ys e fds)
  | subfds_cons: forall fds f t ys e, subfds_fds fds (Fcons f t ys e fds).


Definition subterm_or_eq: exp -> exp -> Prop :=
   fun e' e => subterm_e e' e \/ e' = e.

Definition subfds_or_eq: fundefs -> fundefs -> Prop :=
  fun fds' fds => subfds_fds fds' fds \/ fds' = fds.

Definition subfds_e: fundefs -> exp -> Prop := 
    fun fds  e => exists fds' e', subterm_or_eq (Efun fds' e') e /\  subfds_or_eq fds fds'.

Definition subfds_or_eq_left: forall fds' fds fds'', subfds_fds fds fds' -> subfds_or_eq fds' fds'' -> subfds_or_eq fds fds''.
Proof.
  induction fds'; intros.
  - inversion H; subst. eapply IHfds'. apply H3. admit. admit.
Admitted.  

Theorem subfds_e_subfds: forall fds e fds', subfds_fds fds' fds -> subfds_e fds e -> subfds_e fds' e.
Proof.
  destruct fds; intros.
  - destruct H0; destructAll. exists x x0. split. assumption.  eapply subfds_or_eq_left. apply H. assumption.
  - inversion H. 
Qed.

End SUBTERM.

Section CTX.

  Inductive exp_ctx : Type :=
  | Hole_c : exp_ctx (* [] *)
  | Econstr_c : var -> type -> tag -> list var -> exp_ctx -> exp_ctx
  | Eproj_c  : var -> type -> N -> var -> exp_ctx -> exp_ctx
  | Eprim_c : var -> type -> prim -> list var -> exp_ctx -> exp_ctx
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
           app_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons f t ys e' cfdse)
  .
  
  Hint Constructors app_ctx app_f_ctx.
  
  Fixpoint app_ctx_f (c:exp_ctx) (e:exp): exp :=
    match c with
      | Hole_c => e
      | Econstr_c x t k ys c => Econstr x t k ys (app_ctx_f c e)
      | Eproj_c x t n y c => Eproj x t n y (app_ctx_f c e)
      | Eprim_c x t f ys c => Eprim x t f ys (app_ctx_f c e)
      | Efun1_c fds c => Efun fds (app_ctx_f c e)
      | Efun2_c cfds e' => Efun (app_f_ctx_f cfds e) e' 
    end
  with app_f_ctx_f (c: fundefs_ctx) (e:exp) : fundefs :=
         match c with
           | Fcons1_c f t ys c fds => Fcons f t ys (app_ctx_f c e) fds
           | Fcons2_c f t ys e' cfds => Fcons f t ys e' (app_f_ctx_f cfds e)
         end
  .
  
Inductive  comp_ctx: exp_ctx -> exp_ctx -> exp_ctx -> Prop :=
  | Hole_cc: forall e, comp_ctx Hole_c e e
  | Constr_cc : forall x t k c ys e ce,
           comp_ctx c e ce ->        
           comp_ctx (Econstr_c x t k ys c) e (Econstr_c x t k ys ce)
  | Proj_cc : forall x t n y e c ce, 
           comp_ctx c e ce ->        
           comp_ctx (Eproj_c x t n y c) e (Eproj_c x t n y ce)
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
       | Fcons1_cc : forall c e ce f t ys fds,
           comp_ctx c e ce -> 
           comp_f_ctx (Fcons1_c f t ys c fds) e (Fcons1_c f t ys ce fds)
       | Fcons2_cc: forall e cfdse f cfds ys e' t, 
           comp_f_ctx cfds e cfdse -> 
           comp_f_ctx (Fcons2_c f t ys e' cfds) e (Fcons2_c f t ys e' cfdse)
  .

    
  
    Fixpoint comp_ctx_f (c1:exp_ctx) (c2:exp_ctx): exp_ctx :=
        match c1 with
      | Hole_c => c2
      | Econstr_c x t k ys c => Econstr_c x t k ys (comp_ctx_f c c2)
      | Eproj_c x t n y c => Eproj_c x t n y (comp_ctx_f c c2)
      | Eprim_c x t f ys c => Eprim_c x t f ys (comp_ctx_f c c2)
      | Efun1_c fds c => Efun1_c fds (comp_ctx_f c c2)
      | Efun2_c cfds e' => Efun2_c (comp_f_ctx_f cfds c2) e' 
    end
  with comp_f_ctx_f (c: fundefs_ctx) (c2:exp_ctx) : fundefs_ctx :=
         match c with
           | Fcons1_c f t ys c fds => Fcons1_c f t ys (comp_ctx_f c c2) fds
           | Fcons2_c f t ys e' cfds => Fcons2_c f t ys e' (comp_f_ctx_f cfds c2)
         end.

  (* alternative definition of subterms relation in function of applicative contexts *)
  Definition subterm_e' (e':exp) (e:exp): Prop :=
    exists c, Hole_c <> c /\ app_ctx c e' e.

  
  Definition subterm_or_eq' (e':exp) (e:exp) : Prop :=
    exists c, app_ctx c e' e.


(* theorems about app and comp *)
    Theorem app_ctx_f_correct: forall c e e',
                               app_ctx_f c e  = e' <-> app_ctx c e e'
                               with app_f_ctx_f_correct: forall cf e e',
                                                           app_f_ctx_f cf e = e' <-> app_f_ctx cf e e'.
      Admitted.

    Theorem comp_ctx_f_correct: forall c c' cc',
                                 comp_ctx_f c c'  = cc' <-> comp_ctx c c' cc'
                                 with comp_f_ctx_f_correct: forall cf cf' ccf',
                                                             comp_f_ctx_f cf cf' = ccf' <-> comp_f_ctx cf cf' ccf'.
    Admitted.

    Theorem app_ctx_f_fuse : forall c c' e,
                               app_ctx_f c (app_ctx_f c' e) = app_ctx_f (comp_ctx_f c c') e.
      Admitted.

    
    


End CTX.  

Section OCCUR.

  Definition num_occur_list (lv:list var) (v:var) : nat :=
    fold_right (fun v' n => if (var_dec v v') then 1 + n
                            else n) 0 lv.
                                                       
    
  
  (* number of time var occurs in exp (free or not) *)
  Inductive num_occur: exp -> var -> nat -> Prop :=
  | Num_occ_constr: forall x t c ys e v n, num_occur e v n -> num_occur (Econstr x t c ys e) v (n + (num_occur_list ys v))
  | Num_occ_prim: forall x t f ys e v n, num_occur e v n -> num_occur (Eprim x t f ys e) v (n + (num_occur_list ys v))
  | Num_occ_case: forall v' cl v,
      num_occur (Ecase v' cl) v (num_occur_list (v'::(snd (split cl))) v)
  | Num_occ_proj: forall e v n  y v' t n',
      num_occur  e v n -> 
      num_occur (Eproj v' t n' y e) v (num_occur_list [y] v + n)
  | Num_occ_app: forall f ys v,
      num_occur (Eapp f ys) v (num_occur_list (f::ys) v)
  | Num_occ_fun: forall e v n m fl,
      num_occur e v n ->
      num_occur_fds fl v m ->
      num_occur (Efun fl e) v (n + m )
  with num_occur_fds: fundefs -> var -> nat -> Prop :=
       | Num_occ_nil : forall v,
           num_occur_fds Fnil v 0
       | Num_occ_cons : forall v t n v' ys e fds' m,
                               num_occur e v n ->
                               num_occur_fds fds' v m ->
           num_occur_fds (Fcons v' t ys e fds') v (n + m).


  (* number of time var occurs in a context *)
  Inductive num_occur_ec: exp_ctx -> var -> nat -> Prop :=
  | Noec_hole: forall v, num_occur_ec Hole_c v 0
  | Noec_constr: forall c v n x t ys g,
    num_occur_ec c v n -> 
    num_occur_ec (Econstr_c x t g ys c) v (num_occur_list ys v + n)
  | Noec_prim: forall c v n x t f ys, 
    num_occur_ec c v n -> 
    num_occur_ec (Eprim_c x t f ys c) v (num_occur_list ys v + n )
  | Noec_proj: forall  v n y v' t n' c,
                 num_occur_ec c v n ->
                 num_occur_ec (Eproj_c v' t n' y c) v (num_occur_list [y] v + n)
  | Noec_fun1: forall n m fds c v,
                 num_occur_ec c v n ->
                 num_occur_fds fds v m ->
                 num_occur_ec (Efun1_c fds c) v (n+m)
  | Noec_fun2: forall n m fdc e v ,
                 num_occur e v n ->
                 num_occur_fdc fdc v m ->
                 num_occur_ec (Efun2_c fdc e) v (n + m)
  with num_occur_fdc : fundefs_ctx -> var -> nat -> Prop :=
       | Nofc_fcons1 : forall v n m fds t ys c f,
           num_occur_ec c v n ->
           num_occur_fds fds v m -> 
             num_occur_fdc (Fcons1_c f t ys c fds) v  (n + m)
       | Nofc_fcons2 : forall e v n m fdc f t ys,
           num_occur e v n ->
           num_occur_fdc fdc v m ->
           num_occur_fdc (Fcons2_c f t ys e fdc) v (n + m) 
  .
                 
  
    (* number of time var occurs in exp in an applied position *)
  Inductive num_occur_app: exp -> var -> nat -> Prop :=
  | Num_oa_constr: forall x t c ys e v n, num_occur_app e v n -> num_occur_app (Econstr x t c ys e) v n
  | Num_oa_prim: forall x t f ys e v n, num_occur_app e v n -> num_occur_app (Eprim x t f ys e) v n
  | Num_oa_case: forall v' cl v,
      num_occur_app (Ecase v' cl) v (num_occur_list [v'] v)
  | Num_oa_proj: forall e v n  y v' t n', (* TODO: A&J counts y here *)
      num_occur_app  e v n -> 
      num_occur_app (Eproj v' t n' y e) v (num_occur_list [y] v + n)
  | Num_oa_app: forall f ys v,
      num_occur_app (Eapp f ys) v (num_occur_list [f] v)
  | Num_oa_fun: forall e v n m fl,
      num_occur_app e v n ->
      num_occur_app_fds fl v m ->
      num_occur_app (Efun fl e) v (n + m )
  with num_occur_app_fds: fundefs -> var -> nat -> Prop :=
       | Num_oa_nil : forall v,
           num_occur_app_fds Fnil v 0
       | Num_oa_cons : forall v t n v' ys e fds' m,
                               num_occur_app e v n ->
                               num_occur_app_fds fds' v m ->
           num_occur_app_fds (Fcons v' t ys e fds') v (n + m).

    (* number of time var occurs in exp in an escaping position *)
  Inductive num_occur_esc: exp -> var -> nat -> Prop :=
  | Num_oe_constr: forall x t c ys e v n, num_occur_esc e v n -> num_occur_esc (Econstr x t c ys e) v (n + (num_occur_list ys v))
  | Num_oe_prim: forall x t f ys e v n, num_occur_esc e v n -> num_occur_esc (Eprim x t f ys e) v (n + (num_occur_list ys v))
  | Num_oe_case: forall v' cl v,
      num_occur_esc (Ecase v' cl) v (num_occur_list (snd (split cl)) v)
  | Num_oe_proj: forall e v n  y v' t n',
      num_occur_esc  e v n -> 
      num_occur_esc (Eproj v' t n' y e) v n
  | Num_oe_app: forall f ys v,
      num_occur_esc (Eapp f ys) v (num_occur_list ys v)
  | Num_oe_fun: forall e v n m fl,
      num_occur_esc e v n ->
      num_occur_esc_fds fl v m ->
      num_occur_esc (Efun fl e) v (n + m )
  with num_occur_esc_fds: fundefs -> var -> nat -> Prop :=
       | Num_oe_nil : forall v,
           num_occur_esc_fds Fnil v 0
       | Num_oe_cons : forall v t n v' ys e fds' m,
                               num_occur_esc e v n ->
                               num_occur_esc_fds fds' v m ->
           num_occur_esc_fds (Fcons v' t ys e fds') v (n + m).



  

End OCCUR.  


Section BINDING.

  Inductive bv_e: exp -> list var -> Prop :=
  | Constr_bv : forall e l x t c ys, bv_e e l -> bv_e (Econstr x t c ys e) (x::l)
  | Case_bv : forall v cl, bv_e (Ecase v cl) []
  | Proj_bv: forall v t n y e l, bv_e e l -> bv_e (Eproj v t n y e) (v::l)
  | Fun_bv: forall fl e l1 l2, bv_f fl l1 -> bv_e e l2 -> bv_e (Efun fl e) (l1 ++ l2)
  | App_bv : forall f ys, bv_e (Eapp f ys) []
  | Prim_bv : forall x t f ys e l, bv_e e l -> bv_e (Eprim x t f ys e) (x::l)
  with bv_f : fundefs -> list var -> Prop :=
       | Cons_bv : forall f t ys e fds l1 l2, bv_e e l1 ->
                                              bv_f fds l2 ->
                                              bv_f (Fcons f t ys e fds) (f::(ys++(l1++l2)))
       | Nil_bv : bv_f Fnil [].

Hint Constructors bv_e bv_f.
  
Theorem e_bv_e : forall e, exists l, bv_e e l
with e_bv_f: forall f, exists l, bv_f f l.
  Proof.
    induction e; destructAll; clear e_bv_e; eauto. specialize (e_bv_f f). destruct e_bv_f. eauto. 
    induction f; destructAll; clear e_bv_f; eauto.  specialize (e_bv_e e); destruct e_bv_e. eauto.
Qed.


  
(*   
  Theorem bv_e_det: forall e l1 l2, bv_e e l1 -> bv_e e l2 -> l1 = l2
   with bv_f_det: forall f l1 l2, bv_f f l1 -> bv_f f l2 -> l1 = l2.                     
  Proof.
    - induction e; clear bv_e_det; intros; auto; inversion H; inversion H0; subst; auto.  
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
      + specialize (bv_f_det f _ _ H3 H8); specialize (IHe _ _ H5 H10); subst; reflexivity.
      + specialize (IHe _ _ H7 H14); subst; reflexivity.
    - induction f; clear bv_f_det; intros; auto; inversion H; inversion H0; subst.
      + specialize (bv_e_det e _ _ H7 H15); specialize (IHf _ _ H8 H16); subst; reflexivity.
      + reflexivity.
  Qed.
*)
 

  
End BINDING.

Section OTHER.

 Theorem findtag_not_empty: forall A cl (k:A) (v:tag), findtag cl v = Some k -> 0 < (length cl).
 Proof.
   induction cl; intros.
   - inversion H.
   - simpl in H. destruct a. destruct (M.elt_eq t v).
     + inversion H. simpl. omega.
     + simpl. apply IHcl in H. omega.
 Qed.

 
End OTHER.  