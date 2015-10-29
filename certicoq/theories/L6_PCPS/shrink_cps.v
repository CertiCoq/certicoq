Require Import Coq.Relations.Relations.
Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
Import RelationClasses.

Require Import Bool.
Require Maps.
Require Recdef.
Import Nnat.
Require Import Arith BinNat String List Omega Program Psatz.
Require Import CpdtTactics Permutation.
Require Import HashMap.
Require Import cps.
Require Import cps_util.
Require Import maps_util.

Definition var_dec := M.elt_eq.

(* Shallow val for constr and function *)
Inductive value : Type :=
| Vconstr: type -> tag -> list var -> value (* instead of list val *)
| Vfun : type -> list var -> exp -> value. (* instead of env and full fds *)


(* substitution maps f |-> v where v can stand for a function or a datatype (for projections) *)
Definition ctx_map := M.t value.

(* renamer maps x |-> a *)
Definition r_map := M.t var.

(* census2 maps x |-> # applied occurrences, # escaping occurrences *)
Definition c2_map := M.t (nat * nat).

(* census maps x |-> total # of occurences *)
Definition c_map :=  M.t nat.

Definition b_map := M.t bool.

Definition getd {A:Type} (d:A) :=
  fun v sub => match M.get v sub with
               | None => d
               | Some e => e
               end.
Definition seto {A:Type} (x:var)(oa:option A) (map:M.t A):=
  match oa with
  | Some a => M.set x a map
  | None => map
  end.

Definition get_c2 := getd (0,0).
Definition get_c := getd 0.
Definition get_b := getd false.


  Fixpoint get_fun (f:var) (fds:fundefs): option (type * list var * exp) :=
    match fds with
      | Fnil => None
      | Fcons f' t xs e fds' =>
        if (var_dec f f') then Some (t, xs, e) else get_fun f fds'
    end.
    
  
  
Section MEASURECONTRACT.

  Create HintDb mtss.
  
  (* compute the tree height of an expression *)
  Fixpoint term_size (e: exp) : nat :=
    match e with
      | Econstr _ _ _ _ e => 1 + term_size e
      | Ecase _ cl => 1 + length cl
      | Eproj _ _ _ _ e => 1 + term_size e
      | Eapp _ _ => 1
      | Eprim _ _ _ _ e => 1 + term_size e
      | Efun fds e => 1 + funs_size fds + term_size e
    end
  with funs_size fds : nat :=
         match fds with
           | Fcons _ _ _ e fds' => 1 + funs_size fds' + term_size e   
           | Fnil => 1
         end.

  (* 0 is given to Vconstr for the Constr case of contract, could give 1 but then term_sub_size would have to be lex instead of sum *)
  Definition value_size (v: value) : nat :=
    match v with
    | Vconstr t g lv => 0 
    | Vfun t lv e =>  1 + term_size e 
    end.
  
  Theorem subterm_size : forall e e',
                           subterm_e e' e -> term_size e' < term_size e
                           with subterm_fds_size: forall e fds,
                           subterm_fds_e e fds -> term_size e < funs_size fds                         
  .
  Proof.
    - induction e; intros. 
     + inversion H; subst; [simpl; omega | simpl; apply subterm_size in H2;  omega].  
     + inversion H.
     + inversion H; subst; [simpl; omega | simpl; apply subterm_size in H2;  omega]. 
     + inversion H; subst. simpl. rewrite plus_n_Sm. apply subterm_fds_size in H2. omega.
     + inversion H; subst. 
     + inversion H; subst; [simpl; omega | simpl; apply subterm_size in H2;  omega]. 
    - intros. inversion H; subst. simpl. omega. simpl. apply subterm_size in H0. omega.  apply subterm_fds_size in H. assumption.
 Admitted. 


  Definition fold1r (A B : Type) (f: A -> B -> B) (sub:M.t A) (b:B): B  :=
    List.fold_right (fun p a => f (snd p) a) b (M.elements sub).

  
  Definition sub_size (sub: ctx_map) : nat :=
   fold1r _ _ (fun v => fun n => (value_size v) + n) sub 0.




  (* part of compcert 2.5 *)
    Theorem elements_remove:
    forall (A: Type) i v (m: M.t A),
    M.get i m = Some v ->
    exists l1 l2, M.elements m = l1 ++ (i,v) :: l2 /\ M.elements (M.remove i m) = l1 ++ l2.
Admitted.
    
    (* should be part of compcert :P *)
    Theorem element_set_none:
      forall (A: Type) i v (m: M.t A),
        M.get i m = None -> 
        exists l1 l2, M.elements m = l1 ++ l2 /\ M.elements (M.set i v m) = l1 ++ (i,v)::l2.
     Admitted.
      
      Theorem element_set_some:
        forall (A: Type) i v v' (m: M.t A),
        M.get i m = Some v'  -> 
        exists l1 l2, M.elements m = l1 ++ (i, v') :: l2 /\ M.elements (M.set i v m) = l1 ++ (i,v)::l2.
      Admitted.

   
    Definition equiv_size : (var * value) -> (var * value) -> Prop :=
      fun es => fun es' => value_size (snd es) = value_size (snd es').

    
    Theorem equiv_size_eq: Equivalence equiv_size.
    Proof.
      split; crush.
    Qed.

    
    
    Theorem sub_remove_size: forall x v sub, M.get x sub = Some v ->
                                             sub_size (M.remove x sub) + value_size v = sub_size sub.
  Proof. 
    intros. unfold sub_size. unfold fold1r.  apply elements_remove in H. do 3 destruct H.  rewrite H0. rewrite H.   rewrite SetoidList.fold_right_commutes. apply plus_comm. apply equiv_size_eq. crush. intro. intros. intro. intros. unfold equiv_size in H1. subst. rewrite OrdersEx.Nat_as_OT.add_cancel_r.   assumption.  crush. 
  Qed.        

  Hint Resolve sub_remove_size: mtss.

  Theorem sub_remove_size': forall x sub,
                              sub_size (M.remove x sub) <= sub_size sub.
  Proof.  
    intros. destruct (M.get x sub) eqn:gxs. apply sub_remove_size in gxs. omega. admit. (* need proper_sub_size after maps_util *)
    Admitted.
    
  Theorem sub_set_size1: forall x v v' sub, M.get x sub = Some v' ->  sub_size (M.set x v sub)  = value_size v + sub_size sub - value_size v'.
    Proof.
      intros. apply element_set_some with (v := v) in H .  unfold sub_size. unfold fold1r. do 3 destruct H. rewrite H. rewrite H0. rewrite SetoidList.fold_right_commutes. rewrite SetoidList.fold_right_commutes. simpl. rewrite plus_assoc. crush. apply equiv_size_eq. crush. intro. intros.  intro.  intros. crush. crush. apply equiv_size_eq. crush. intro. intros. intro. intros. crush. crush.
    Qed.


    Hint Resolve sub_set_size1: mtss.
    
    Theorem sub_set_size2: forall v x sub, M.get x sub = None ->  sub_size (M.set x v sub) = value_size v + sub_size sub.
    Proof.
      intros. apply element_set_none with (v := v) in H. do 3 destruct H.  unfold sub_size. unfold fold1r. rewrite H. rewrite H0. rewrite SetoidList.fold_right_commutes. crush. apply equiv_size_eq. crush. intro. intros. intro. crush. crush.
      Qed.

      Hint Resolve sub_set_size2: mtss.
      
  Theorem sub_set_size: forall v x sub, sub_size (M.set x v sub)  <= value_size v + sub_size sub.
    Proof.
      intros. assert (M.get x sub = None \/ exists v', M.get x sub = Some v'). destruct (M.get x sub). right. exists v0. reflexivity. left. reflexivity. destruct H. eapply sub_set_size2 in H. crush. destruct H.  eapply sub_set_size1 in H. crush.
    Qed.

    Hint Resolve sub_set_size: mtss.
      
      (* could also do lex on term + occurence count *)
  Definition term_sub_size (es: (exp * ctx_map)):  nat :=
    term_size (fst es) + sub_size (snd es).

  Definition funs_sub_size (fs: (fundefs * ctx_map)): nat :=
    funs_size (fst fs) + sub_size (snd fs).

  Theorem subterm_sub_size : forall e' e sub,
     subterm_e e' e  -> term_sub_size (e', sub) < term_sub_size (e, sub).
    Proof.
      intros. unfold term_sub_size. apply subterm_size in H. simpl. omega.
    Qed.

    Hint Resolve subterm_sub_size: mtss.
    

   
    Theorem constr_sub_size: forall e v t g lv sub,                                 term_sub_size (e, M.set v (Vconstr t g lv) sub) < term_sub_size (Econstr v t g lv e, sub).
    Proof.
      intros. unfold term_sub_size. simpl. assert (sub_size (M.set v (Vconstr t g lv) sub) <= value_size (Vconstr t g lv)  + sub_size sub). apply sub_set_size. simpl in H. omega.
    Qed.      

    
    Theorem subfds_fds_size: forall fds' fds, subfds_fds fds fds' -> funs_size fds < funs_size fds'.
    Proof.
      induction fds'; intros.
      - inversion H; subst. apply IHfds' in H2. simpl. omega. simpl. omega.
      - inversion H.
    Qed.

        
    Theorem subterm_or_eq_size: forall e e', subterm_or_eq e e' -> term_size e <= term_size e'.
    Proof.
      induction e; intros; inversion H; try (subst; reflexivity); try (apply subterm_size in H0; omega).
    Qed.


    Theorem subfds_or_eq_size: forall fds fds', subfds_or_eq fds fds' -> funs_size fds <= funs_size fds'.
    Proof.
      destruct fds; intros; inversion H; try (subst; reflexivity).
      - apply subfds_fds_size in H0. omega.
      - inversion H0; subst. simpl; omega.  simpl; omega.
    Qed.

    Corollary subfds_or_eq_e_size:  forall fds fds', subfds_or_eq fds fds' -> forall e, funs_size fds < term_size (Efun fds' e).
    intros.  apply subfds_or_eq_size in H. simpl. destruct e; omega.
  Qed.
        
    Corollary subfds_e_size: forall fds e, subfds_e fds e -> funs_size fds < term_size e.
    Proof.
      intros. inversion H. destructAll. apply subfds_or_eq_size in H1. apply subterm_or_eq_size in H0. simpl in H0. omega.
    Qed.


          
End MEASURECONTRACT.



(* option_map on pairs of option *)
  Fixpoint f_opt {A} f on om: option A :=
    match on with
      | Some n =>  (match om with
                      | Some m => Some (f n m)
                      | None => Some n
                    end)
      | None => om
    end
  .
  
  Definition f_pair {A B C D} (f: A -> A -> B) (g: C -> C -> D): (A * C) -> (A * C)  -> (B * D) :=
    fun e1 e2 => match (e1, e2) with
               | ( (a1, c1), (a2, c2)) => ( f a1 a2 , g c1 c2)
             end.

  Inductive occ_type : Type :=
  | App_occ : occ_type
  | Esc_occ : occ_type.
                
  Definition c2_up (v:var) (t:occ_type) (count:c2_map) :=
    match M.get v count with
    | Some (an, en) => match t with
                       | App_occ => M.set v (an + 1, en) count
                       | Esc_occ => M.set v (an, en + 1 ) count
                       end
    | None =>  match t with
                       | App_occ => M.set v ( 1, 0) count
                       | Esc_occ => M.set v ( 0, 1) count
               end
    end.


  Fixpoint set_list {A:Type}  (l : list (M.elt * A)) (map: M.t A) : M.t A :=
    fold_right (fun xv cmap => M.set (fst xv) (snd xv) cmap ) map l.



  Definition count_init (ao:list var) (eo: list var): c2_map :=
   fold_right (fun v count => c2_up v App_occ count) 
              (fold_right (fun v count => c2_up v Esc_occ count) (M.empty (nat * nat)) eo)
    ao. 

 Definition c2_combine (c1 :c2_map) (c2:c2_map) : c2_map :=  
   M.combine (f_opt (f_pair plus plus)) c1 c2.


  Definition apply_r sigma y :=
    match (M.get y sigma) with
    | Some v => v
    | None => y
    end.
  
  Definition apply_r_list sigma ys :=
    map (apply_r sigma) ys.

  Definition apply_r_case (sigma:r_map) (cl: list (tag*var)) :=
    map (fun k => (fst k, apply_r sigma (snd k))) cl.
 


(* 
Fixpoint census (e:exp): c_map := 
  match e with
  | Econstr x t c ys e => M.combine (f_opt plus) (count_init [] (apply_r_list sigma ys)) (census e)
  | Eprim x t f ys e =>  M.combine (count_init [] (apply_r_list sigma ys)) (census sigma e)                                    
  | Ecase v cl => count_init [(apply_r sigma v)] (apply_r_list sigma (snd (split cl)))
  | Eproj v t n y e => c2_combine (count_init [(apply_r sigma y)] []) (census sigma e) 
  | Efun fl e => c2_combine (census_f sigma fl) (census sigma e)
  | Eapp f ys => count_init [(apply_r sigma f)] (apply_r_list sigma ys)
  end
  with census_f (sigma:r_map) (fds:fundefs): c2_map :=
         match fds with
         | Fcons v t ys e fds' => c2_combine (census sigma e) (census_f sigma fds')

         | Fnil => M.empty (nat * nat)
         end. *) 

  Fixpoint c_combine fun_delta (count:c_map) (ys:list var) :=
    match ys with
      | y::ys => M.set y (fun_delta (get_c y count) 1) count
      | [] => count
    end.


       (* could reduce the number of accesses to the c_map by first tallying the number of occ for each var in the list *)
     Fixpoint update_census_list (sig:r_map) (ys:list var) (fun_delta:nat -> nat -> nat) (count:c_map) :=
       match ys with
         | [] => count
         | y::ys' =>
           let y' := apply_r sig y in
           update_census_list sig ys' fun_delta (M.set y' (fun_delta (get_c y' count) 1) count)
       end.

  

  
  Fixpoint update_census (sig:r_map) (e:exp) (fun_delta:nat -> nat -> nat) (count:c_map) : c_map :=    
  match e with
    | Econstr x t c ys e =>
      let count' := update_census_list sig ys fun_delta count in
      update_census sig e fun_delta count' 
    | Eprim x t f ys e =>
      let count' := update_census_list sig ys fun_delta count in
      update_census sig e fun_delta count' 
    | Ecase v cl =>
      update_census_list sig (v::(snd (split cl))) fun_delta count
    | Eproj v t n y e =>
       let count' := update_census_list sig [y] fun_delta count in
      update_census sig e fun_delta count' 
    | Efun fl e =>
      let count' := update_census_f sig fl fun_delta count in
      update_census sig e fun_delta count' 
    | Eapp f ys => update_census_list sig (f::ys) fun_delta count
  end 
with update_census_f (sig:r_map) (fds:fundefs) (fun_delta:nat -> nat -> nat) (count:c_map): c_map :=
       match fds with
         | Fcons v t ys e fds' => let count' := update_census sig e fun_delta count in
                                  update_census_f sig fds' fun_delta count' 
         | Fnil => count
end.


Definition init_census (e:exp) := update_census (M.empty var) e plus (M.empty nat).
 Definition dec_census (sig:r_map) (e:exp) (count:c_map) := update_census sig e minus count.
 Definition dec_census_list (sig:r_map) (ys:list var) (count:c_map) := update_census_list sig ys minus count.
     
Section REWRITE.



  Fixpoint remove_all (sigma:r_map) (vs:list var) :=
    match vs with
    | v::vs' => remove_all (M.remove v sigma) vs'
    | [] => sigma
    end.
  
  Fixpoint all_fun_name (fds:fundefs) : list var :=
    match fds with
    | Fcons f t ys e fds' => f::(all_fun_name fds')
    | Fnil => []
    end.

  Definition rename_init (vp: list (var * var)): r_map :=
    fold_right (fun xv sigma => M.set (fst xv) (snd xv) sigma ) (M.empty var) vp.


  
  Fixpoint rename_all (sigma:r_map) (e:exp) : exp :=
    match e with
    | Econstr x t c ys e' => Econstr x t c (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eprim x t f ys e' => Eprim x t f (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all (M.remove v sigma) e')
    | Ecase v cl =>
      let (cs, ks) := split cl in
      Ecase (apply_r sigma v) (combine  cs (apply_r_list sigma ks))
    | Efun fl e' =>
      let fs := all_fun_name fl in
      let fl' := rename_all_fun (remove_all sigma fs) fl in

      Efun fl' (rename_all (remove_all sigma fs) e')
    | Eapp f ys =>
      Eapp (apply_r sigma f) (apply_r_list sigma ys)
    end
  with rename_all_fun (sigma:r_map) (fds:fundefs): fundefs :=
         match fds with
         | Fnil => Fnil
         | Fcons v' t ys e fds' => Fcons v' t ys (rename_all (remove_all sigma ys) e) (rename_all_fun sigma fds')
         end.

  Definition rename (y x:var) (e:exp) : exp :=
    rename_all (M.set x y (M.empty (var))) e.

  
  Inductive split_fds: fundefs -> fundefs -> fundefs -> Prop :=
  | Left_f: forall lfds rfds lrfds v t ys e,  split_fds lfds rfds lrfds -> split_fds (Fcons v t ys e lfds) rfds (Fcons v t ys e lrfds)
  | Right_f: forall lfds rfds lrfds v t ys e, split_fds lfds rfds lrfds -> split_fds lfds (Fcons v t ys e rfds) (Fcons v t ys e lrfds)
  | End_f: split_fds Fnil Fnil Fnil.


  (* rewrite rules that 
    (1) produces a smaller exp
    (2) preserves the unique binding invariant 

  Fun_split separates a group of mutually recursive functions lrf into two (lf and rf) where the functions bound in rf do not appear in lf 
     Fun_inline replaces one occurence on f by its definition
     Fun_dead removes the definition of a set of functions if none of them occur in the rest of the program
     Constr_dead removes the binding of a datatype when it doesn't appear in the rest of the program 
     Constr_proj replaces a binding by the nth projection of a datatype when the datatype is known (in ctx) 
     Constr_case reduces a pattern match into an application of the right continuation on the datatype when the datatype is know (in ctx)

   *)
  Inductive rw: relation exp :=
  | Fun_split: forall lf rf lrf e,
      split_fds lf rf lrf ->    
      Forall (fun v => num_occur_fds rf v 0) (all_fun_name lf) ->
      rw (Efun lrf e) (Efun lf (Efun rf e))
  | Fun_dead: forall e fds,
                Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
                rw (Efun fds e) e
  | Constr_dead: forall x t c ys e, 
      num_occur e x 0 ->
      rw (Econstr x t c ys e) e
  | Constr_proj: forall v  t t' n x e k ys c c' c'e c'e', 
      app_ctx c' (Eproj v t' n x e) c'e ->
      nthN ys n = Some k -> 
      app_ctx c' (rename k x e) c'e' -> 
      rw (Econstr x t c ys c'e) (Econstr x t c ys c'e')
  | Constr_case: forall x c' c'e cl co k y c'e' ys t,
      app_ctx c' (Ecase y cl) c'e ->
      findtag cl co = Some k ->
      app_ctx c' (Eapp k [y]) c'e' -> 
      rw (Econstr x t co ys c'e) (Econstr x t co ys c'e')
  | Fun_inline: forall c'  vs c'e f  t xs fb c'e' fds,
                  app_ctx c' (Eapp f vs) c'e ->
                  num_occur_ec c' f 0 -> 
      get_fun f fds = Some (t, xs, fb) ->
      app_ctx c' (rename_all (set_list (combine xs vs) (M.empty var)) fb) c'e' ->
      rw (Efun fds c'e) (Efun fds c'e')        
  .
         
    
  Fixpoint collect_funvals (fds:fundefs)  : list (var * value) :=
    match fds with
    | Fnil => []
    | Fcons v t ys e fds' => ( v, (Vfun t ys e))::(collect_funvals fds')
    end.
         
  
  Inductive gen_rw : relation exp :=
  | Ctx_rw : forall c e e' ce ce',
     rw e e' ->
     app_ctx c e ce ->
     app_ctx c e' ce' ->
     gen_rw ce ce'
  .


  Definition gr_clos := clos_refl_trans exp gen_rw.



 
 End REWRITE.


Section CONTRACT.


  Fixpoint precontractfun (sig:r_map) (count:c_map) (sub:ctx_map) (fds:fundefs): (fundefs * c_map * ctx_map) :=
    match fds with
      | Fcons f t ys e fds' =>
        match (get_c f count) with
          | 0 => let count' := dec_census sig e count in
                 precontractfun sig count' sub fds' 
            
          | _ =>
            let (fc', sub') := precontractfun sig count sub fds' in
            let (fds'', count') := fc' in
            (Fcons f t ys e fds'', count', (M.set f (Vfun t ys e) sub'))
        end            
      | Fnil => (Fnil, count, sub)
    end.


  Theorem set_none_size: forall x sub val, 
    M.get x sub = None ->
    sub_size (M.set x val sub) =  value_size val + sub_size sub. 
    Admitted.

  Theorem set_some_size: forall x sub val val',
                           M.get x sub = Some val' ->
                           sub_size (M.set x val sub) + value_size val' = sub_size sub + value_size val.
  Admitted.

  
  Theorem set_value_size : forall x val sub,
                             sub_size (M.set x val sub) <= sub_size sub + value_size val.
  Proof.    
    intros; destruct (M.get x sub) eqn:gxs.
    - apply set_some_size with (val := val) in gxs. omega. 
    - apply set_none_size with (val := val) in gxs. omega.
Qed.
      
  Theorem precontractfun_size: forall fds sig count sub fds' count' sub',
                                 (fds', count', sub') =  precontractfun sig count sub fds -> sub_size(sub') <= funs_size (fds) + sub_size (sub).
  Proof.
    induction fds; intros; simpl in H.
    - destruct (get_c v count) eqn: gcvc.
      + apply IHfds in H. simpl. omega.
      +  assert (exists fds' count' sub', (fds', count', sub') = precontractfun sig count sub fds). destruct (precontractfun sig count sub fds). destruct p. eauto. destructAll. assert (H0' := H0). apply IHfds in H0.  rewrite <- H0' in H. inversion H; subst. simpl. eapply le_trans. apply set_value_size.  simpl. omega.        
    - inversion H; subst. simpl. omega.
Qed.  
  
  (* oe is original expression of form (Efun fds e'), every e on which contract is called is a subterm of oe ( by subterm_fds ) *)
  Program Fixpoint postcontractfun (oes: exp * ctx_map) (fcon:  r_map -> c_map -> b_map -> forall es:(exp*ctx_map), (term_sub_size es < term_sub_size oes) -> (exp * c_map * b_map))  (sig:r_map) (count:c_map) (inl:b_map) (sub:ctx_map) (fds: fundefs) (pfe:subfds_e fds (fst oes)) (pfsub:sub_size sub <= sub_size (snd oes)) : (fundefs * c_map * b_map) :=
    match fds with
      | Fnil => (Fnil, count, inl)
      | Fcons f t ys e fds' =>
        (match (get_b f inl) with
           | true => postcontractfun oes fcon sig count inl sub fds' _ _
           | false =>
             (match (get_c f count) with
                | 0 => (* deadF *)                     
                  let count' := dec_census sig e count in
                  postcontractfun oes fcon sig count' inl (M.remove f sub) fds' _ _
                | _ =>
                  let (ec', inl') := (fcon sig count inl (e,sub) (_:(term_sub_size (e,sub) < term_sub_size oes))): (exp * c_map * b_map) in
                  let (e', count') := ec' in
                  
                  let (fc', inl'') := postcontractfun oes fcon sig count' inl' sub fds' _ _ in
                  let (fds'', count'') := fc' in                     
                  (Fcons f t ys e' fds'', count'', inl'')
              end)
         end)
    end.
  Solve Obligations with (program_simpl; simpl; simpl in pfe; destruct pfe; destructAll; exists x x0;  split; auto; eapply subfds_or_eq_left; [apply subfds_cons | apply H0]).
  Solve Obligations with (program_simpl; simpl;  simpl in pfsub; eapply le_trans; [apply sub_remove_size' |  assumption]).
 Solve Obligations with (program_simpl; simpl in pfsub; simpl in pfe; unfold term_sub_size; simpl; apply subfds_e_size in pfe; simpl in pfe; omega).
 Solve Obligations with (program_simpl; simpl; simpl in pfe; eapply subfds_e_subfds; [apply subfds_cons | apply pfe]).
 Next Obligation. Defined.
                   
  Program Fixpoint contract (sig:r_map) (count:c_map) (inl:b_map) (es:exp * ctx_map) {measure (term_sub_size es)} : (exp * c_map * b_map) :=
    match es with
      | ( Econstr x t c ys e , sub) =>
        match (get_c x count) with
          | 0 =>
            let count' := dec_census_list sig ys count in 
            contract sig count' inl (e, sub)
          | _ =>
            let '(e', count', inl') := contract sig count inl (e, (M.set x (Vconstr t c ys) sub)) in
            (match (get_c x count) with
              | 0 =>
                let count'' := dec_census_list sig ys count'  in
                (e', count'', inl')
              | _ => 
                 (Econstr x t c ys e', count', inl')
             end)
        end
      | (Eproj v t n y e, sub)  =>
        let y' := apply_r sig y in
        match (M.get y' sub) with
          | Some (Vconstr t c ys) =>
            (match (nthN ys n) with
               | Some yn =>
                 let yn' := apply_r sig yn in
                 let count' := M.set y' ((get_c y' count) - 1) count in
                 let count'' := M.set v 0 (M.set yn' (get_c v count + get_c yn' count) count) in
                 contract (M.set v yn' sig) count'' inl (e, sub)
               | None =>
                 let (ec', inl') := contract sig count inl (e, sub) in
                 let (e', count') := ec' in
                 (Eproj v t n y' e', count', inl')                  
             end)
          | _ =>
            (match (contract sig count inl (e, sub)) with
               | (e', count', inl') =>
                 (Eproj v t n y' e', count', inl')
             end)
        end
      | (Eprim x t f ys e, sub) =>
        let ys' := apply_r_list sig ys in
        let '(e', count', inl') := contract sig count inl (e, sub) in
             (Eprim x t f ys' e, count', inl')
      | (Ecase v cl, sub) =>
        let v' := apply_r sig v in
        (match (M.get v' sub) with
           | Some (Vconstr t g lv) =>
             (match findtag cl g with
                | Some k =>
                  (* decrease count of each (sig k') other than k *)
                  let ks := snd (split cl) in
                  let count' := dec_census_list sig (remove var_dec k ks) count in
                  (* recursive call to contract (will most likely) inline the definition of (sig k) *)
                  contract sig count' inl (Eapp (apply_r sig k) [v'], sub)
                | None => (Ecase v' (apply_r_case sig cl), count, inl)
              end)
           | _ => (Ecase v' (apply_r_case sig cl), count, inl)
         end )
      | (Efun fl e, sub) =>
             let '(fl', count', sub') := precontractfun sig count sub fl in
             let '(e', count'', inl') := contract sig count' inl (e, sub') in
             let '(fl'', count''', inl'') := postcontractfun (Efun fl' e', sub') contract sig count'' inl' sub' fl' _ _ in 
             (Efun fl'' e', count''', inl'')
        
      | ( Eapp f ys, sub) =>
        let f' := apply_r sig f in
        let ys' := apply_r_list sig ys in
        (match get_c f' count with
          | 1 => (match (M.get f' sub) with
                   | Some (Vfun t xs m) =>
                     let inl' := M.set f' true inl in
                   (* update counts of ys' and xs *)
                     let count' := count in
                     contract (set_list (combine xs ys') sig) count' inl' (m, M.remove f' sub)                   
                   | _ => (Eapp f' ys', count, inl)
                 end)
          | _ => (Eapp f' ys', count, inl)
          end) 


    end. 
  
 Solve Obligations with (program_simpl; unfold term_sub_size; simpl;  rewrite plus_n_Sm; rewrite <- Nat.add_lt_mono_l;  eapply Nat.le_lt_trans; [apply sub_set_size | (simpl; omega)]).
 Next Obligation. Defined. 
Solve Obligations with (program_simpl; unfold term_sub_size; simpl; symmetry in Heq_anonymous; apply findtag_not_empty in Heq_anonymous; omega).
Next Obligation. apply precontractfun_size in Heq_anonymous. unfold term_sub_size. simpl. apply le_lt_n_Sm. omega. Qed.  
Next Obligation. Show Proof. inversion Heq_es; subst. assert (Ha0 := Heq_anonymous0). apply precontractfun_size in Ha0.  unfold term_sub_size; simpl.  admit. Admitted. (* need...to look more into this *)
Next Obligation.  exists fl' e'. split; right; reflexivity. Qed.
Next Obligation.  unfold term_sub_size; simpl. symmetry in Heq_anonymous. apply sub_remove_size in Heq_anonymous. rewrite <- Heq_anonymous. simpl. omega. Qed. 



End CONTRACT.  


(* 
invariants for programs:


precontractfun:

forall e, correct_count (sig inl ctx (Efun fl e)) c -> 
  map_ctx_view sub (inl ctx)
 (fl', c', sub') = precontractfun sig c sub fl ->
   map_ctx_view sub' (inl (ctx) . fl')
/\ correct_count (sig inl ctx (Efun fl' e)) c'
/\ sig inl ctx (Efun fl e) ~gen_rw~ sig inl ctx (Efun fl' e)

will only use Fun_split and Fun_dead



postcontractfun: similar to precontract fun


contract: *)