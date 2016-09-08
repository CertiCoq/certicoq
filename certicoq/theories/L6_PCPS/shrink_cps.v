Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Import RelationClasses.

Add LoadPath "../../libraries" as Libraries.

Require Import ExtLib.Data.Bool.
Require Libraries.Maps.
Require Coq.funind.Recdef.
Import Nnat.
Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Import Libraries.CpdtTactics Coq.Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
(* Add LoadPath "../common" as Common. *)
(* Add LoadPath "../L1_MalechaQuoted" as L1. *)
(* Add LoadPath "../L2_typeStripped" as L2. *)
(* Add LoadPath "../L3_flattenedApp" as L3. *)
(* Add LoadPath "../L4_deBruijn" as L4. *)
(* Add LoadPath "../L5_CPS" as CPS. *)

Add LoadPath "../L6_PCPS" as L6.
Require Import L6.cps.
Require Import L6.ctx.
Require Import L6.cps_util L6.List_util.


Definition var_dec := M.elt_eq.

(* Shallow val for constr and function *)
Inductive value : Type :=
| Vconstr: cTag -> list var -> value (* instead of list val *)
| Vfun :  fTag -> list var -> exp -> value. (* instead of env and full fds *)


(* substitution maps f |-> v where v can stand for a function or a datatype (for projections) *)
Definition ctx_map := M.t value.

(* renamer maps x |-> a *)
Definition r_map := M.t var.


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

Notation get_c := (getd 0%nat).
Notation get_b := (getd false).


  Fixpoint get_fun (f:var) (fds:fundefs): option (fTag * list var * exp) :=
    match fds with
      | Fnil => None
      | Fcons f' t xs e fds' =>
        if (var_dec f f') then Some (t, xs, e) else get_fun f fds'
    end.
    
  
  
Section MEASURECONTRACT.

  Create HintDb mtss.
  
  (* compute the number of constructors of an expression *)
  Fixpoint term_size (e: exp) : nat :=
    match e with
      | Econstr _ _ _ e => 1 + term_size e
      | Ecase _ cl => 1 + (List.fold_right (fun (p:(var * exp)) => fun  (n:nat)  => let (k, e) := p in
                                                                               (n + (term_size e))%nat) 0%nat cl)
      | Eproj _ _ _ _ e => 1 + term_size e
      | Eapp _ _ _ => 1
      | Eprim _ _ _ e => 1 + term_size e
      | Efun fds e => 1 + funs_size fds + term_size e
      | Ehalt _ => 1                                              
    end
  with funs_size fds : nat :=
         match fds with
           | Fcons _ _ _ e fds' => 1 + funs_size fds' + term_size e   
           | Fnil => 1
         end.


    Definition value_size (v: value) : nat :=
    match v with
    | Vconstr t lv => 0 
    | Vfun t lv e => term_size e 
    end.

  
  Definition sub_inl_size (sub:ctx_map) (inl:b_map) : nat :=
    M.fold  (fun n => fun f => fun v => 
                                             (if (get_b f inl) then
                                             0 else value_size v) + n
            ) sub 0. 

  

  
  
  Theorem subterm_size : forall e e',
                           subterm_e e' e -> (term_size e' < term_size e)%nat
                           with subterm_fds_size: forall e fds,
                           subterm_fds_e e fds -> (term_size e < funs_size fds)%nat
  .
  Proof.
  Admitted.


    Definition term_sub_inl_size (esi: (exp * ctx_map * b_map)): nat :=
    term_size (fst (fst esi)) + sub_inl_size (snd (fst esi)) (snd esi).


  (*
  Definition fold1r (A B : Type) (f: A -> B -> B) (sub:M.t A) (b:B): B  :=
    List.fold_right (fun p a => f (snd p) a) b (M.elements sub).


  Definition sub_size (sub: ctx_map) : nat :=
   (fold1r _ _ (fun v => fun n => (value_size v) + n) sub 0)%nat.
*)



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

    
    
    Theorem sub_remove_size: forall x t xs e im sub, M.get x sub = Some (Vfun t xs e) ->
                                                     (sub_inl_size sub im  = sub_inl_size sub (M.set x true im) + term_size e )%nat.
      Admitted.
(*    intros. unfold sub_size. unfold fold1r.  apply elements_remove in H. do 3 destruct H.  rewrite H0. rewrite H.   rewrite SetoidList.fold_right_commutes. apply plus_comm. apply equiv_size_eq. crush. intro. intros. intro. intros. unfold equiv_size in H1. subst. rewrite OrdersEx.Nat_as_OT.add_cancel_r.   assumption.  crush. *)


  Hint Resolve sub_remove_size: mtss.

  
  Theorem sub_remove_size': forall x sub inl,
                              (sub_inl_size (M.remove x sub) inl <= sub_inl_size sub inl)%nat.
    Admitted.




  
    Theorem sub_set_size: forall v x sub im, (sub_inl_size (M.set x v sub) im  <= value_size v + sub_inl_size sub im)%nat.
      Admitted.
      
   
    Theorem constr_sub_size: forall e v t lv sub im,                                 (term_sub_inl_size (e, M.set v (Vconstr t lv) sub, im) < term_sub_inl_size (Econstr v t lv e, sub, im))%nat.
    Proof.
      intros. unfold term_sub_inl_size. simpl. assert ((sub_inl_size (M.set v (Vconstr t lv) sub) im <= value_size (Vconstr t lv)  + sub_inl_size sub im))%nat. apply sub_set_size. simpl in H. omega.
    Qed.      

    
    Theorem subfds_fds_size: forall fds' fds, subfds_fds fds fds' -> (funs_size fds < funs_size fds')%nat.
    Proof.
      induction fds'; intros.
      - inversion H; subst. apply IHfds' in H2. simpl. omega. simpl. omega.
      - inversion H.
    Qed.

    Theorem case_size: forall g v k cl,
         findtag cl g = Some k -> 
         (term_size k < term_size (Ecase v cl))%nat.
    Proof.
      induction cl; intro; simpl in H.
      - inversion H.
      - destruct a.
        destruct (M.elt_eq c g).
        + inversion H; subst.
          admit.
        + apply IHcl in H.
          admit.
    Admitted.
    
    Theorem subterm_or_eq_size: forall e e', subterm_or_eq e e' -> (term_size e <= term_size e')%nat.
    Proof.
    Admitted.


    Theorem subfds_or_eq_size: forall fds fds', subfds_or_eq fds fds' -> (funs_size fds <= funs_size fds')%nat.
    Proof.
      destruct fds; intros; inversion H; try (subst; reflexivity).
      - apply subfds_fds_size in H0. omega.
      - inversion H0; subst. simpl; omega.  simpl; omega.
    Qed.

    Corollary subfds_or_eq_e_size:  forall fds fds', subfds_or_eq fds fds' -> forall e, (funs_size fds < term_size (Efun fds' e))%nat.
    intros.  apply subfds_or_eq_size in H. simpl. destruct e; omega.
  Qed.
        
    Corollary subfds_e_size: forall fds e, subfds_e fds e -> (funs_size fds < term_size e)%nat.
    Proof.
      intros. inversion H. destructAll. apply subfds_or_eq_size in H1. apply subterm_or_eq_size in H0. simpl in H0. omega.
    Qed.


      Definition b_map_le: b_map -> b_map -> Prop :=
    fun inl inl_r => forall v, get_b v inl = true -> get_b v inl_r = true.

  Theorem b_map_le_refl: forall i,
                           b_map_le i i.
  Proof.
    intros; intro; intros. assumption.
  Qed.

  Theorem b_map_le_trans: forall i i' i'',
                            b_map_le i i' -> b_map_le i' i'' -> b_map_le i i''.
  Proof.
    intros; intro; intros. apply H in H1. apply H0 in H1. assumption.
Qed.

  Theorem b_map_le_empt: forall i,
                         b_map_le (M.empty bool) i.
  Proof.
    intro; intro; intros. unfold get_b in H. unfold getd in H. rewrite M.gempty in H. inversion H.
  Qed.    

  Theorem b_map_le_true : forall v i,
             b_map_le   i  (M.set v true i).
  Proof.
    intros. intro. intros.
    destruct (var_dec v0 v); subst.
    -  apply gdss.
    - rewrite gdso by auto. apply H.
  Qed.

  Theorem sub_size_le : forall sub inl inl',
                          b_map_le inl inl' ->
                          sub_inl_size sub inl' <= sub_inl_size sub inl.                         
  Admitted.

  
      Inductive b_map_le_i : b_map -> b_map -> Prop :=
  | ble_refl: forall b, b_map_le_i b b
  | ble_add : forall b b' v, b_map_le_i b b' ->
                   b_map_le_i b (M.set v true b').

  Theorem b_map_le_c : forall b b',
    b_map_le_i b b' -> b_map_le b b'.
  Proof.
    intros.
    induction H.
    apply b_map_le_refl.
    subst.
    eapply b_map_le_trans. apply IHb_map_le_i.
    apply b_map_le_true.
  Qed.
  
  Theorem b_map_le_i_trans: forall b b',
                              b_map_le_i b b' -> forall b'',
                              b_map_le_i b' b'' ->
                              b_map_le_i b b''.
  Proof.
    intros b b' H b'' H'. induction H'; intros.
    assumption.
    apply ble_add. apply IHH'. assumption.
  Qed.    

  Theorem b_map_i_true:  forall b b' v,
  (b_map_le_i (M.set v true b) b' ->
   b_map_le_i b b').
  Proof.
    intros b b' v H.
    remember (M.set v true b) as tb.
    induction H.
    rewrite Heqtb. constructor 2; constructor.
    constructor 2. apply IHb_map_le_i in Heqtb. assumption.
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
                


  Fixpoint set_list {A:Type}  (l : list (M.elt * A)) (map: M.t A) : M.t A :=
    fold_right (fun xv cmap => M.set (fst xv) (snd xv) cmap ) map l.




  Definition apply_r sigma y :=
    match (M.get y sigma) with
    | Some v => v
    | None => y
    end.
  
  Definition apply_r_list sigma ys :=
    map (apply_r sigma) ys.

  Definition tag := positive.
    
  Definition apply_r_case (sigma:r_map) (cl: list (tag*var)) :=
    map (fun k => (fst k, apply_r sigma (snd k))) cl.
 



       (* could reduce the number of accesses to the c_map by first tallying the number of occ for each var in the list *)
     Fixpoint update_census_list (sig:r_map) (ys:list var) (fun_delta:var -> c_map -> nat) (count:c_map) :=
       match ys with
         | [] => count
         | y::ys' =>
           let y' := apply_r sig y in
           update_census_list sig ys' fun_delta (M.set y' (fun_delta y' count) count)
       end.

  

  
  Fixpoint update_census (sig:r_map) (e:exp) (fun_delta:var -> c_map -> nat) (count:c_map) : c_map :=    
  match e with
    | Econstr x t ys e =>
      let count' := update_census_list sig ys fun_delta count in
      update_census sig e fun_delta count' 
    | Eprim x f ys e =>
      let count' := update_census_list sig ys fun_delta count in
      update_census sig e fun_delta count' 
    | Ecase v cl =>
      fold_right (fun (p:(var*exp)) c =>
                    let (k, e) := p in
                    update_census sig e fun_delta c) count cl
    
    | Eproj v t n y e =>
       let count' := update_census_list sig [y] fun_delta count in
      update_census sig e fun_delta count' 
    | Efun fl e =>
      let count' := update_census_f sig fl fun_delta count in
      update_census sig e fun_delta count' 
    | Eapp f t ys => update_census_list sig (f::ys) fun_delta count
    | Ehalt v => update_census_list sig [v] fun_delta count                                    
  end 
with update_census_f (sig:r_map) (fds:fundefs) (fun_delta: var -> c_map -> nat) (count:c_map): c_map :=
       match fds with
         | Fcons v t ys e fds' => let count' := update_census sig e fun_delta count in
                                  update_census_f sig fds' fun_delta count' 
         | Fnil => count
       end
  .

  Print c_map.
  Definition init_census (e:exp) := update_census (M.empty var) e (fun v c =>
                                                                      get_c v c + 1)%nat (M.empty nat).
 Definition dec_census (sig:r_map) (e:exp) (count:c_map) := update_census sig e (fun v c => get_c v c - 1)%nat  count.
 Definition dec_census_list (sig:r_map) (ys:list var) (count:c_map) := update_census_list sig ys (fun v c => get_c v c - 1)%nat count.

 (* Decrease the count by each cl except the one(s) that match y *)
 Fixpoint dec_census_case (sig:r_map) (cl:list (var*exp)) (y:var) (count:c_map) :=
   match cl with
     | [] => count
     | (k, e)::cl' =>
       let count' := dec_census_case sig cl' y count in
       if (var_dec k y) then
         count'
       else
         dec_census sig e count
   end.

 (* assume NoDup(ys++xs) *)
 Fixpoint update_count_inlined (ys:list var) (xs:list var) (count:c_map) :=
   match ys, xs with
   | y::ys', x::xs' =>
     let cy := get_c y count in
     let cx := get_c x count in
     update_count_inlined ys' xs'  (M.set y (cy + cx - 1) (M.set x 0 count))%nat
   | _, _ => count
   end.
 
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
    | Econstr x t ys e' => Econstr x t (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eprim x f ys e' => Eprim x f (apply_r_list sigma ys) (rename_all (M.remove x sigma) e')
    | Eproj v t n y e' => Eproj v t n (apply_r sigma y) (rename_all (M.remove v sigma) e')
    | Ecase v cl =>
      Ecase (apply_r sigma v) (List.map (fun (p:var*exp) => let (k, e) := p in
                                               (k, rename_all sigma e)) cl)
    | Efun fl e' =>
      let fs := all_fun_name fl in
      let fl' := rename_all_fun (remove_all sigma fs) fl in

      Efun fl' (rename_all (remove_all sigma fs) e')
    | Eapp f t ys =>
      Eapp (apply_r sigma f) t (apply_r_list sigma ys)
    | Ehalt v => Ehalt (apply_r sigma v)       
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
  | Constr_case: forall x c' c'e cl co e y c'e' ys t,
      app_ctx c' (Ecase y cl) c'e ->
      findtag cl co = Some e ->
      app_ctx c' e c'e' -> 
      rw (Econstr x t co ys c'e) (Econstr x t co ys c'e')
  | Fun_inline: forall c'  vs c'e f  t xs fb c'e' fds,
                  app_ctx c' (Eapp f t vs) c'e ->
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



*) 
 End REWRITE.


Section CONTRACT.


  Fixpoint precontractfun (sig:r_map) (count:c_map) (sub:ctx_map) (fds:fundefs): (fundefs * c_map * ctx_map) :=
    match fds with
      | Fcons f t ys e fds' =>
        match (get_c f count) with
          | 0%nat => let count' := dec_census sig e count in
                 precontractfun sig count' sub fds' 
            
          | _ =>
            let (fc', sub') := precontractfun sig count sub fds' in
            let (fds'', count') := fc' in
            (Fcons f t ys e fds'', count', (M.set f (Vfun t ys e) sub'))
        end            
      | Fnil => (Fnil, count, sub)
    end.


  Theorem set_none_size: forall x sub im val, 
    M.get x sub = None ->
    (sub_inl_size (M.set x val sub) im =  value_size val + sub_inl_size sub im)%nat.
    Admitted.

  Theorem set_some_size: forall x sub im val val',
                           M.get x sub = Some val' ->
                           (sub_inl_size (M.set x val sub) im + value_size val' = sub_inl_size sub im + value_size val)%nat.
  Admitted.

  
  Theorem set_value_size : forall x val sub im,
                             (sub_inl_size (M.set x val sub) im <= sub_inl_size sub im + value_size val)%nat.
  Proof.    
    intros; destruct (M.get x sub) eqn:gxs.
    - apply set_some_size with (val := val) (im:=im) in gxs. omega. 
    - apply set_none_size with (val := val) (im := im) in gxs. omega.
Qed.
      
  Theorem precontractfun_size: forall fds sig count sub fds' count' sub',
                                 ((fds', count', sub') =  precontractfun sig count sub fds -> (forall im, sub_inl_size sub' im <= funs_size (fds) + sub_inl_size sub im /\ funs_size fds' <= funs_size fds))%nat.
  Proof.
    induction fds; intros; simpl in H.    
    - destruct (get_c v count) eqn: gcvc.
      + specialize (IHfds _ _ _ _ _ _ H im). simpl. omega.
      +  assert (exists fds' count' sub', (fds', count', sub') = precontractfun sig count sub fds). destruct (precontractfun sig count sub fds). destruct p. eauto. destructAll. assert (H0' := H0). specialize (IHfds _ _ _ _ _ _ H0 im).  rewrite <- H0' in H. inversion H; subst. simpl. split. eapply le_trans. apply set_value_size.  simpl. omega. omega.
    -  inversion H; subst. simpl. omega.
Qed.  

  Definition sublist {A:Type} (l:list A) (l':list A): Prop :=
    forall x, In x l -> In x l'.
  
  Definition subcl_e: list (var*exp) -> exp -> Prop :=
    fun cl' e =>
      exists y cl, e = Ecase y cl /\
                   sublist cl' cl.

  
  Program
  Fixpoint contractcases (oes: exp * ctx_map * b_map)
    (fcon: r_map -> c_map -> 
           forall esi:(exp*ctx_map*b_map), (term_sub_inl_size esi < term_sub_inl_size oes)%nat ->
                                    {esir:(exp * c_map * b_map) & (b_map_le_i (snd esi) (snd esir))})
    (sig:r_map) (count:c_map) (inl:b_map) (sub:ctx_map) (cl:list (var*exp))
    (pfe:subcl_e cl (fst (fst oes))) (pfsub: (sub_inl_size sub inl <= sub_inl_size (snd (fst oes)) (snd oes))%nat)
    : {lsi:(list (var*exp) * c_map * b_map) & (b_map_le_i inl (snd lsi))} :=
    match cl with
      | [] => existT _ ([], count, inl) (ble_refl inl)
      | (y,e)::cl' =>
        match fcon sig count (e, sub, inl) (_:(term_sub_inl_size (e,sub, inl) < term_sub_inl_size oes)%nat) with
          | existT _ (e', count', inl') bp =>
            (match contractcases oes fcon sig count' inl' sub cl' _ _ with
                 existT _ (cl'', count'', inl'') bp' =>
                 existT _ ((y,e')::cl'', count'', inl'') (b_map_le_i_trans _ _ bp _ bp')
             end)
        end
    end.
  Next Obligation.     
    simpl in pfe.
    inversion pfe.
    destructAll.
  Admitted.
  Next Obligation.
    simpl in *.
    inversion pfe.
    destructAll.
    exists x, x0.
    split. auto.
    intro. intros.
    apply H0.
    constructor 2. auto.
  Qed.
  Next Obligation.
    simpl.
    simpl in pfsub. 
    etransitivity.
    clear Heq_anonymous.
    eapply b_map_le_c in bp.
    eapply sub_size_le. apply bp. auto.
  Qed.

    (* oe is original expression of form (Efun fds e'), every e on which contract is called is a subterm of oe ( by subterm_fds ) *)


  Program
  Fixpoint postcontractfun (oes: exp * ctx_map * b_map)
             (fcon: r_map -> c_map -> 
           forall esi:(exp*ctx_map*b_map), (term_sub_inl_size esi < term_sub_inl_size oes)%nat ->
                                    {esir:(exp * c_map * b_map) & (b_map_le_i (snd esi) (snd esir))})
    (sig:r_map) (count:c_map) (inl:b_map) (sub:ctx_map) (fds: fundefs) 
        (pfe:subfds_e fds (fst (fst oes))) (pfsub: (sub_inl_size sub inl <= sub_inl_size (snd (fst oes)) (snd oes))%nat)
    : { fsi:(fundefs * c_map * b_map) & (b_map_le_i inl (snd fsi))} :=
    match fds with
      | Fnil => existT _ (Fnil, count, inl) (ble_refl inl)
      | Fcons f t ys e fds' =>
        (match (get_b f inl) with
           | true =>
              (* DEBUG: might want to verify here that the variable is actually dead *)
               postcontractfun oes fcon sig count inl sub fds' _ _
           | false =>
             (match (get_c f count) with
                | 0%nat => (* deadF *)                     
                  let count' := dec_census sig e count in
                  postcontractfun oes fcon sig count' inl (M.remove f sub) fds' _ _
                | _ =>
                  match (fcon sig count (e,sub,inl) (_:(term_sub_inl_size (e,sub, inl) < term_sub_inl_size oes)%nat)) with
                    | existT _ (e', count', inl') bp =>                   
                      match postcontractfun oes fcon sig count' inl' sub fds' _ _ with
                        | existT _ (fds'', count'', inl'') bp' =>
                          existT _ (Fcons f t ys e' fds'', count'', inl'') (b_map_le_i_trans _ _ bp _ bp')
                            end
                  end
              end)
         end)
    end.
  Solve Obligations with (program_simpl; simpl; simpl in pfe; destruct pfe; destructAll; exists x, x0;  split; auto; eapply subfds_or_eq_left; [apply subfds_cons | apply H0]).
  Solve Obligations with (program_simpl; simpl;  simpl in pfsub; eapply le_trans; [apply sub_remove_size' |  assumption]).
 Solve Obligations with (program_simpl; simpl in pfsub; simpl in pfe; unfold term_sub_inl_size; simpl; apply subfds_e_size in pfe; simpl in pfe; omega).
 Solve Obligations with (program_simpl; simpl; simpl in pfe; eapply subfds_e_subfds; [apply subfds_cons | apply pfe]).
 Next Obligation.
   program_simpl.
   simpl in pfsub.
   etransitivity.
   clear Heq_anonymous.
   eapply sub_size_le. eapply b_map_le_c. eauto.
   auto.
 Qed.



  Program Fixpoint contract (sig:r_map) (count:c_map) (es:exp * ctx_map * b_map) {measure (term_sub_inl_size es)} : {esir:(exp * c_map * b_map) & (b_map_le_i (snd es) (snd esir))} :=
    match es with
      | ( Ehalt v, sub, im) =>
          existT _ (Ehalt (apply_r sig v), count, im) _
      | ( Econstr x t ys e , sub, im) =>
        match (get_c x count) with
          | 0%nat =>
            let count' := dec_census_list sig ys count in 
            contract sig count' (e, sub, im )   
          | _ =>
            match contract sig count (e, (M.set x (Vconstr t ys) sub), im ) with
              | existT _  (e', count', im') bp =>
                (match (get_c x count') with
                   | 0%nat =>
                     let count'' := dec_census_list sig ys count'  in
                     existT _ (e', count'', im') bp
                   | _ =>
                     let ys' := apply_r_list sig ys in
                     existT _ (Econstr x t ys' e', count', im') bp
                 end)
            end
        end
      | (Eproj v t n y e, sub, im)  =>
        let y' := apply_r sig y in
        match (M.get y' sub) with
          | Some (Vconstr t ys) =>
            (match (nthN ys n) with
               | Some yn =>
                 let yn' := apply_r sig yn in
                 let count' := M.set y' ((get_c y' count) - 1)%nat count in
                 let count'' := M.set v 0%nat (M.set yn' (get_c v count + get_c yn' count)%nat count') in
                 contract (M.set v yn' sig) count'' (e, sub, im )
               | None =>
                 match contract sig count (e, sub, im ) with
                   | existT _ (e', count', im') bp =>
                     existT _ (Eproj v t n y' e', count', im') bp
                 end
             end)
          | _ =>
            (match (contract sig count (e, sub, im)) with
               | existT _ (e', count', im') bp =>
                 existT _ (Eproj v t n y' e', count', im') bp
             end)
        end
      | (Eprim x f ys e, sub, im) =>
        let ys' := apply_r_list sig ys in
        (match contract sig count (e, sub, im) with
            | existT _  (e', count', im') bp  =>
                     existT _ (Eprim x f ys' e, count', im') bp
         end)
      | (Ecase v cl, sub, im) =>
        let v' := apply_r sig v in
        (match (M.get v' sub) with
           | Some (Vconstr t lv) =>
             (match findtag cl t with
                | Some k =>
                  (* decrease count of each (sig e') other than k *)
                  let count' := dec_census_case sig cl t count in
                  (* recursive call to contract (will most likely) inline the definition of (sig k) *)
                  contract sig count' (k, sub, im)
                | None =>
                  (* fold over case body *)
                  (match contractcases (Ecase v cl, sub, im)
                                      (fun rm cm es H => contract rm cm es) sig count im sub cl _ _ with
                    | existT _ (cl', count', im') bp =>                      
                      existT _ (Ecase v' cl', count', im') bp
                  end)
(*                  (Ecase v' (apply_r_case sig cl), count, im) *)
              end)
           | _ =>
             (match contractcases (Ecase v cl, sub, im)
                                 (fun rm cm es H => contract rm cm es) sig count im sub cl _ _ with
               | existT _ (cl', count', im') bp  =>
                  
                 existT _ (Ecase v' cl', count', im') bp
             end)
         end )
      | (Efun fl e, sub, im) =>
        (match  precontractfun sig count sub fl with
         | (fl', count', sub') =>
           (match contract sig count' (e, sub', im) with
                existT _ (e', count'', im') bp =>
                match postcontractfun (Efun fl' e, sub, im') 
                                      (fun rm cm es H => contract rm cm es) sig count''
                                      im' sub fl' _ _ with 
                  | existT _ (fl'', count''', im'') bp' =>
                    (match fl'' with (* eliminate empty function defns. *)
                       | Fnil => existT _ ( e', count''', im'') (b_map_le_i_trans _ _ bp _ bp')
                       |  _  =>  existT _ (Efun fl'' e', count''', im'') (b_map_le_i_trans _ _ bp _ bp')
                     end)
                end
            end)
         end)
      
      | ( Eapp f t ys, sub, im) =>
        let f' := apply_r sig f in
        let ys' := apply_r_list sig ys in
        (match get_c f' count with
        | 1%nat => (match (M.get f' sub) with
                      | Some (Vfun t xs m)  =>
                            let im' := M.set f' true im in
                            (* update counts of ys' and xs after setting f' to 0 *)
                            let count' := update_count_inlined ys' xs (M.set f' 0 count) in
                            (match contract (set_list (combine xs ys') sig) count' (m,  sub, im') with
                               | existT _ (e, c, i) bp => existT _ (e, c, i) (b_map_i_true _ _ _ bp)
                             end)
                      | _ => existT _ (Eapp f' t ys', count, im) (ble_refl im)
                    end) 
        | _ => existT _ (Eapp f' t ys', count, im) (ble_refl im)
         end)
    end. 
  
 Solve Obligations with (program_simpl; unfold term_sub_inl_size; simpl;  rewrite plus_n_Sm; rewrite <- Nat.add_lt_mono_l;  eapply Nat.le_lt_trans; [apply sub_set_size | (simpl; omega)]).
 Next Obligation.  apply ble_refl. Defined. 
 Solve Obligations with (program_simpl; unfold term_sub_inl_size; simpl; symmetry in Heq_anonymous; apply findtag_not_empty in Heq_anonymous; omega).
 Next Obligation.
   unfold term_sub_inl_size in *; simpl in *.
   assert (term_size k < term_size (Ecase v cl))%nat.
   eapply case_size; eauto.
   simpl in H. omega.   
 Qed.
 Next Obligation.
   exists v, cl. intuition. intro. intuition.
 Qed.
  Next Obligation.
   exists v, cl. intuition. intro. intuition.
  Qed.
  Next Obligation.
    assert ((forall im, sub_inl_size sub' im <= funs_size (fl) + sub_inl_size c im /\ funs_size fl' <= funs_size fl))%nat. eapply precontractfun_size. eauto.  unfold term_sub_inl_size. simpl. specialize (H b). apply le_lt_n_Sm. omega. Qed.  
Next Obligation.
  inversion Heq_es; subst. 
  assert (Ha0 := Heq_anonymous0).
  apply precontractfun_size in Ha0.
  unfold term_sub_inl_size in H |- *. simpl in H |- *.
  eapply (lt_le_trans _ _ _ H). assert ( sub_inl_size c0 im' <=  sub_inl_size c0 b0). apply sub_size_le. apply b_map_le_c. auto. omega. auto.
Qed.
Next Obligation.  exists fl'. exists e. split. apply rt_refl. right. auto. Qed. 
Next Obligation.
  unfold term_sub_inl_size; simpl.
  symmetry in Heq_anonymous. apply sub_remove_size with (im :=  b) in Heq_anonymous. omega.
Qed.



End CONTRACT.  


Definition shrink_top (e:exp) : exp :=
  let count := init_census e in
  match (contract (M.empty var) count (e, (M.empty value), (M.empty bool))) with
    | existT _ (e', _, _) _ => e'
  end.


