(* 
  Proof of correctness of the Clight code generation phase of CertiCoq 

  > Relates values to location in memory (syntactic)
  > Relates expression to statements (syntactic)
  > Relates Codegen values (header, payload) to Codegen values after GC (syntactic, up to non-function pointer location)
  > Relates LambdaANF states to Codegen states according to execution semantics



TODO: bundle the notation in LambdaANF_to_Clight and import it instead of redefining it 

Done: change LambdaANF_to_Clight's fn_vars into fn_temps
Done: change LambdaANF_to_Clight's reserve into reserve', todo update proof with new order 
Done: update proof to 64 bits (parametric over Archi.ptr64) 
 *)
        
Require Import CertiCoq.LambdaANF.cps CertiCoq.LambdaANF.eval CertiCoq.LambdaANF.cps_util CertiCoq.LambdaANF.List_util CertiCoq.LambdaANF.Ensembles_util CertiCoq.LambdaANF.identifiers CertiCoq.LambdaANF.tactics CertiCoq.LambdaANF.shrink_cps_corresp.
  


(* Require Import RamifyCoq.CertiGC.GCGraph. *)



Require Import Coq.ZArith.BinInt Coq.ZArith.Znat Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.micromega.Lia Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec Coq.Relations.Relations.


Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values
        compcert.common.Globalenvs
        compcert.common.Memory.

Require Import CertiCoq.Codegen.tactics
               CertiCoq.Codegen.LambdaANF_to_Clight
               CertiCoq.Codegen.LambdaANF_to_Clight_stack.

(* Re-bind names shadowed by _stack import *)
Notation asgnAppVars' := LambdaANF_to_Clight.asgnAppVars'.
Notation asgnAppVars'' := LambdaANF_to_Clight.asgnAppVars''.
Notation asgnAppVars := LambdaANF_to_Clight.asgnAppVars.
Notation asgnFunVars' := LambdaANF_to_Clight.asgnFunVars'.
Notation makeVar := LambdaANF_to_Clight.makeVar.
Notation mkCallVars := LambdaANF_to_Clight.mkCallVars.
Notation make_case_switch := LambdaANF_to_Clight.make_case_switch.
Notation ctor_rep := LambdaANF_to_Clight.ctor_rep.
Notation enum := LambdaANF_to_Clight.enum.
Notation boxed := LambdaANF_to_Clight.boxed.
Notation make_ctor_rep := LambdaANF_to_Clight.make_ctor_rep.
Notation assignConstructorS' := LambdaANF_to_Clight.assignConstructorS'.
Notation assignConstructorS := LambdaANF_to_Clight.assignConstructorS.
Notation val := LambdaANF_to_Clight.val.
Notation uval := LambdaANF_to_Clight.uval.
Notation add := LambdaANF_to_Clight.add.
Notation c_int := LambdaANF_to_Clight.c_int.
Notation c_int' := LambdaANF_to_Clight.c_int.
Notation valPtr := LambdaANF_to_Clight.valPtr.
Notation makeTag := LambdaANF_to_Clight.makeTag.
Notation makeTagZ := LambdaANF_to_Clight.makeTagZ.
Notation mkCall := LambdaANF_to_Clight.mkCall.
Notation mkFunTy := LambdaANF_to_Clight.mkFunTy.

Require Import CertiCoq.Libraries.maps_util.
From Coq.Lists Require List.
Import List.ListNotations.

Lemma var_dec_eq : decidable_eq var.
Proof. intros x y. unfold decidable. destruct (cps_util.var_dec x y); auto. Qed.

Lemma Zred_factor3 n m : n * m + n = n * (1 + m).
Proof. lia. Qed.

Lemma Zshiftl_mul_two_p (x y : Z) : (0 <= y)%Z -> Z.shiftl x y = (x * Zpower.two_p y)%Z.
Proof. intros. rewrite Zpower.two_p_correct. apply Z.shiftl_mul_pow2. auto. Qed.

Lemma Zshiftr_div_two_p (x y : Z) : (0 <= y)%Z -> Z.shiftr x y = (x / Zpower.two_p y)%Z.
Proof. intros. rewrite Zpower.two_p_correct. apply Z.shiftr_div_pow2. auto. Qed.


(* Space guarantied by the GC on return *)
Definition gc_size:Z := Z.shiftl 1%Z 16%Z.
 
Definition loc:Type := block * ptrofs.


Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                           {| attr_volatile := false; attr_alignas := None |}).
Notation boolTy := (Tint IBool Unsigned noattr). 


 (* 64-bit 

Definition int_chunk := if Archi.ptr64 then Mint64 else Mint32.
Definition val := if Archi.ptr64 then ulongTy else uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *) 
Definition uval := if Archi.ptr64 then ulongTy else uintTy.
Definition sval := if Archi.ptr64 then longTy else intTy.
Definition val_typ := if Archi.ptr64 then  (AST.Tlong:typ) else (Tany32:typ).
Definition Init_int x := if Archi.ptr64 then (Init_int64 (Int64.repr x)) else (Init_int32 (Int.repr x)).
Definition make_vint z := if Archi.ptr64 then Vlong (Int64.repr z) else Vint (Int.repr z).
Definition make_cint z t := if Archi.ptr64 then Econst_long (Int64.repr z) t else (Econst_int (Int.repr z) t).
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.                                                                   
  *)



                



Definition int_size := (size_chunk int_chunk).
Definition max_args :=   1024%Z. (* limited by space in boxed header *)

Theorem int_size_pos:
  (0 <= size_chunk int_chunk)%Z.
Proof.
  apply Z.lt_le_incl. apply Z.gt_lt.   apply size_chunk_pos. 
Qed.


Definition uint_range : Z -> Prop := 
  fun i => (0 <= i <=   Ptrofs.max_unsigned)%Z. 
Transparent uint_range.

Theorem uint_range_unsigned:
  forall i,
    uint_range (Ptrofs.unsigned i).
Proof.
  apply Ptrofs.unsigned_range_2.
Qed.
  
Ltac int_red := unfold int_size in *; simpl size_chunk in *.

Ltac chunk_red := unfold int_size in *; unfold int_chunk in *; destruct Archi.ptr64 eqn:Harchi; simpl size_chunk in *.

Ltac uomega := (unfold int_size; simpl size_chunk; lia).

Definition uint_range_l: list Z -> Prop :=
  fun l => Forall uint_range l.


Theorem ptrofs_mu_weak:
  (Int.max_unsigned <= Ptrofs.max_unsigned)%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi. 

  rewrite Ptrofs.modulus_eq64 by auto. unfold Int.modulus. unfold Int64.modulus. simpl. lia.
  rewrite Ptrofs.modulus_eq32 by auto. reflexivity.
Qed.

Theorem ptrofs_ms:
(Ptrofs.max_signed = if Archi.ptr64 then Int64.max_signed else Int.max_signed )%Z.
Proof.
  unfold Int.max_signed.
  unfold Ptrofs.max_signed.
  unfold Ptrofs.half_modulus.
  destruct (Archi.ptr64) eqn:Harchi.   
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity. 
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.
  

Theorem ptrofs_mu:
  (Ptrofs.max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned )%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi.   
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity. 
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.

Ltac uint_range_ptrofs :=
  unfold uint_range_l; unfold uint_range; rewrite ptrofs_mu.

Ltac solve_uint_range:=
  unfold Int64.max_unsigned in *; unfold Int64.modulus in *; unfold Int.max_unsigned in *; unfold Int.modulus in *;  simpl in *; (match goal with
          | [H:uint_range _ |- _] => unfold uint_range in H; rewrite ptrofs_mu in H; solve_uint_range
          | [H:uint_range_l _ |- _] => unfold uint_range_l in H;  solve_uint_range 
          | [H: Forall uint_range _ |- _] => inv H; solve_uint_range 
          | [|- uint_range _] => unfold uint_range; unfold Int.max_unsigned; unfold Int.modulus; simpl; try lia
          | [|- uint_range (Ptrofs.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range (Int.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range_l _] => unfold uint_range_l; solve_uint_range
          | [ |- Forall uint_range _] => constructor; solve_uint_range
          | _ => auto
          end).



Theorem int_z_mul :
  forall i y,
    uint_range_l [i; y] -> 
  Ptrofs.mul (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i * y)%Z.
Proof.
  intros.
  unfold Ptrofs.mul.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr. reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.

  
Theorem int_z_add:
  forall i y,
    uint_range_l [i; y] -> 
    Ptrofs.add (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i + y)%Z.
Proof.
  intros.
                       rewrite Ptrofs.add_unsigned.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr.
  reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.  


Theorem pointer_ofs_no_overflow:
forall ofs z, 
  (0 <= z)%Z ->
  (Ptrofs.unsigned ofs + int_size * z <= Ptrofs.max_unsigned )%Z ->
                        
                        Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size * z))) =
        (Ptrofs.unsigned ofs + int_size * z)%Z.
Proof.
  intros.
  unfold int_size in *; simpl size_chunk in *.
  assert (0 <=  Ptrofs.unsigned ofs)%Z by apply Ptrofs.unsigned_range_2.
  unfold Ptrofs.add.
  assert (0 <= size_chunk int_chunk)%Z by apply int_size_pos.
  rewrite Ptrofs.unsigned_repr with (z := (_ * z)%Z).
  rewrite Ptrofs.unsigned_repr. reflexivity.  

  split; auto. apply Z.add_nonneg_nonneg; auto. apply Z.mul_nonneg_nonneg; auto.
  split; auto. apply Z.mul_nonneg_nonneg; auto. 
  lia.
Qed.

   
 (* TODO: move to identifiers *)
Inductive bound_var_val: cps.val -> Ensemble var :=
| Bound_Vconstr :
    forall c vs v x, 
    bound_var_val v x ->
    List.In v vs ->
    bound_var_val (Vconstr c vs) x
| Bound_Vfun:
    forall fds rho x f,
    bound_var_fundefs fds x ->
    bound_var_val (Vfun rho fds f) x.

  
Inductive occurs_free_val: cps.val -> Ensemble var :=
| OF_Vconstr :
    forall c vs v x, 
    occurs_free_val v x ->
    List.In v vs ->
    occurs_free_val (Vconstr c vs) x
| OF_Vfun:
    forall fds rho x f,
      occurs_free_fundefs fds x ->
      M.get x rho = None ->
      occurs_free_val (Vfun rho fds f) x.


Definition closed_val (v : cps.val) : Prop :=
  Same_set var (occurs_free_val v) (Empty_set var).


Theorem closed_val_fun:
  forall fl f t vs e, 
    closed_val (Vfun (M.empty cps.val) fl f) ->
    find_def f fl = Some (t, vs, e) ->
    (Included _ (occurs_free e) (Ensembles.Union _  (FromList vs) (name_in_fundefs fl)) ).
Proof.
  intros. inv H. intro. intros.
  assert (~  occurs_free_val (Vfun (M.empty cps.val) fl f) x). intro. apply H1 in H3. inv H3.
  clear H1. clear H2.
  assert (decidable (List.In x vs)). apply In_decidable. apply var_dec_eq.
  assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
  inv H1; inv H2; auto. exfalso. 
  apply H3. constructor. Search occurs_free_fundefs find_def.
  eapply shrink_cps_correct.find_def_free_included. eauto. constructor. constructor. auto. auto. auto.
  apply M.gempty.
Qed.
  
  

Inductive dsubval_v: cps.val -> cps.val -> Prop :=
| dsubval_constr: forall v vs c,
  List.In v vs ->
  dsubval_v v (Vconstr c vs)
| dsubval_fun : forall x fds rho f,
  name_in_fundefs fds x ->
    dsubval_v (Vfun rho fds x) (Vfun rho fds f)
.

Definition subval_v := clos_trans _ dsubval_v.
Definition subval_or_eq := clos_refl_trans _ dsubval_v.


  
Theorem t_then_rt:
  forall A R (v v':A),
  clos_trans _ R v v'  ->
  clos_refl_trans _ R v v'.
Proof.
  intros. induction H.
  apply rt_step. auto.
  eapply rt_trans; eauto.
Qed.


Theorem rt_then_t_or_eq:
  forall A R (v v':A),
    clos_refl_trans _ R v v' ->
    v = v' \/ clos_trans _ R v v'.
Proof.
  intros. induction H.
  right. apply t_step; auto.
  left; auto.
  inv IHclos_refl_trans1; inv IHclos_refl_trans2.
  left; auto.
  right; auto.
  right; auto. right.
  eapply t_trans; eauto.
Qed.

Theorem dsubterm_case_cons:
  forall v l e',
    dsubterm_e e' (Ecase v l) -> 
  forall a, dsubterm_e e' (Ecase v (a:: l)).
Proof.
  intros. inv H. econstructor.
  right; eauto.
Qed.

  

Theorem subterm_case:
forall v l e', 
  subterm_e e' (Ecase v l) -> 
  forall a, subterm_e e' (Ecase v (a:: l)).
Proof.  
  intros. remember (Ecase v l) as y. revert dependent v. revert l. induction H.
  - intros. subst. constructor.
    eapply dsubterm_case_cons; eauto.
  - intros. apply IHclos_trans2 in Heqy.
    eapply t_trans. apply H. eauto.
Qed.


Theorem subval_fun: forall v rho fl x,
    name_in_fundefs fl x -> 
        subval_or_eq v (Vfun rho fl x) ->
        exists l, v = Vfun rho fl l /\ name_in_fundefs fl l.
Proof.
  intros. apply rt_then_t_or_eq in H0.
  inv H0.
  exists x; auto.
  remember (Vfun rho fl x) as y.
  assert (exists x, y = Vfun rho fl x /\ name_in_fundefs fl x ) by eauto.
  clear H. clear Heqy. clear x. 
  induction H1.  destructAll. subst. inv H. eauto.
  destructAll. 
  assert ( (exists x : var, Vfun rho fl x0 = Vfun rho fl x /\ name_in_fundefs fl x)) by eauto.
  apply IHclos_trans2 in H. apply IHclos_trans1 in H. auto.
Qed.  

Theorem subval_or_eq_constr:
forall v v' vs c,
  subval_or_eq v v' ->
  List.In v' vs ->
  subval_or_eq v (Vconstr c vs).
Proof.
  intros.
  eapply rt_trans; eauto.
  apply rt_step. constructor; auto.
Qed.


 
Theorem subval_v_constr:
  forall v vs t,
  subval_v v (Vconstr t vs) ->
  exists v',
    subval_or_eq v v' /\ List.In v' vs.
Proof.
  intros.
  remember (Vconstr t vs) as v'. revert t vs Heqv'.
  induction H; intros; subst. 
  - inv H. exists x. split.
    apply rt_refl. apply H2.
  -  specialize (IHclos_trans2 t vs eq_refl).
     destruct IHclos_trans2.
     exists x0. destruct H1. split.
     apply t_then_rt in H.
     eapply rt_trans; eauto.
     auto.
Qed.      
       
Theorem subval_or_eq_fun:
  forall rho' fds f vs t,
  subval_or_eq (Vfun rho' fds f) (Vconstr t vs) ->
  exists v',
    subval_or_eq (Vfun rho' fds f) v' /\ List.In v' vs.
Proof.
  intros.
  apply rt_then_t_or_eq in H. destruct H.
  inv H.
  eapply subval_v_constr; eauto.
Qed.  


Theorem bound_var_subval:
  forall x v v',
  bound_var_val v x ->
  subval_or_eq v v' -> 
  bound_var_val v' x.
Proof.
  intros. induction H0.
  - inv H0. econstructor; eauto.
    inv H. constructor. auto.
  - auto.
  - apply   IHclos_refl_trans2.
    apply   IHclos_refl_trans1.
    auto.
Qed.


(* bound_var_val - name_in_fds *)
Inductive bound_subvar_val : cps.val -> Ensemble var :=
    Bound_SVconstr : forall (c : ctor_tag) (vs : list cps.val) (v : cps.val) (x : var),
                    bound_var_val (Vconstr c vs) x -> bound_subvar_val (Vconstr c vs) x
  | Bound_SVfun : forall (fds : fundefs) (rho : cps.M.t cps.val) (x f : var),
      bound_var_val (Vfun rho fds f) x -> ~name_in_fundefs fds x -> bound_subvar_val (Vfun rho fds f) x. 


 
(* deep version of bound_subvar_val, likely what is needed for functions_not_bound inv *)
Inductive bound_notfun_val: cps.val -> Ensemble var :=
  Bound_FVconstr : forall (c : ctor_tag) (vs : list cps.val) 
                         (v : cps.val) (x : var),
                    bound_notfun_val v x ->
                    List.In v vs -> bound_notfun_val (Vconstr c vs) x
| Bound_FVfun : forall (e:exp) (fds : fundefs) (rho : cps.M.t cps.val) ys (x f f' : var) t,
    In _ (Ensembles.Union _ (FromList ys) (bound_var e)) x ->  find_def f' fds = Some (t, ys, e) ->  bound_notfun_val (Vfun rho fds f) x.


Theorem find_dsubterm:
  forall x t ys e fl,
find_def x fl = Some (t, ys, e) -> dsubterm_fds_e e fl.
Proof.
  induction fl; intros.
  - simpl in H. destruct (cps.M.elt_eq x v) eqn:Heq_xv. inv H. constructor.
    constructor 2. eapply IHfl; eauto.
  - inv H.
Qed.
      
Theorem bound_subvar_var: forall v x,
  bound_subvar_val v x -> bound_var_val v x.
Proof.
  intros. inv H; auto. 
Qed.

Theorem bound_notfun_var: forall v x,
  bound_notfun_val v x -> bound_var_val v x.
Proof.
  intros. induction H.
  - econstructor; eauto. 
  -  constructor. induction fds. simpl in H0.
     destruct  (cps.M.elt_eq f' v). inv H0. inv H. constructor; auto.     
     constructor 3; auto.
     constructor 2. auto.
     inv H0.
Qed.        


Theorem set_lists_In:
  forall {A} x xs (v:A) vs rho rho' ,
    List.In x xs ->
    M.get x rho' = Some v ->
    set_lists xs vs rho = Some rho' ->
    List.In  v vs.
Proof.
  induction xs; intros.
  -   inv H.
  - destruct vs. simpl in H1; inv H1. simpl in H1.
    destruct (set_lists xs vs rho) eqn:Hsl; inv H1.
    destruct (var_dec x a).     
    + subst. 
      rewrite M.gss in H0. inv H0. constructor; reflexivity.      
    + rewrite M.gso in H0 by auto.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.

Ltac inList := repeat (try (left; reflexivity); right).


Ltac solve_nodup :=
  let hxy := fresh "Hxy" in
  intro hxy; subst; try (clear hxy); 
repeat (match goal with
        | [H: NoDup _ |- _] => let h2 := fresh "Hnd" in
                               let h1 := fresh "HinList" in
                               let x := fresh "x" in
                               let l := fresh "l" in
                               inversion H as [h1 | x l h1 h2];
                               subst; clear H;
                               try (solve [apply h1; inList])
        end).

(**** Representation relation for LambdaANF values, expressions and functions ****)
Section RELATION.
 
  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).  
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).

  Definition protectedIdent: list ident := (argsIdent::allocIdent::limitIdent::gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).

  

  Variable cenv:cps.ctor_env.
  Variable fenv:cps.fun_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
  Variable p:program.
  
  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.
 
  
  Notation threadStructInf := (Tstruct threadInfIdent noattr).
  Notation threadInf := (Tpointer threadStructInf noattr).

  Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := None;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := None;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons val Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := None;
                                 cc_unproto := false;
                                 cc_structret := false |}).







Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).


Notation allocPtr := (LambdaANF_to_Clight.allocPtr allocIdent).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).



(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinf := (Etempvar tinfIdent threadInf).
Notation tinfd := (Ederef tinf threadStructInf).

Notation heapInf := (Tstruct heapInfIdent noattr).


Notation " a '+'' b " := (add a b) (at level 30).


Notation " a '-'' b " := (sub a b) (at level 30).


Notation " a '='' b " := (int_eq a b) (at level 35).


Notation "'!' a " := (not a) (at level 40).

Notation seq := Ssequence.

Notation " p ';' q " := (seq p q)
                         (at level 100, format " p ';' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).



Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z uval))) (at level 36). (* must be uval (integer), not val (pointer), for classify_add *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z uval))) (at level 36).

Definition int_shru z1 z2 := if Archi.ptr64 then (Vlong (Int64.shru (Int64.repr z1) (Int64.repr z2)))
                                                  else (Vint (Int.shru (Int.repr z1) (Int.repr z2))).

Definition int_and z1 z2 := if Archi.ptr64 then
                              (Vlong (Int64.and (Int64.repr z1) (Int64.repr z2))) else
                              (Vint (Int.and (Int.repr z1) (Int.repr z2))).

Ltac archi_red :=
  int_red;
  unfold sizeof in *;
  unfold int_chunk in *;
  unfold val in *;
  unfold uval in *;
  unfold val_typ in *;
  unfold Init_int in *;
  unfold make_vint in *;
  unfold make_cint in *;
  unfold int_shru in *;
  unfold int_and in *;
  unfold c_int in *;
  unfold uint_range in *;
  unfold Ctypesdefs.talignas, Ctypesdefs.tattr, Ctypesdefs.tptr, Ctypesdefs.tvoid, change_attributes in *;
  cbv beta iota in *;
  try (rewrite ptrofs_mu in *);
  (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H in *); try (cbv beta iota in *)
   end).

(* Reduces access_mode for pointer-based val type; call before constructor when assign_loc or deref_loc is needed *)
Ltac reduce_val_access :=
  try unfold Ctypes.access_mode;
  try unfold Clight.typeof;
  try unfold AST.Mptr;
  try (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H); try (cbv beta iota)
   end).

(* these ltac are agnostic on archi, useful for automation *)   
   Ltac ptrofs_of_int :=
     unfold Ptrofs.of_int64 in *;
     unfold ptrofs_of_int in *;
     unfold Ptrofs.of_intu in *;
     unfold Ptrofs.of_int in *.

   Ltac int_unsigned_repr :=
     try (rewrite Int64.unsigned_repr in *);
     try (rewrite Int.unsigned_repr in *).
          
   Ltac int_max_unsigned:=  
     unfold Int64.max_unsigned in *;
     unfold Int.max_unsigned in *.



 Inductive header_of_rep: ctor_rep -> Z -> Prop :=
 | header_enum: forall t, header_of_rep (enum t) (Z.of_N ((N.shiftl t 1) + 1))
 | header_boxed: forall t a, header_of_rep (boxed t a) (Z.of_N ((N.shiftl a 10) + t)).

 Function var_or_funvar_f' (n : nat) (x:positive):expr :=
   match Genv.find_symbol (Genv.globalenv p) x with
   | Some _ =>  makeVar threadInfIdent n x fenv finfo_env
   | None => var x
   end.
 
 Function var_or_funvar_f (x:positive):expr :=
   match Genv.find_symbol (Genv.globalenv p) x with
   | Some _ =>  makeVar threadInfIdent nParam x fenv finfo_env
   | None => var x
   end.
 
 (* The full the domain of map is exactly the symbols of globalenv *)
  Definition find_symbol_domain {A} (map:M.t A):=
   forall (x:positive), (exists V1, M.get x map = Some V1) <-> (exists b, Genv.find_symbol (Genv.globalenv p) x = Some b).

 Definition finfo_env_correct :=
   forall (x:positive) i t, M.get x finfo_env = Some (i , t) -> (exists finfo, M.get t fenv = Some finfo).
  
(* CHANGE THIS *)                                    
Inductive repr_asgn_fun': list positive -> list N -> statement -> Prop :=
| repr_asgn_nil: repr_asgn_fun' [] [] Sskip
| repr_asgn_cons: forall y ys i inf s, repr_asgn_fun' ys inf s ->
                 repr_asgn_fun' (y::ys) (i::inf) (s; args[ Z.of_N i ] :::= (var_or_funvar_f y)).

Inductive repr_asgn_fun: list positive -> list N -> statement -> Prop :=
  |repr_asgn_wrap: forall ys inf s, repr_asgn_fun' ys inf s ->
                   repr_asgn_fun ys inf (argsIdent ::= Efield tinfd argsIdent (Tarray uval maxArgs noattr);s).

Inductive repr_call_vars' (par : nat) : nat -> list positive -> list expr -> Prop :=
| repr_call_nil : repr_call_vars' par 0 [] []
| repr_call_cons : forall n y ys es, repr_call_vars' par n ys es ->
                                     repr_call_vars' par (S n) (y :: ys) (var_or_funvar_f' par y :: es).


Definition repr_call_vars : nat -> list positive -> list expr -> Prop := repr_call_vars' nParam.

(* like fromN but for Z, should move to list_util and make a generic one *)
Fixpoint fromZ (z:Z) (m:nat): list Z :=
  match m with
  | 0 => nil
  | S m' => z :: (fromZ (Z.succ z) m')
  end.

Fixpoint fromInt (i:int) (m:nat): list int :=
  match m with
  | 0 => nil
  | S m' => i :: (fromInt (Int.add i Int.one) m')
  end.


Theorem fromN_Some: forall x n z l ,
 nthN (fromN l z) n = Some x ->
 x = N.add l n.
Proof.  
  induction n using N.peano_rect; intros; simpl in H.
  - destruct z. simpl in H. inv H.
    simpl in H. inv H. 
    rewrite N.add_0_r. reflexivity.
  - destruct z. simpl in H. inv H.
    simpl in H. (destruct (N.succ n) eqn:Sn). apply N.neq_succ_0 in Sn.  inv Sn.
    assert (n = (N.sub (N.pos p0)  1)).
    rewrite <- Sn. rewrite <- N.pred_sub.
    symmetry. apply N.pred_succ.
    rewrite <- H0 in H.
    apply IHn in H. rewrite <- Sn.
    rewrite N.add_succ_l in H.
    rewrite N.add_succ_r. auto.
Qed. 
    


Definition Forall_in_mem_block {A} : (A -> (block *  int) -> Prop) -> list A -> (block * int) -> int -> Prop :=
  fun P ls loc z =>
    let (b, z0) := loc in
    let ids := fromN 0%N  (length ls) in 
    Forall2 (fun a i => P a (b, Int.add z0 (Int.mul (Int.repr (Z.of_N i)) z))) ls ids.


Theorem Forall_in_mem_block_nthN :
  forall {A P vs b i z v n},
     Forall_in_mem_block P vs  (b, i) z -> 
     @nthN A vs n = Some v ->
     P v (b, Int.add i (Int.mul (Int.repr (Z.of_N n)) z)).
Proof.
  intros. unfold Forall_in_mem_block in H.
  assert (Hf2 := Forall2_nthN _ _ _ _ _ H H0).
  destruct Hf2. destruct H1.
  apply fromN_Some in H1. simpl in H1. subst; assumption.
Qed.  

Inductive Forall_statements_in_seq' {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> BinNums.Z -> Prop :=
| Fsis_last: forall (R: (BinNums.Z  -> A -> statement -> Prop)) n v s, R n v s -> Forall_statements_in_seq' R [v] s n
| Fsis_cons: forall R v vs s s' n, Forall_statements_in_seq' R vs s' (Z.succ n) ->
                                   R n v s ->  Forall_statements_in_seq' R (v::vs) (s; s') n.



Inductive Forall_statements_in_seq_rev {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> nat -> Prop :=
| Fsir_last: forall (R: (BinNums.Z  -> A -> statement -> Prop)) v s, R 0%Z v s -> Forall_statements_in_seq_rev R [v] s 0
| Fsir_cons: forall R v vs s s' n, Forall_statements_in_seq_rev R vs s' n ->
                                   R (Z.of_nat (S n)) v s ->  Forall_statements_in_seq_rev R (v::vs) (s; s') (S n).




(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > list cannot be empty (o.w. no statement)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A}: (BinNums.Z  -> A -> statement -> Prop) ->  list A -> statement -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s (0%Z).

(* This should sync with makeVar *)
Inductive var_or_funvar : positive -> expr -> Prop :=
| F_VoF : forall x b,
    Genv.find_symbol (Genv.globalenv p) x = Some b ->
                var_or_funvar x (makeVar threadInfIdent nParam x fenv finfo_env)
| V_VoF : forall x,
    Genv.find_symbol (Genv.globalenv p) x = None ->
       var_or_funvar x (var x).

Theorem var_or_funvar_of_f:
  forall x e,
  var_or_funvar x e <-> var_or_funvar_f x = e.
Proof.
  unfold var_or_funvar_f; split; intro.
  inv H;  rewrite H0; auto. 
  destruct ( Genv.find_symbol (Genv.globalenv p) x) eqn:Hx; subst; econstructor; eauto.
Qed.
  
Fixpoint Vint_or_Vptr (v:Values.val): bool :=
  match v with
  | Vint _ => negb Archi.ptr64 
  | Vlong _ => Archi.ptr64 
  | Vptr _ _ => true
  | _ => false
  end.

Inductive get_var_or_funvar (lenv: temp_env): positive -> Values.val -> Prop :=
|F_gVoF:
   forall b x,
     Genv.find_symbol (Genv.globalenv p) x = Some b ->
   get_var_or_funvar lenv x (Vptr b (Ptrofs.repr 0%Z))
| V_gVoF:
    forall x v,
      Genv.find_symbol (Genv.globalenv p) x = None -> 
      M.get x lenv = Some v ->
      Vint_or_Vptr v = true -> 
      get_var_or_funvar lenv x v.
 
(* goes through a lists of positive l and returns a lists of Values vs for which 
 Forall2 (get_var_or_fun lenv) l vs *)
Fixpoint get_var_or_funvar_list (lenv:temp_env) (l:list positive): option (list (Values.val)) :=
  match l with
  | nil => Some nil
  | x::ls =>
    (match get_var_or_funvar_list lenv ls with
     | Some vs =>
       (match Genv.find_symbol (Genv.globalenv p) x with
        | Some b => Some ((Vptr b Ptrofs.zero)::vs)
        | None =>
          (match (M.get x lenv) with
           | Some v =>
             (match v with
              | Vint _ => if Archi.ptr64 then None else Some (v::vs)
              | Vlong _ => if Archi.ptr64 then Some (v::vs) else None
              | Vptr _ _ => Some (v::vs)
              | _ => None
              end)
           | None => None
           end)
        end)
     | None => None
     end)
  end.


Lemma get_var_or_funvar_list_correct1:
  forall lenv l vs, 
  get_var_or_funvar_list lenv l = Some vs ->
  Forall2 (get_var_or_funvar lenv) l vs.
Proof.
  induction l; intros.
  simpl in H. inv H. constructor.
  simpl in H.
  destruct (get_var_or_funvar_list lenv l)  eqn:gvl.
  specialize (IHl l0 eq_refl).
  destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:gfpa.
  - inv H.
    constructor; auto.
    left; auto.
  - destruct  (M.get a lenv) eqn:gal. 
    destruct v; inv H.
    destruct (Archi.ptr64) eqn:Harch; constructor. right; auto. auto.
    constructor; auto. auto.
    constructor; auto. right;  auto.  inv H.
  - inv H.
Qed.

Theorem get_var_or_funvar_list_correct2:
  forall lenv l vs, 
    Forall2 (get_var_or_funvar lenv) l vs    ->
    get_var_or_funvar_list lenv l = Some vs. 
Proof.
  induction l; intros.
  - inv H. reflexivity.
  - inv H. apply IHl in H4. simpl. rewrite H4.    
    inv H2.
    rewrite H.
    reflexivity.
    rewrite H. rewrite H0. destruct y; inv H1; auto.
Qed.

Theorem get_var_or_funvar_list_correct:
  forall lenv l vs, 
  Forall2 (get_var_or_funvar lenv) l vs    <->
    get_var_or_funvar_list lenv l = Some vs. 
Proof.
  split. apply get_var_or_funvar_list_correct2.
  apply get_var_or_funvar_list_correct1.
Qed.

(* can be strenghten to lenv maps that are equal over l *)
Theorem get_var_or_funvar_list_set:
  forall lenv x v l,
    ~ List.In x l ->
              get_var_or_funvar_list lenv l = get_var_or_funvar_list (M.set x v lenv) l.
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. rewrite M.gso. rewrite IHl. reflexivity.
    intro. apply H. constructor 2. auto. intro; apply H.
    constructor; auto.
Qed.
 

Theorem Forall2_length':
  forall A B (R:A -> B -> Prop) l l',
  Forall2 R l l' ->
  length l = length l'.
Proof.
  induction l; intros. inv H. auto.
  inv H. apply IHl in H4. simpl; auto.
Qed.  
  
Theorem get_var_or_funvar_list_same_length:
  forall lenv l vs,
  get_var_or_funvar_list lenv l = Some vs ->
  length l = length vs.
Proof.
  intros. 
  apply get_var_or_funvar_list_correct in H.
  apply Forall2_length' in H.
  auto.
Qed.


Definition map_get_r_l: forall t l, relation (M.t t) := 
  fun t l => fun sub sub' => forall v,
               List.In v l ->
               M.get v sub = M.get v sub'.

Theorem get_var_or_funvar_proper:
  forall lenv lenv' l x v,
  get_var_or_funvar lenv x v ->
  map_get_r_l _ l lenv lenv' ->
  List.In x l -> 
  get_var_or_funvar lenv' x v.
Proof.
  intros.
  inv H. constructor; auto.
  constructor 2; auto. erewrite <- H0; auto.
Qed.

Theorem get_var_or_funvar_int_or_ptr:
  forall lenv y v7,
    get_var_or_funvar lenv y v7 ->
    Vint_or_Vptr v7 = true.
Proof.
  intros. inv H. auto.
  auto.
Qed.


Theorem get_var_or_funvar_list_proper:
  forall lenv lenv' l vs, 
  get_var_or_funvar_list lenv l = Some vs ->
  map_get_r_l _ l lenv lenv' ->
  get_var_or_funvar_list lenv' l = Some vs.
Proof.
  induction l; intros.
  simpl. simpl in H. auto.
  simpl in H.
  destruct (get_var_or_funvar_list lenv l) eqn:Hgll.
  assert ( Some l0 = Some l0) by reflexivity.
  assert (map_get_r_l Values.val l lenv lenv'). intro; intros.
  apply H0. constructor 2; auto.
  specialize (IHl _ H1 H2).
  simpl. rewrite IHl.
  destruct  (Genv.find_symbol (Genv.globalenv p) a).
  auto.
  rewrite <- H0. auto.
  constructor. auto.
  inv H.
Qed. 
  
Inductive is_nth_projection_of_x : positive -> Z -> positive -> statement -> Prop :=
  Make_nth_proj: forall x  n v e,
                         var_or_funvar v  e ->
                          is_nth_projection_of_x x n v (Field(var x, n) :::=  e).


(* this version of mem_after_n_proj casts to match is_nth_projection *)
Inductive mem_after_n_proj_store_cast : block -> Z -> (list Values.val) -> Z -> mem -> mem ->  Prop :=
| Mem_last_c:
    forall m b ofs i v m',
    Mem.store int_chunk m b  (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size*i)))) v = Some m' ->
    mem_after_n_proj_store_cast b ofs [v] i m m'
| Mem_next_c:
    forall m b ofs i v m' m'' vs,
      Mem.store int_chunk m b (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size*i)))) v = Some m' ->
      mem_after_n_proj_store_cast b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store_cast b ofs (v::vs) i m m''. 


Inductive mem_after_n_proj_store : block -> Z -> (list Values.val) -> Z -> mem -> mem ->  Prop :=
| Mem_last:
    forall m b ofs i v m',
    Mem.store int_chunk m b  (ofs + (int_size*i)) v = Some m' ->
    mem_after_n_proj_store b ofs [v] i m m'
| Mem_next:
    forall m b ofs i v m' m'' vs,
      Mem.store int_chunk m b (ofs + (int_size*i)) v = Some m' ->
      mem_after_n_proj_store b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store b ofs (v::vs) i m m''. 

(* represent work "already done" while consuming mem_after_n_proj *)
Inductive mem_after_n_proj_snoc :  block -> Z -> (list Values.val)  -> mem -> mem ->  Prop :=
| Mem_nil_snoc: forall m b ofs, 
    mem_after_n_proj_snoc b ofs [] m m
| Mem_cons_snoc: forall m b ofs m' m'' v vs,
    mem_after_n_proj_snoc b ofs vs m m' ->
    Mem.store int_chunk m' b (ofs + (int_size*(Z.of_nat (length vs)))) v = Some m'' ->
    mem_after_n_proj_snoc b ofs (v::vs) m m''.




Theorem  mem_after_n_proj_store_snoc:
  forall b ofs vs1 m m1, 
  mem_after_n_proj_snoc b ofs vs1 m m1 ->
forall vs2 m',
  mem_after_n_proj_store b ofs vs2 (Z.of_nat (length vs1)) m1 m' ->
  forall vs,
    List.app (rev vs1) vs2 = vs -> 
    mem_after_n_proj_store b ofs vs 0 m m'.
Proof.
  induction vs1; intros.
  - simpl in H1; subst. simpl in H0. inv H. auto.
  -   simpl in H1. inv H.
      rewrite <- app_assoc. eapply IHvs1. apply H6. 2: reflexivity.
      simpl.
      simpl length in H0. rewrite Nat2Z.inj_succ in H0.
      econstructor; eauto.
Qed.
 
Theorem  mem_after_n_proj_store_snoc':
  forall b ofs vs m m',
    mem_after_n_proj_store b ofs vs 0 m m' ->
    forall vs1 vs2,
      vs2 <> nil ->
      List.app (rev vs1) vs2 = vs ->
      exists m1, 
  mem_after_n_proj_snoc b ofs vs1 m m1 /\ 
  mem_after_n_proj_store b ofs vs2 (Z.of_nat (length vs1)) m1 m'.
Proof.
  intros b ofs vs m m' Hmm'.
  induction vs1; intros.
  -  simpl in H0; subst. exists m. simpl. split.
     constructor. auto.
  - simpl in H0. rewrite <- app_assoc in H0. apply IHvs1 in H0. destruct H0. destruct H0.
    simpl in H1.
    inv H1. (* impossible, vs2 is not empty *)  exfalso; auto.
    exists m'0. split. econstructor; eauto. simpl length. rewrite Nat2Z.inj_succ. auto. intro. inv H1.
Qed.    
      
    


  (*
todo:
Theorem mem_after_n_proj_store_snoc:
  forall b ofs,
  forall vs1 vs2, 
    List.app (rev vs1) vs2 = vs ->
    forall vs m m' i,
      mem_after_n_proj_store b ofs vs i m m' ->
      exists m1,
        mem_after_n_proj_snoc b ofs vs1 m m1  /\
        mem_after_n_proj_store b ofs vs2 (Z.of_nat (length (rev vs1))) m1 m'.
*)
    
      
Theorem mem_after_n_proj_wo_cast:
  forall vs b ofs i m m', 

  (0 <= ofs)%Z -> (0 <= i)%Z ->
   (uint_range (ofs+int_size*(i+(Z.of_nat (length vs)))))%Z ->
      mem_after_n_proj_store_cast b ofs vs i m m' <-> mem_after_n_proj_store b ofs vs i m m'. 
Proof.
  induction vs; intros.
  { (* impossible *) split; intro; inv H2. }
  assert (ofs + int_size * i  = Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr (int_size * i))))%Z.
  assert (0 <=  int_size * (i + Z.of_nat (length (a::vs)))<= Ptrofs.max_unsigned)%Z.
  unfold int_size in *. simpl size_chunk in *.
  inv H1. assert (Hisp := int_size_pos).
  split. apply Z.mul_nonneg_nonneg; auto.  lia. lia.
  rewrite Ptrofs.add_unsigned.
  unfold int_size in *.
  simpl size_chunk in *.
  inv H1.
  rewrite Ptrofs.unsigned_repr with (z := ofs).
  rewrite Ptrofs.unsigned_repr with (z := (_ * i)%Z).
  rewrite Ptrofs.unsigned_repr.
  reflexivity. split.
  assert (Hisp := int_size_pos).
  apply Z.add_nonneg_nonneg; auto. 
  apply Z.mul_nonneg_nonneg; auto.
  chunk_red; lia.
  chunk_red; lia.
  lia.
  simpl length in H1.
  rewrite Nat2Z.inj_succ in H1.  
  rewrite Z.add_succ_r in H1.
  split; intro; inv H3.
  - constructor. rewrite H2. auto.
  - econstructor. rewrite H2. apply H8.
    rewrite <- IHvs; auto. lia.
    rewrite Z.add_succ_l.
    apply H1.    
  - constructor. rewrite <- H2. auto.
  - econstructor. rewrite <- H2. apply H8.
    rewrite IHvs; auto. lia.
    rewrite Z.add_succ_l.
    apply H1.
Qed. 


(* mem_after_n_proj_store_load *)

Theorem mem_after_n_proj_store_load:
  forall b ofs vs i m m', 
    mem_after_n_proj_store b ofs vs i m m' ->
    forall ofs' b',
      ( b' <> b \/
        (ofs' + int_size <= ofs + int_size * i)%Z \/
        (ofs + int_size * (1+(i+(Z.of_nat (length vs)))) <= ofs')%Z) ->
      Mem.load int_chunk m' b' ofs' = Mem.load int_chunk m b' ofs'.
Proof.
  induction vs; intros; inv H.
  - eapply Mem.load_store_other.
    apply H8.
    unfold int_size in *.
    simpl length in H0. simpl Z.of_nat in H0.
    inv H0; auto.
    inv H; auto.
    right; right.
    simpl size_chunk in H0. assert (Hisp := int_size_pos). lia.
  - eapply IHvs in H9.
     symmetry.
     erewrite <- Mem.load_store_other.  
     symmetry. apply H9. apply H5.
     { destruct H0; auto.
       unfold int_size in *.
       destruct H; auto.
       right. right.
       simpl length in H.
       rewrite Nat2Z.inj_succ in H.
       chunk_red ; lia. 
     }
     {
       assert (Hisp := int_size_pos). 
       unfold int_size in *.
       simpl size_chunk in *.
       simpl length in H0.
       rewrite Nat2Z.inj_succ in H0.
       destruct H0; auto.
       destruct H. right. left. chunk_red; lia. 
       right. right. chunk_red; lia. 
     }
Qed.

 
(* mem_after_n_proj_store on area in comp(L) leaves m unchanged on L (or any area unaffected by the proj stored *)
Theorem mem_after_n_proj_store_unchanged:
  forall L b ofs vs i m m',
    mem_after_n_proj_store b ofs vs i m m' ->
  (forall j, (ofs+int_size*i) <= j < ofs+int_size*(i + Z.of_nat (length vs)) ->  ~ L b j)%Z -> 
  Mem.unchanged_on L m m'.
Proof.
  induction vs; intros; inv H.
  - eapply Mem.store_unchanged_on; eauto.
    intros.
    apply H0.
    unfold int_size in *.
    simpl length. simpl Z.of_nat.    
    chunk_red; lia.
  - apply Mem.unchanged_on_trans with (m2 := m'0).
    + eapply Mem.store_unchanged_on; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      lia.
    + eapply IHvs; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      lia.
Qed.

Theorem mem_after_n_proj_snoc_unchanged:
  forall L b ofs vs  m m',
    mem_after_n_proj_snoc b ofs vs m m' ->
  (forall j, ofs <= j < ofs+int_size*(Z.of_nat (length vs)) ->  ~ L b j)%Z -> 
  Mem.unchanged_on L m m'.
Proof.
  induction vs.
  - intros. inv H. apply Mem.unchanged_on_refl.
  - intros. inv H.
    apply Mem.unchanged_on_trans with (m2 := m'0).
    + apply IHvs in H5; auto.
      simpl length in H0.
      rewrite Nat2Z.inj_succ in H0.        intros. apply H0. chunk_red; lia.
    + eapply Mem.store_unchanged_on; eauto.
      intros.
      simpl length in H0.
      rewrite Nat2Z.inj_succ in H0. intros. apply H0. chunk_red;
      lia. 
Qed.


Definition prefix_ctx {A:Type} rho' rho :=
  forall x v, M.get x rho' = Some v -> @M.get A x rho = Some v.



(* keep around the fact that t is no bigger than 2^(int_size-1) [which we know by correct_crep] *)
 Definition repr_unboxed_Codegen: N -> Z -> Prop :=
   fun t => fun h =>
              (h = (Z.shiftl (Z.of_N t) 1) + 1)%Z /\
              (0 <= (Z.of_N t)  <  Ptrofs.half_modulus )%Z.

 Theorem repr_unboxed_eqm: forall h t,
     repr_unboxed_Codegen t h -> 
   Ptrofs.eqm h (Z.of_N ((N.shiftl t 1) + 1)).
 Proof.
   intros. inv H.
   rewrite OrdersEx.Z_as_DT.shiftl_mul_pow2; try lia.
   simpl.
   rewrite N.shiftl_mul_pow2.
   rewrite N2Z.inj_add.
   rewrite N2Z.inj_mul.
   simpl.
   rewrite Z.pow_pos_fold.
   rewrite Pos2Z.inj_pow.  apply Ptrofs.eqm_refl.
 Qed.   
 Search Int.max_signed.

 Theorem nat_shiftl_p1:
   forall n z,
     1 < z ->
 n  < (z / 2) ->
 n * 2 + 1 < z.
 Proof.
   induction n; intros.
   simpl. auto.
   simpl.
   destruct z. inv H0. destruct z.
   - inv H0. 
   - rewrite <- Nat.div2_div in H0. simpl in H0. rewrite Nat.div2_div in H0. 
     apply Nat.succ_lt_mono in H0.
     assert (Hz := Nat.lt_decidable 1 z). inv Hz.
     specialize (IHn _ H1 H0). lia.
     destruct z.
       (* case 0 *) inv H0. inv H.
     destruct z.
     (* case 1 *) inv H0. 
     exfalso. apply H1. lia.
 Qed.

 Theorem pos_nat_div2 : forall p,
    p <> xH ->
  Pos.to_nat (Pos.div2 p) = Nat.div2 (Pos.to_nat p).
 Proof.
   intros. destruct p0.
   - simpl Pos.div2.
     rewrite Pos2Nat.inj_xI.
     rewrite Nat.div2_succ_double. reflexivity.
   - simpl Pos.div2.
     rewrite Pos2Nat.inj_xO.
     rewrite Nat.div2_double. reflexivity.
   - exfalso. apply H; auto.
 Qed.
 
 Theorem Div2_Z_to_nat: forall n,
     (0 <= n)%Z ->
    Z.to_nat (Z.div2 n) = Nat.div2 (Z.to_nat n).
 Proof.
   induction n; intros.
   - reflexivity.
   -  simpl. destruct p0.
      rewrite Z2Nat.inj_pos. 
      rewrite pos_nat_div2. reflexivity.
      intro. inv H0.
      rewrite Z2Nat.inj_pos. 
      rewrite pos_nat_div2. reflexivity.
      intro. inv H0.
      reflexivity.      
   - exfalso. lia.
 Qed.
   
   
   
 Theorem repr_unboxed_header_range:
   forall t h,
     repr_unboxed_Codegen t h ->
     (0 <= h <= Ptrofs.max_unsigned)%Z.
 Proof. 
   intros. inv H.   
   unfold Ptrofs.max_unsigned.
   unfold Ptrofs.half_modulus in *.
   
   unfold Ptrofs.modulus in *.
   rewrite OrdersEx.Z_as_DT.shiftl_mul_pow2; try lia.
   rewrite Z.pow_1_r.
   split; try lia.

   rewrite Z.sub_1_r.
   rewrite <- Z.lt_le_pred.
   destruct H1.
   unfold Ptrofs.wordsize in *. unfold Wordsize_Ptrofs.wordsize in *. 
   assert (Hws:(0 <= Zpower.two_power_nat (if Archi.ptr64 then 64%nat else 32%nat))%Z).
   {     
     assert (Hws' := Coqlib.two_power_nat_pos (if Archi.ptr64 then 64%nat else 32%nat)). lia.
   }
   rewrite Z2Nat.inj_lt; try lia. rewrite Z2Nat.inj_lt in H0; try lia.
   rewrite Z2Nat.inj_add in * by lia.
   rewrite Z2Nat.inj_mul in * by lia.
   rewrite <- Z.div2_div in H0.
   rewrite Div2_Z_to_nat in H0.
   rewrite Nat.div2_div in H0.
   eapply nat_shiftl_p1.
   chunk_red; simpl; rewrite <- Pos2Nat.inj_1;
     apply nat_of_P_lt_Lt_compare_morphism; auto.
   auto. auto.
 Qed.



 Theorem repr_unboxed_shiftr:
   forall t h, 
   repr_unboxed_Codegen t h ->
   Z.shiftr h 1 =  Z.of_N t.
 Proof.
   intros.
   inv H.
   rewrite Zshiftl_mul_two_p by lia.
   unfold Z.shiftr. 
   simpl Z.shiftl.
   unfold Zpower.two_power_pos. simpl.
   rewrite Zdiv.Zdiv2_div. 
   replace (Z.of_N t * 2 + 1)%Z with (OrdersEx.Z_as_OT.b2z true + 2 * (Z.of_N t))%Z by (simpl OrdersEx.Z_as_OT.b2z; lia).
   apply OrdersEx.Z_as_OT.add_b2z_double_div2.
Qed.
 

Definition boxed_header: N -> N -> Z -> Prop :=
  fun t => fun a =>  fun h =>
                       (h =  (Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z /\
                       (0 <= Z.of_N t <  Zpower.two_power_pos 8)%Z /\
                       (0 <= Z.of_N a <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z.

Theorem repr_boxed_header_range:
   forall t a h,
     boxed_header t a h ->
     (0 <= h <= Ptrofs.max_unsigned)%Z.
 Proof.
   intros. inv H.
   rewrite  OrdersEx.Z_as_DT.shiftl_mul_pow2.
   destruct H1.
   rewrite Zpower.two_power_pos_correct in *.
   rewrite Zpower.two_power_nat_correct in *.
   simpl in *.
   unfold Z.pow_pos in *.
   2: lia.
   split. 
   - apply Z.add_nonneg_nonneg.
     apply Z.mul_nonneg_nonneg. lia. simpl; lia.
     lia.
   - (* moving to pos then computing by archi *)
     unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. 
     unfold Ptrofs.wordsize in *.
     unfold Wordsize_Ptrofs.wordsize in *. 
     chunk_red; simpl in *. lia. lia.
Qed. 
 
Theorem div2_iter_pos:
  forall p0 a, 
    (0 <= a -> 0 <= Pos.iter Z.div2 a p0)%Z.
Proof.
  induction p0; intros.
  - simpl.
    rewrite OrdersEx.Z_as_OT.div2_nonneg.
    apply IHp0. apply IHp0. auto.
  - simpl. apply IHp0. apply IHp0.
    auto.
  - simpl; rewrite OrdersEx.Z_as_OT.div2_nonneg; auto.
Qed.


Theorem mul2_iter_pos:
  forall p0 a, 
    (0 <= a -> 0 <= Pos.iter (Z.mul 2) a p0)%Z.
Proof.
  induction p0; intros.
  - simpl. destruct (Pos.iter (Z.mul 2) (Pos.iter (Z.mul 2) a p0) p0) eqn:Hp.
    * reflexivity.
    * apply Pos2Z.is_nonneg.
    * exfalso.
      assert (0 <=  Pos.iter (Z.mul 2) (Pos.iter (Z.mul 2) a p0) p0)%Z.
      apply IHp0. apply IHp0. auto.
      rewrite Hp in H0.
      assert (Hneg := Pos2Z.neg_is_neg p1).
      lia.
  - simpl. apply IHp0. apply IHp0. auto.
  - simpl. destruct a; try lia.
    all: try apply Pos2Z.is_nonneg.
    all: try (exfalso; assert (Hneg := Pos2Z.neg_is_neg p0); lia).
Qed.


Theorem pos_iter_xI: forall A f (a:A) p,
  Pos.iter f (a)%Z p~1 = f (Pos.iter f (Pos.iter f a p)%Z p).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem pos_iter_xH: forall A f (a:A),
  Pos.iter f (a)%Z 1 = f a.
Proof.
  intros. simpl. reflexivity.
Qed.
 
Theorem pos_iter_xO: forall A f (a:A) p,
  Pos.iter f (a)%Z p~0 = (Pos.iter f (Pos.iter f a p)%Z p).
Proof.
  intros. simpl. reflexivity.
Qed.

Search Z.div2 Z.add.


Theorem div2_even_add:
  forall a b,
    (Z.odd a = false ->
   Z.div2 (a + b) = Z.div2 a + Z.div2 b)%Z.
Proof.
  intros.
  repeat (rewrite Z.div2_div).
  rewrite Z.div2_odd with (a := b).
  rewrite Z.add_assoc.
  rewrite Z.add_carry_div2.
  rewrite <- Z.div2_odd with (a := b).
  repeat (rewrite Z.bit0_odd).
  rewrite H.
  rewrite <- Z.bit0_odd.
  rewrite Z.testbit_even_0.
  replace  (Z.b2z (false && false || Z.odd b && (false || false))) with 0%Z.
  rewrite Z.mul_comm.
  rewrite Zdiv.Z_div_mult. 
  rewrite Z.add_0_r.
  rewrite Z.div2_div. reflexivity.
  lia.
  destruct (Z.odd b); simpl; reflexivity.
Qed.



Theorem shiftl_add_nonneg:
  forall c a b,
   ( 0 <= a ->
    0 <= b ->
     0 <= c ->
    Z.shiftl (a + b) c = Z.shiftl a c + Z.shiftl b c)%Z.
Proof. 
  destruct c; intros.
  reflexivity.
  - simpl.
    revert dependent a. revert dependent b.
    clear H1. revert p0.
    induction p0; intros. 
    + do 3 (rewrite pos_iter_xI).
      rewrite <- Z.mul_add_distr_l.
      rewrite <- IHp0.
      rewrite <- IHp0.
      reflexivity.
      auto. auto.
      apply mul2_iter_pos; auto.
      apply mul2_iter_pos; auto.
    + simpl. rewrite IHp0.
      rewrite IHp0.
      reflexivity.
      apply mul2_iter_pos; auto.
      apply mul2_iter_pos; auto.
      auto. auto.
    + do 3 (rewrite pos_iter_xH).
      apply Z.mul_add_distr_l.
  - simpl.
    exfalso.
    assert (Hneg := Pos2Z.neg_is_neg p0). lia.
Qed.



Theorem iter_div_testbit_decompose:
  (forall c a b,
      (forall d, (0 <= d < (Z.pos c))%Z ->
                 Z.testbit a d = false) ->
      Pos.iter Z.div2 (a + b) c =
      Pos.iter Z.div2 a c + Pos.iter Z.div2 b c)%Z.
Proof.
  induction c; intros.
  - do 3 (rewrite pos_iter_xI).
    assert (Hrw := Z.shiftr_spec).
    rewrite IHc.
    rewrite IHc.
    rewrite div2_even_add. reflexivity.
    rewrite <- Z.bit0_odd. 
    assert (Hrw' := Hrw).
    specialize (Hrw (Pos.iter Z.div2 a c) (Z.pos c)).
    unfold Z.shiftr in Hrw. simpl in Hrw.
    rewrite Hrw by lia.
    specialize (Hrw' a (Z.pos c)). rewrite Hrw'.
    simpl Z.add.
    apply H. split.
    apply Pos2Z.pos_is_nonneg.
    rewrite Pos.add_diag.
    rewrite Pos2Z.inj_xI.
    rewrite Pos2Z.inj_xO. lia.
    simpl.
    apply Pos2Z.pos_is_nonneg.
    specialize (Hrw a (Z.pos c)).
    unfold Z.shiftr in Hrw. simpl in Hrw.
    intros. 
    rewrite Hrw. apply H.
    rewrite Pos2Z.inj_xI.
    lia. lia.
    intros. apply H.
    rewrite Pos2Z.inj_xI. lia.
  - rewrite pos_iter_xO.    
    rewrite IHc.
    rewrite pos_iter_xO.
    rewrite pos_iter_xO.
    2:{ intros. apply H.
    rewrite Pos2Z.inj_xO.
    assert (0 < Z.pos c)%Z by apply Pos2Z.is_pos.
    lia. }
    rewrite IHc. reflexivity.
    intros.
    assert (Hrw := Z.shiftr_spec).
    specialize (Hrw a (Z.pos c)). unfold Z.shiftr in Hrw.
    simpl in Hrw.  rewrite Hrw. 
    2:{ destruct H0. auto. }
    apply H.
    rewrite Pos2Z.inj_xO. lia.
  - repeat (rewrite pos_iter_xH).
    rewrite div2_even_add. reflexivity.
    rewrite <- Z.bit0_odd.
    apply H. lia.
Qed.

Corollary shiftr_testbit_decompose:
  (forall c a b,
      (forall d, (0 <= d < (Z.pos c))%Z ->
                 Z.testbit a d = false) ->
      Z.shiftr (a + b) (Z.pos c) =
      Z.shiftr a (Z.pos c) + Z.shiftr b (Z.pos c))%Z.
Proof.
  intros. unfold Z.shiftr. simpl.
  apply iter_div_testbit_decompose; auto.
Qed.

 
Theorem shiftr_bounded_decompose:
  forall a b c,
  (0 <= a ->
  0 < c ->
  (0 <= b < Zpower.two_p c) ->
  Z.shiftr ((Z.shiftl a c) + b) c = a)%Z.
Proof.
  intros.
  destruct c.
  (* impossible cases *)
  inv H0.
  2:{ exfalso.
  assert (Hneg:= Pos2Z.neg_is_neg p0). lia. }
  rewrite shiftr_testbit_decompose.
  rewrite Z.shiftr_shiftl_l.
  rewrite Z.sub_diag. simpl.
  
  rewrite Zshiftr_div_two_p.
  rewrite Zdiv.Zdiv_small. lia.
  auto.
  lia.
  lia.
  intros.
  apply Z.shiftl_spec_low. destruct H2. auto.
Qed.

Theorem repr_boxed_a:
   forall a t h, 
     boxed_header t a h ->
   Z.shiftr h 10 =  Z.of_N a.
Proof.
  intros.
  inv H.
  destructAll.
  rewrite shiftr_bounded_decompose; auto.
  lia. simpl.
  split; auto.  
  rewrite Zpower.two_power_pos_equiv in *.
  simpl in *. unfold Z.pow_pos in *. simpl in *.
  lia.
Qed.

Theorem pos_testbit_impossible:
  forall b, 
  ~ (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  induction b; intro.
  - apply IHb; intros.
    assert ( 0 <= 0)%N by reflexivity.
    apply H in H1. inv H1.
  - apply IHb.
    intros.    
    simpl in H.    
    assert (0 <= (N.pos (N.succ_pos d)))%N.
    apply N.lt_le_incl.
    unfold N.lt. reflexivity. 
    apply H in H1.
    rewrite N.pos_pred_succ in H1.
    auto.
  - assert (0 <= 0)%N.
    reflexivity.
    apply H in H0. inv H0.    
Qed.

Theorem pos_testbit_nat_impossible:
  forall b,
  ~(forall d : nat, 0 <= d -> Pos.testbit_nat b d = false).
Proof.
  induction b; intro.
  - apply IHb; intros.
    assert ( 0 <= 0) by reflexivity.
    apply H in H1. inv H1.
  - apply IHb.
    intros.    
    simpl in H.    
    assert (0 <= S d) by lia.
    apply H in H1.
    auto.
  - assert (0 <= 0).
    reflexivity.
    apply H in H0. inv H0.    
Qed.

Theorem N_lt_pos:  
  forall p, (0 < N.pos p)%N.
Proof.
  intro.
  apply N2Z.inj_lt.
  simpl.
  apply Pos2Z.is_pos.
Qed.
     
Theorem pos_testbit_false_xI:
  forall b, 
  (forall d : N, (1 <= d)%N -> Pos.testbit b~1 d = false) ->
  (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  intros.
  assert (1 <= (N.pos (N.succ_pos d)))%N.
  apply N2Z.inj_le.
  apply Z.lt_pred_le.
  simpl.
  apply Pos2Z.is_pos.   
  apply H in H1.
  simpl in H1.
  rewrite N.pos_pred_succ in H1.
  auto.
Qed.  
 
Theorem pos_testbit_false_xO:
  forall b, 
  (forall d : N, (1 <= d)%N -> Pos.testbit b~0 d = false) ->
  (forall d : N, (0 <= d)%N -> Pos.testbit b d = false).
Proof.
  intros.
  assert (1 <= (N.pos (N.succ_pos d)))%N.
  apply N2Z.inj_le.
  apply Z.lt_pred_le.
  simpl.
  apply Pos2Z.is_pos.   
  apply H in H1.
  simpl in H1.
  rewrite N.pos_pred_succ in H1.
  auto.
Qed.



Theorem pland_split_nat:
  forall c a b,
  (forall d, d < c -> Pos.testbit_nat a d = false) -> 
  (forall d, c <= d -> Pos.testbit_nat b d = false) ->
                Pos.land a b = 0%N.
Proof.
  induction c; intros.
  - apply pos_testbit_nat_impossible in H0.
    inv H0.
  - destruct a.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by lia.
      apply H in H1.
      inv H1.
    + destruct b.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by lia.
        apply H in H2. auto.
        assert (S c <= S d) by lia.
        apply H0 in H2.
        simpl in H2. auto.
      * simpl.
        rewrite IHc; intros.
        reflexivity.
        simpl in H.
        assert (S d < S c) by lia.
        apply H in H2. auto.
        assert (S c <= S d) by lia.
        apply H0 in H2.
        simpl in H2. auto.
      * reflexivity.
    + (* impossible: a needs to be 0 on lower bits *)
      assert (0 < S c) by lia.
      apply H in H1.
      inv H1.
Qed.

Lemma Ztestbit_above (n : nat) (z i : Z) :
  (0 <= z < Zpower.two_power_nat n)%Z ->
  (Z.of_nat n <= i)%Z ->
  Z.testbit z i = false.
Proof.
  intros. destruct (Z.eq_dec z 0).
  - subst. apply Z.testbit_0_l.
  - apply Z.bits_above_log2. lia.
    assert (Z.log2 z < Z.of_nat n)%Z.
    { apply Z.log2_lt_pow2. lia. rewrite Zpower.two_power_nat_equiv in H. lia. }
    lia.
Qed.

Theorem repr_boxed_t:
   forall a t h, 
     boxed_header t a h ->
   Z.land h 255 =  Z.of_N t.
Proof.
  intros. inv H.
  apply Z.bits_inj.
  unfold Z.eqf.
  intro.
  destruct H1.
  rewrite Z.land_spec.
  assert (Hcase_z:= Z.lt_ge_cases n 0%Z).
  destruct Hcase_z as [Hnz | Hnz].
  { (* testbit = false *)
    destruct n. exfalso; lia.
    exfalso. assert (0 < Z.pos p0)%Z by apply Pos2Z.pos_is_pos. lia.
    reflexivity.
  }    
  
  assert (Hcase := Z.lt_ge_cases n 8%Z).

  destruct Hcase.
  - replace 255%Z with (Z.pred (2^8))%Z.
    rewrite <- Z.ones_equiv. 
    rewrite Z.ones_spec_low.
    rewrite Bool.andb_true_r.
    rewrite Z.add_nocarry_lxor.
    rewrite Z.lxor_spec.
    rewrite OrdersEx.Z_as_OT.shiftl_spec_low.
    rewrite Bool.xorb_false_l.
    reflexivity. lia.
    (* multiple cases depending of if one is 0 or not *)
    {
      destruct (Z.shiftl (Z.of_N a) 10) eqn:Ha.
      - reflexivity.
      - destruct (Z.of_N t) eqn:Hb.
        + reflexivity.
        + simpl.
          rewrite pland_split_nat with (c := 8). reflexivity.
          * intros.
            rewrite <- Ndigits.Ptestbit_Pbit.            
            destruct d. simpl.
            destruct (Z.of_N a). simpl in Ha.
            assert (0 < Z.pos p0)%Z by apply Pos2Z.pos_is_pos. lia.
            simpl in Ha. inv Ha. reflexivity.
            inv Ha. 
            replace false with
                (Z.testbit (Z.pos p0)  (Z.of_nat (S d))).
            reflexivity.
            rewrite <- Ha.
            apply Z.shiftl_spec_low.
            apply Nat2Z.inj_lt in H2.
            simpl Z.of_nat in *. lia.
          * intros.
            rewrite Zpower.two_power_pos_nat in H.
            rewrite <- Ndigits.Ptestbit_Pbit.            
            destruct d. exfalso; lia.
            replace false with
                (Z.testbit (Z.pos p1)  (Z.of_nat (S d))). reflexivity.
            apply Z.bits_above_log2. lia.
            apply Nat2Z.inj_le in H2.
            replace (Pos.to_nat 8) with 8 in H2 by reflexivity.
            rewrite Zpower.two_power_nat_equiv in H.
            replace (Z.of_nat (Pos.to_nat 8)) with 8%Z in H by reflexivity.
            assert (Z.log2 (Z.pos p1) < 8)%Z by (apply Z.log2_lt_pow2; lia).
            lia.
        + destruct t; inv Hb.
      - exfalso.
        destruct H0.
        rewrite <- Z.shiftl_nonneg with (n := 10%Z) in H0.
        rewrite Ha in H0.       
        lia.
    }
    
    
    lia.
    simpl. reflexivity.
  - (* always false *)
    rewrite Bool.andb_false_intro2.
    symmetry.
    eapply Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct. 
    rewrite Zpower.two_power_pos_correct in *.
    unfold Z.pow_pos in H. simpl in *.
    lia.
    simpl. lia.
    eapply Ztestbit_above with (n := 8).
    rewrite Zpower.two_power_nat_correct. simpl. lia.
    simpl. lia.
Qed.    
  

  
  

Definition arity_of_header (h:Z): N :=
  Z.to_N (Z.shiftr h 10).

Definition tag_of_header (h:Z): N :=
    Z.to_N (Z.land h 255).



Inductive repr_asgn_constr: positive -> ctor_tag -> list positive -> statement -> Prop :=
| Rconstr_ass_boxed: forall x (t:ctor_tag) vs s a n h,
    (* boxed x *)   
    M.get t rep_env = Some (boxed n a) ->
    boxed_header n a h -> 
    Forall_statements_in_seq (is_nth_projection_of_x x) vs s -> 
    repr_asgn_constr x t vs (x ::= [val] (allocPtr +' (c_int Z.one uval));
                                     allocIdent ::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) uval); Field(var x, -1) :::= c_int h val;  s)
| Rconstr_ass_enum: forall x t n h,
    (* unboxed x *)
    M.get t rep_env  = Some (enum n) ->
    repr_unboxed_Codegen n h  ->
    repr_asgn_constr x t nil (x ::= c_int h val).


Inductive repr_switch_LambdaANF_Codegen: positive -> labeled_statements -> labeled_statements -> statement -> Prop :=
| Mk_switch: forall x ls ls',
    repr_switch_LambdaANF_Codegen x ls ls'
                      (make_case_switch isptrIdent caseIdent x ls ls').

(* relate a LambdaANF.exp -| ctor_env, fun_env to a series of statements in a clight program (passed as parameter) -- syntactic relation that shows the right instructions have been generated for functions body. There should not be function definitions (Efun), or primitive operations (they are not supported by our backend) in this 
TODO: maybe this should be related to a state instead? 
 *)

(* CHANGE THIS (relational version from translate body) *)
Inductive repr_expr_LambdaANF_Codegen: cps.exp -> statement -> Prop :=
| Rconstr_e:
    forall x t vs  s s' e, 
    repr_asgn_constr x t vs s -> 
    repr_expr_LambdaANF_Codegen e  s' ->
    repr_expr_LambdaANF_Codegen (Econstr x t vs e)  (s; s')    
| Rproj_e: forall x t n v e  s,
    repr_expr_LambdaANF_Codegen e  s ->
    repr_expr_LambdaANF_Codegen (Eproj x t n v e)  (x ::= Field(var v, Z.of_N n) ; s)
| R_app_e: forall f inf ainf ys ays bys pnum (t : fun_tag) s1 s2,
    (* 1 - assign vs to the right args acording to fenv(f)*)
    M.get t fenv = Some inf ->
    ays = skipn nParam ys ->
    bys = firstn nParam ys ->
    ainf = skipn nParam (snd inf) ->
    repr_asgn_fun ays ainf s1 ->
    pnum = min (N.to_nat (fst inf)) nParam ->
    repr_call_vars pnum bys s2 ->
    (* 2 - call f *)
    (* NOTE: added redundant limitIdent |-> limitPtr to avoid having to carry this info around, but could optimize it away *)
    repr_expr_LambdaANF_Codegen (Eapp f t ys) (s1; Efield tinfd allocIdent valPtr :::= allocPtr ; Efield tinfd limitIdent valPtr  :::= limitPtr ;
                                      (Scall None ([Tpointer (mkFunTy threadInfIdent pnum) noattr] (var_or_funvar_f f)) ((Etempvar tinfIdent threadInf) :: s2)))
| R_letapp_e: forall x f inf ainf ys ays bys pnum (t : fun_tag) s1 s2 e s',
    M.get t fenv = Some inf ->
    ays = skipn nParam ys ->
    bys = firstn nParam ys ->
    ainf = skipn nParam (snd inf) ->
    repr_asgn_fun ays ainf s1 ->
    pnum = min (N.to_nat (fst inf)) nParam ->
    repr_call_vars pnum bys s2 ->
    repr_expr_LambdaANF_Codegen e s' ->
    repr_expr_LambdaANF_Codegen (Eletapp x f t ys e)
      (s1; Efield tinfd allocIdent valPtr :::= allocPtr;
       Efield tinfd limitIdent valPtr :::= limitPtr;
       (Scall None ([Tpointer (mkFunTy threadInfIdent pnum) noattr] (var_or_funvar_f f)) ((Etempvar tinfIdent threadInf) :: s2));
       allocIdent ::= Efield tinfd allocIdent valPtr;
       x ::= Field(args, Z.of_nat 1);
       s')
| R_halt_e: forall v e,
    (* halt v <-> store alloc/limit back to tinfo, then set args[1] *)
    var_or_funvar v e ->
    repr_expr_LambdaANF_Codegen (Ehalt v)  (Efield tinfd allocIdent valPtr :::= allocPtr ;
                                             Efield tinfd limitIdent valPtr :::= limitPtr ;
                                             args[Z.of_nat 1 ] :::= e)
| Rcase_e: forall v cl ls ls' s ,
    (* 1 - branches matches the lists of two lists of labeled statements *)
    repr_branches_LambdaANF_Codegen cl ls ls' -> 
    (* 2 - switch-header matches  *)
    repr_switch_LambdaANF_Codegen v ls ls' s ->
    repr_expr_LambdaANF_Codegen  (Ecase v cl)  s
                     (* default case for last boxed and unboxed constructor 
                        OS: perhaps want to include a *)
with repr_branches_LambdaANF_Codegen: list (ctor_tag * exp) -> labeled_statements -> labeled_statements -> Prop :=
     | Rempty_br : repr_branches_LambdaANF_Codegen nil LSnil LSnil
     | Runboxed_default_br: forall t e cl ls n s,
         repr_expr_LambdaANF_Codegen e s ->
         M.get t rep_env  = Some (enum n) ->
         repr_branches_LambdaANF_Codegen cl ls LSnil ->
         repr_branches_LambdaANF_Codegen ((t, e) ::cl) ls (LScons None  (Ssequence s Sbreak)
                                                      LSnil)
     | Runboxed_br: forall cl ls lsa' lsb' lsc' t n tag e s, repr_branches_LambdaANF_Codegen cl ls (LScons lsa' lsb' lsc') ->
                                                repr_expr_LambdaANF_Codegen e s ->
                                                M.get t rep_env  = Some (enum n) ->
                                                repr_unboxed_Codegen n tag ->
                                                repr_branches_LambdaANF_Codegen ((t, e) ::cl) ls (LScons (Some (Z.shiftr tag 1)) (Ssequence s Sbreak) (LScons lsa' lsb' lsc'))
     | Rboxed_default_br : forall cl  ls' t a n e s, repr_branches_LambdaANF_Codegen cl LSnil ls' ->
                                           repr_expr_LambdaANF_Codegen e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           repr_branches_LambdaANF_Codegen ((t, e)::cl) (LScons None  (Ssequence s Sbreak) LSnil) ls'
     | Rboxed_br : forall cl lsa lsb lsc ls' t a n tag e s, repr_branches_LambdaANF_Codegen cl (LScons lsa lsb lsc) ls' ->
                                           repr_expr_LambdaANF_Codegen e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           boxed_header n a tag ->
                                           repr_branches_LambdaANF_Codegen ((t, e)::cl) (LScons (Some (Z.land tag 255)) (Ssequence s Sbreak)  (LScons lsa lsb lsc)) ls'.

                    
Theorem repr_branches_LSnil_no_unboxed:
  forall t e cl  ls,
    findtag cl t = Some e ->
    repr_branches_LambdaANF_Codegen cl ls LSnil  -> 
    ~ (exists arr, M.get t rep_env = Some (enum arr)).
Proof.
  induction cl; intros.
  - inv H.
  - simpl in H. destruct a.
    destruct (M.elt_eq c t).
    + subst. inv H0; intro; destruct H0; rewrite H0 in H8; inv H8.
    + inv H0. inv H4. inv H.
      eapply IHcl; eauto.
Qed.

Theorem repr_branches_LSnil_no_boxed:
  forall t e cl  ls,
    findtag cl t = Some e ->
    repr_branches_LambdaANF_Codegen cl LSnil ls  -> 
    ~ (exists arr s, M.get t rep_env = Some (boxed arr s)).
Proof.
  induction cl; intros.
  - inv H.
  - simpl in H. destruct a.
    destruct (M.elt_eq c t).
    + subst. inv H0; intro; destruct H0; destruct H0. rewrite H0 in H7; inv H7. rewrite H0 in H8; inv H8.
    + inv H0. inv H8. inv H.
      eapply IHcl; eauto.
Qed.


      
Definition gc_vars := ((allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, boolTy) ::nil).

Definition gc_set := (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray val maxArgs noattr)).

Definition gc_test (gcArrIdent:positive) (l:N) (vs : list positive) (ind : list N) (fenv : fun_env) (finfo_env : fun_info_env) := (reserve argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent nParam gcArrIdent
                                                           (Z.of_N (l + 2)) vs ind fenv finfo_env).

Definition gc_test' (gcArrIdent:positive) (l:N) (vs : list positive) (ind : list N) (fenv : fun_env) (finfo_env : fun_info_env) := (reserve' argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent nParam gcArrIdent
                                                           (Z.of_N (l + 2)) vs ind fenv finfo_env).

Inductive right_param_asgn: list positive -> list N -> statement -> Prop :=
| asgn_nil: right_param_asgn nil nil Sskip
| asgn_cons: forall x xs n ns s,  right_param_asgn xs ns s -> right_param_asgn (x::xs) (n::ns) ((x ::= args[Z.of_N n]);s).


(* lenv' is lenv after binding xs->vs with NoDup xs *)
Definition lenv_param_asgn (lenv lenv':temp_env) (xs:list positive) (vs:list Values.val): Prop :=
  forall i, (forall z, nthN xs z  = Some i ->  M.get i lenv' = nthN vs z)
            /\
            (~ List.In i xs -> M.get i lenv' = M.get i lenv).

Inductive lenv_param_asgn_i: temp_env -> temp_env -> list positive -> list Values.val -> Prop :=
| LPA_nil: forall lenv, lenv_param_asgn_i lenv lenv [] []    
| LPA_cons: forall lenv lenv' ys vs y v,
    lenv_param_asgn_i (M.set y v lenv) lenv' ys vs ->
    lenv_param_asgn_i lenv lenv' (y::ys) (v::vs).


Theorem lenv_param_asgn_i_length:
  forall ys vs lenv lenv',
    lenv_param_asgn_i lenv lenv' ys vs ->
    length ys = length vs.
Proof.
  induction ys; intros. inv H; reflexivity.
  inv H. simpl. eapply IHys in H5. auto.
Qed.


Theorem lenv_param_asgn_rel:
  forall ys vs lenv lenv', 
    lenv_param_asgn_i lenv lenv' ys vs ->
    NoDup ys ->
    lenv_param_asgn lenv lenv' ys vs.
Proof.
  induction ys; intros.
  - inv H. constructor; intros. inv H. reflexivity.
  - inv H. eapply IHys in H6. split; intros; specialize (H6 i); destruct H6.
    + rewrite nthN_equation in *. destruct (var_dec a i).
      * destruct z. subst.
        rewrite H2. rewrite M.gss. reflexivity. inv H0; auto.
        apply H1 in H. auto.
      * destruct z. exfalso. inv H. apply n; auto.
        apply H1 in H. auto.        
    + rewrite M.gso in H2. apply H2.
      intro. apply H. constructor 2. auto.
      intro. apply H. constructor; auto.
    + inv H0; auto.
Qed.

Theorem e_lenv_param_asgn_i:
  forall ys lenv vs,
    length ys = length vs ->
    NoDup ys ->
    exists lenv',
      lenv_param_asgn_i lenv lenv' ys vs.
Proof.
  induction ys; intros.
  - destruct vs; inv H. exists lenv. constructor. 
  - destruct vs; inv H. inv H0.
    specialize (IHys  (M.set a v lenv)).
    specialize (IHys _ H2 H4).
    destruct IHys as [lenv' Hlenv'].
    eexists; constructor; eauto. 
Qed.



Theorem e_lenv_param_asgn:
  forall lenv ys vs,
    length ys = length vs ->
    NoDup ys ->
    exists lenv',
      lenv_param_asgn lenv lenv' ys vs.
Proof.
  intros.
  assert (Hi := e_lenv_param_asgn_i ys lenv vs H H0).
  destruct Hi.
  apply lenv_param_asgn_rel in H1; eauto.
Qed.


Theorem get_list_nth_get' (B:Type):
  forall  (vs : list B) rho v xs  N, 
  get_list xs rho = Some vs ->
  nthN vs N = Some v ->
  exists x, nthN xs N = Some x /\ M.get x rho = Some v. 
Proof.
  induction vs; intros; destruct xs.
  inv H0. inv H0.
  simpl in H. inv H.
  rewrite nthN_equation in H0.
  destruct N.
  - inv H0. simpl in H.
    exists e. split. reflexivity.
    destruct (M.get e rho).
    destruct (get_list xs rho). inv H; auto.
    inv H. inv H.
  - simpl in H. destruct (M.get e rho).
    destruct (get_list xs rho) eqn:Hxs. inv H.
    specialize (IHvs _ _ _ _ Hxs H0).
    rewrite nthN_equation. auto. inv H.
    inv H.
Qed.   
  

Theorem in_rho_entry:
  forall xs vs fl rho x v, 
  set_lists xs vs (def_funs fl fl (M.empty cps.val) (M.empty cps.val)) = Some rho ->
  NoDup xs ->
  M.get x rho = Some v ->
  (exists n, nthN xs n = Some x /\ nthN vs n = Some v) \/
  (exists t ys b, ~List.In x xs /\  find_def x fl = Some (t, ys, b) /\ v = Vfun (M.empty cps.val) fl x).
Proof.                               
  intros.
  assert (decidable (List.In x xs)). apply In_decidable. apply var_dec_eq. 
  inv H2.
  - left. 
    assert (Hgl := get_list_set_lists _ _ _ _  H0 H ).
    apply In_nthN in H3. destruct H3.
    assert (Hgl' := get_list_nth_get _ _ _ _ _ Hgl H2).
    destruct Hgl'.
    destruct H3.
    exists x0.
    rewrite H4 in H1; inv H1.
    split; auto.
  - right.
    erewrite <- set_lists_not_In in H1; eauto.
    assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
    inv H2.
    + assert (H4' := H4).
      eapply def_funs_eq in H4.
      rewrite H1 in H4.
      inv H4.
      apply name_in_fundefs_find_def_is_Some in H4'.
      destruct H4' as [ft [ys [e Hfd]]].
      exists ft, ys, e; eauto.
    +  erewrite def_funs_neq in H1; eauto.
       rewrite M.gempty in H1; inv H1.
Qed.

      


Inductive repr_val_LambdaANF_Codegen:  cps.val -> mem -> Values.val -> Prop :=
| Rint_v: forall  z r m,
    repr_unboxed_Codegen (Z.to_N z) r ->
    repr_val_LambdaANF_Codegen (cps.Vint z) m (make_vint r)
| Rconstr_unboxed_v:
    forall t arr n m,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_Codegen arr n ->
      repr_val_LambdaANF_Codegen (cps.Vconstr t nil) m  (make_vint n)
| Rconstr_boxed_v: forall  t vs n a b i m h,
    (* t is a boxed constructor, n ends with 0 and represents 
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed n a) ->
    (* 1) well-formedness of the header block *)

    Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size))) = Some (make_vint h) ->
    boxed_header n a h ->
    (* 2) all the fields are also well-represented *)
    repr_val_ptr_list_LambdaANF_Codegen vs m b i ->
    repr_val_LambdaANF_Codegen (cps.Vconstr t vs) m  (Vptr b i)
| Rfunction_v: 
    forall vars avars fds f m b t t' vs pvs avs alocs e asgn body l locs finfo gccall,
      let F := mkfunction (Tvoid)
                          ((mkcallconv None false false)) (*({| cc_vararg := None; cc_unproto := false; cc_structret := false |})*)
             ((tinfIdent, threadInf)::(map (fun x => (x , val)) pvs))
             (nil)
             (List.app avars gc_vars)
             (Ssequence gccall (Ssequence (Ssequence gc_set asgn)
                                          body)) in
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some (finfo , t') -> (* TODO: check this *)
      t = t' ->
      Genv.find_symbol (Genv.globalenv p) f = Some b -> (* symbol f points to b in the globalenv *)
      (* b points to an internal function in the heap [and i is 0] *)
      gc_test' finfo l vs locs fenv finfo_env = Some gccall ->
      Genv.find_funct (globalenv p) (Vptr b  Ptrofs.zero) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler, 
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      (*
       - calling convention?  
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       (*
        - all the vars match + the 3 gc vars *)       

       (* - no temps *)
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_LambdaANF_Codegen)
        *)
      Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
      pvs = firstn nParam vs ->
      avs = skipn nParam vs ->
      alocs = skipn nParam locs ->
      avars = skipn nParam vars ->
      right_param_asgn avs alocs asgn ->
      repr_expr_LambdaANF_Codegen e body ->
      repr_val_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m (Vptr b Ptrofs.zero) 
with repr_val_ptr_list_LambdaANF_Codegen: (list cps.val) -> mem -> block -> ptrofs -> Prop := 
     | Rnil_l:
         forall m b i,
           repr_val_ptr_list_LambdaANF_Codegen nil m b i
     | Rcons_l:
         forall v vs m b i v7,
           Mem.load int_chunk m b (Ptrofs.unsigned  i) = Some v7 ->
           repr_val_LambdaANF_Codegen v m v7 -> 
           repr_val_ptr_list_LambdaANF_Codegen vs m b (Ptrofs.add i (Ptrofs.repr int_size)) ->
           repr_val_ptr_list_LambdaANF_Codegen (v::vs) m b i.



Definition locProp := block -> Z -> Prop.


(* m and m' are the _same_ over subheap L *)

Definition sub_locProp: locProp -> locProp -> Prop :=
  fun L L' => forall b ofs, L b ofs -> L' b ofs.

      

(* CHANGE THIS *)
Inductive repr_val_L_LambdaANF_Codegen:  cps.val -> mem -> locProp -> Values.val -> Prop :=
| RSint_v: forall L z r m,
    repr_unboxed_Codegen (Z.to_N z) r ->
    repr_val_L_LambdaANF_Codegen (cps.Vint z) m L (make_vint r)
| RSconstr_unboxed_v:
    forall t arr n m L,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_Codegen arr n ->
      repr_val_L_LambdaANF_Codegen (cps.Vconstr t nil) m L (make_vint n)
| RSconstr_boxed_v: forall (L:block -> Z -> Prop) t vs n a b i m h,
    (* t is a boxed constructor, n ends with 0 and represents 
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed n a) ->
    (forall j : Z, (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size)) <= j <
   Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size)) + size_chunk int_chunk)%Z  -> L b j%Z) ->
    (* 1) well-formedness of the header block *)

    Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i (Ptrofs.repr int_size))) = Some (make_vint h) -> 
    boxed_header n a h ->
    (* 2) all the fields are also well-represented *)
    repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
    repr_val_L_LambdaANF_Codegen (cps.Vconstr t vs) m L (Vptr b i)
| RSfunction_v:             
    forall (L:block -> Z -> Prop)  vars avars fds f m b t t' vs pvs avs e asgn body l locs alocs finfo gccall,
      let F := mkfunction (Tvoid)
                          ((mkcallconv None false false)) (*({| cc_vararg := None; cc_unproto := false; cc_structret := false |})*)
             ((tinfIdent, threadInf)::(map (fun x => (x , val)) pvs))
             (nil)
             (List.app avars gc_vars)
             (Ssequence gccall (Ssequence (Ssequence gc_set asgn)
                                          body)) in
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some (finfo , t') -> (* TODO: check this *)
      t = t' ->
      Genv.find_symbol (Genv.globalenv p) f = Some b -> (* symbol f points to b in the globalenv *)
      (* b points to an internal function in the heap [and i is 0] *)
      gc_test' finfo l vs locs fenv finfo_env = Some gccall ->
      Genv.find_funct (globalenv p) (Vptr b  Ptrofs.zero) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler, 
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      (*
       - calling convention?  
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       (*
        - all the vars match + the 3 gc vars *)       

       (* - no temps *)
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_LambdaANF_Codegen)
        *)
      Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
      pvs = firstn nParam vs ->
      avs = skipn nParam vs ->
      alocs = skipn nParam locs ->
      avars = skipn nParam vars ->
      right_param_asgn avs alocs asgn ->
      repr_expr_LambdaANF_Codegen e body ->
      repr_val_L_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m L (Vptr b Ptrofs.zero) 
with repr_val_ptr_list_L_LambdaANF_Codegen: (list cps.val) -> mem -> locProp -> block -> ptrofs -> Prop := 
     | RSnil_l:
         forall m L b i,
           repr_val_ptr_list_L_LambdaANF_Codegen nil m L b i
     | RScons_l:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, ((Ptrofs.unsigned i) <= j < (Ptrofs.unsigned i) + int_size)%Z -> L b j) ->
           Mem.load int_chunk m b (Ptrofs.unsigned i) = Some v7 ->
           repr_val_L_LambdaANF_Codegen v m L v7 -> 
           repr_val_ptr_list_L_LambdaANF_Codegen vs m L b (Ptrofs.add i (Ptrofs.repr int_size)) ->
           repr_val_ptr_list_L_LambdaANF_Codegen (v::vs) m L b i.

Scheme repr_val_L_LambdaANF_Codegen_rec := Induction for repr_val_L_LambdaANF_Codegen Sort Prop
  with repr_val_ptr_list_L_LambdaANF_Codegen_rec := Induction for repr_val_ptr_list_L_LambdaANF_Codegen Sort Prop.



Inductive  repr_val_ptr_list_L_LambdaANF_Codegen_Z: (list cps.val) -> mem -> locProp -> block -> Z -> Prop := 
     | RSnil_l_Z:
         forall m L b i,
           repr_val_ptr_list_L_LambdaANF_Codegen_Z nil m L b i
     | RScons_l_Z:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, (i <= j < i + int_size)%Z -> L b j) ->
           Mem.load int_chunk m b i = Some v7 ->
           repr_val_L_LambdaANF_Codegen v m L v7 -> 
           repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b (i+ int_size)%Z ->
           repr_val_ptr_list_L_LambdaANF_Codegen_Z (v::vs) m L b i.




 

(* 
Theorem repr_val_forall_L_fun:
  forall L fds f m b,
  repr_val_ptr_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m (b,Int.zero) <-> repr_val_L_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m L (Vptr b Int.zero).
Proof.
  intros. split; intro H; inv H; econstructor; eauto.
Qed.   *)

Theorem repr_val_ptr_list_Z:
  forall m L b vs i,
    uint_range ((Ptrofs.unsigned i) + (Z.of_nat (length vs)* int_size))%Z -> 
  repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i <-> repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b (Ptrofs.unsigned i).
Proof.
  induction vs; intros.
  - split; intro; constructor.
  - assert  (Hi4 : (Ptrofs.unsigned i + int_size)%Z = (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr int_size)))).
    { 
      unfold int_size in *; simpl size_chunk in *.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr.
      rewrite Ptrofs.unsigned_repr. reflexivity.
      compute; destruct Archi.ptr64; split; intros Hlt; inv Hlt.

      
      rewrite Ptrofs.unsigned_repr.
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
      rewrite Z.mul_succ_l in H.
      assert (0 <= Z.of_nat (length vs))%Z.     
      apply Nat2Z.is_nonneg.
      rewrite Z.add_assoc in H.
      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      inv H. split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. auto. 
      chunk_red; lia. chunk_red; lia. compute; destruct Archi.ptr64; split; intros Hlt; inv Hlt.
      }
    split; intro; inv H0.
    + econstructor; eauto; unfold int_size in *; simpl size_chunk in *.
      apply IHvs in H10.
      rewrite Hi4.
      auto.
      rewrite <- Hi4.
      
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
     
      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Nat2Z.is_nonneg.
      inv H.
      rewrite Z.mul_succ_l in H7.
      rewrite Z.add_assoc in H7.
      split; chunk_red; lia.
    + econstructor; eauto.
      unfold int_size in *; simpl size_chunk in *.
      apply IHvs.
      rewrite <- Hi4. 
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.     
      assert (0 <= Ptrofs.unsigned i)%Z by apply Ptrofs.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Nat2Z.is_nonneg.
      inv H.
      rewrite Z.mul_succ_l in H6.
      rewrite Z.add_assoc in H6.
      split; chunk_red; lia.
      rewrite <- Hi4. auto.
Qed.      


    
  
(* this is the sum of get_var_or_funvar and repr_val_L_LambdaANF_Codegen (-> and <-\-) *)
Inductive repr_val_id_L_LambdaANF_Codegen: cps.val -> mem -> locProp -> temp_env -> positive -> Prop := 
| RVid_F:
   forall b f lenv fds L m,
     Genv.find_symbol (Genv.globalenv p) f = Some b ->
     repr_val_L_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m L (Vptr b (Ptrofs.zero)) ->
     repr_val_id_L_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m L lenv f
| RVid_V:
    forall x m lenv L v6 v7,
      Genv.find_symbol (Genv.globalenv p) x = None -> 
      M.get x lenv = Some v7 ->
      repr_val_L_LambdaANF_Codegen v6 m L v7 ->
      repr_val_id_L_LambdaANF_Codegen v6 m L lenv x.


Theorem repr_val_id_L_LambdaANF_Codegen_vint_or_vptr:
  forall v6 m L v7,
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  Vint_or_Vptr v7 = true.
Proof.  
  intros; inv H; auto. 
Qed.


(* If v is needed *)
Theorem repr_val_id_L_LambdaANF_Codegen_ptr:
  forall v6 m L lenv x,
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  exists v7, repr_val_L_LambdaANF_Codegen v6 m L v7 /\
            ((M.get x lenv = Some v7 /\
             Genv.find_symbol (Genv.globalenv p) x = None)
             \/
             (exists b, v7 = Vptr b Ptrofs.zero /\
                        Genv.find_symbol (Genv.globalenv p) x = Some b)).
Proof.            
  intros. inv H.
  - exists (Vptr b (Ptrofs.zero)). split; auto.
    right. exists b; auto.
  - exists v7. split; auto. 
Qed. 


Theorem get_var_or_funvar_eval:
  forall lenv a v m, 
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    get_var_or_funvar lenv a v ->
    eval_expr (globalenv p) empty_env lenv m (var_or_funvar_f   a) v.
Proof. 
  intros. specialize (H a). inv H. unfold var_or_funvar_f. inv H1.
  - rewrite H. destruct (H3 (ex_intro _ b H)). 
    unfold makeVar. rewrite H1.
    destruct x.
    specialize (H0 _ _ f H1).
    destruct H0. destruct x.
    rewrite H0.
    econstructor. constructor 2.
    apply M.gempty. eauto.
    constructor. auto.
  - rewrite H. constructor. auto.
Qed.

Theorem get_var_or_funvar_semcast:
  forall v a m lenv,
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    get_var_or_funvar lenv a v ->
    sem_cast v (typeof (var_or_funvar_f a)) val m = Some v.
Proof.
  intros. unfold var_or_funvar_f. specialize (H a). inv H. inv H1.
  - rewrite H. destruct (H3 (ex_intro _ b H)).
    unfold makeVar. rewrite H1.
    destruct x.
    specialize (H0 _ _ f H1).
    destruct H0. destruct x.
    rewrite H0.
    simpl. auto.
  - rewrite H. unfold val. destruct Archi.ptr64; destruct v; inv H5; simpl; auto.
Qed.  

Theorem repr_val_id_implies_var_or_funvar:
  forall v6 m L lenv x,
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  exists v7, get_var_or_funvar lenv x v7 /\
             repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  intros. inv H.
  - exists (Vptr b Ptrofs.zero).
    split. constructor; auto.
    auto.
  - exists v7.
    split. constructor 2; auto. inv H2; auto.
    auto.
Qed.

Theorem repr_val_id_set:
  forall v6 m L lenv x,
    repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
    forall x0 v, 
    x <> x0 ->
    repr_val_id_L_LambdaANF_Codegen v6 m L (M.set x0 v lenv) x.
Proof.
  intros. inv H.
  - econstructor; eauto.
  - econstructor 2; eauto.
    rewrite M.gso; auto.
Qed.
                                
Scheme repr_val_ind' := Minimality for repr_val_L_LambdaANF_Codegen Sort Prop
  with repr_val_list_ind' := Minimality for repr_val_ptr_list_L_LambdaANF_Codegen Sort Prop.
 (* Combined Scheme repr_val_L_LambdaANF_Codegen_mutind from repr_val_L_LambdaANF_Codegen_ind, repr_val_ptr_list_L_LambdaANF_Codegen_ind. *)
 
Theorem nthN_pos_pred: 
  forall {A} (a:A) vs v6 p0,
  nthN (a :: vs) (N.pos p0) = Some v6 ->
  nthN vs (N.pred (N.pos p0)) = Some v6.
Proof.
  intros. destruct p0; auto.
Qed.

Theorem Z_mul_4:
  forall p,
   Z.pos p~0~0 = (4 * Z.pos p)%Z.
Proof.
  intro.
  replace ((xO (xO p0))) with (Zpower.shift 2%Z p0) by reflexivity.
  rewrite Zpower.shift_equiv; auto. lia.
Qed.


Theorem repr_val_ptr_list_L_Z_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i -> 
 nthN vs n = Some v6 ->
 exists v7, Mem.load int_chunk m b (i + (Z.of_N n * int_size))  = Some v7 /\
 repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.  
  induction vs; intros. inv H0.
  inv H. 
  destruct n. simpl in H0. inv H0.
  exists v7.
  simpl. rewrite Z.add_0_r. auto.
  apply nthN_pos_pred in H0.
  eapply IHvs in H0; eauto. destruct H0. exists x. inv H.
  split; auto.
  rewrite N2Z.inj_pred in H0. 2: apply N_lt_pos. rewrite Z.mul_pred_l in H0.  
  replace (i +  int_size + (Z.of_N (N.pos p0) *  int_size -  int_size))%Z with (i + Z.of_N (N.pos p0) *  int_size)%Z in H0 by (chunk_red; lia).
  auto.
Qed.


Theorem repr_val_ptr_list_L_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i -> 
 nthN vs n = Some v6 ->
 exists v7, Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr (Z.of_N n)) (Ptrofs.repr int_size))))  = Some v7 /\
 repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.  
  induction vs; intros. inversion H0.
  destruct n.
  - simpl. inv H0.
    inv H.
    rewrite Ptrofs.add_zero. 
    exists v7; auto.
  - simpl.
    inv H.
    apply nthN_pos_pred in H0.
    specialize (IHvs _ _ _ H10 H0).
    destruct IHvs. destruct H.
    exists x; split; auto.
    replace (Ptrofs.unsigned
           (Ptrofs.add (Ptrofs.add i (Ptrofs.repr int_size))
              (Ptrofs.mul (Ptrofs.repr (Z.of_N (N.pred (N.pos p0))))
                       (Ptrofs.repr int_size)))) with
        (Ptrofs.unsigned
           (Ptrofs.add i (Ptrofs.mul (Ptrofs.repr (Z.pos p0)) (Ptrofs.repr int_size)))) in H.
    auto.
    rewrite Ptrofs.add_assoc.
    unfold Ptrofs.mul.
    unfold Ptrofs.add.
    erewrite  Ptrofs.eqm_samerepr.
    reflexivity.
    apply Ptrofs.eqm_add.
    apply Ptrofs.eqm_refl.
    eapply Ptrofs.eqm_trans.
    apply Ptrofs.eqm_unsigned_repr_l.
    2:{
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl. }
    rewrite Z.add_comm.
    rewrite N2Z.inj_pred by (unfold N.lt; auto).
    int_red.
    rewrite N2Z.inj_pos.
    eapply Ptrofs.eqm_trans.
    apply Ptrofs.eqm_mult.
    apply Ptrofs.eqm_unsigned_repr_l.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_l.
    apply Ptrofs.eqm_refl. 
    eapply Ptrofs.eqm_trans.
    2:{
    apply Ptrofs.eqm_add.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_mult.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl.
    apply Ptrofs.eqm_unsigned_repr_r.
    apply Ptrofs.eqm_refl. }
    rewrite Z.mul_pred_l.
    apply Ptrofs.eqm_refl2. lia.
Qed.



Theorem repr_val_L_unchanged:
  forall v6 m L v7, 
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_L_LambdaANF_Codegen v6 m' L v7.
Proof.
  apply (repr_val_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_LambdaANF_Codegen v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5). 
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.  
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Theorem repr_val_id_L_unchanged:
  forall v6 m lenv L x, 
  repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_id_L_LambdaANF_Codegen v6 m' L lenv x.
Proof.
    intros. inv H.
  - econstructor; eauto. eapply repr_val_L_unchanged; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_ptr_list_L_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i.
Proof.
  apply (repr_val_list_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_LambdaANF_Codegen v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5). 
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.  
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Corollary repr_val_ptr_list_L_Z_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m' L b i.
Proof.
  induction vs; intros.
  constructor.
  inv H. econstructor; eauto.
  eapply Mem.load_unchanged_on; eauto.  
  eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_L_sub_locProp:
    forall v6 m L v7, 
  repr_val_L_LambdaANF_Codegen v6 m L v7 ->
  forall L', sub_locProp L L' -> 
  repr_val_L_LambdaANF_Codegen v6 m L' v7.
Proof.
  apply (repr_val_ind' (fun v6 m L v7 => forall L', sub_locProp L L' -> 
                                                   repr_val_L_LambdaANF_Codegen v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Theorem repr_val_id_L_sub_locProp:
  forall v6 m L x lenv, 
    repr_val_id_L_LambdaANF_Codegen v6 m L lenv x ->
    forall L', sub_locProp L L' -> 
               repr_val_id_L_LambdaANF_Codegen v6 m L' lenv x.
Proof.
  intros. inv H.
  - econstructor; eauto. eapply repr_val_L_sub_locProp; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.

    
Theorem repr_val_ptr_list_L_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_LambdaANF_Codegen vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i.
Proof.
  apply (repr_val_list_ind' (fun v6 m L v7 => forall L', sub_locProp L L' -> 
                                                   repr_val_L_LambdaANF_Codegen v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_LambdaANF_Codegen vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Corollary repr_val_ptr_list_L_Z_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_LambdaANF_Codegen_Z vs m L' b i.
Proof.
  induction vs; intros.
  -  constructor.
  - inv H. econstructor; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.  



    
(* 
Returns True if the pointer Vptr q_b q_ofs is reachable by crawling v7 
Assumes correct memory layout (i.e. repr_val_LambdaANF_Codegen v6 m v7)
 *)
Fixpoint reachable_val_Codegen (v6:cps.val) (m:mem) (v7:Values.val) (q_b:block) (q_ofs:ptrofs): Prop :=
  match v6, v7 with
  | cps.Vint z, Vint r => False
  | cps.Vconstr t vs, Vptr b i =>
    (fst (List.fold_left (fun curr v =>
                            let '(p, (p_b, p_ofs)) := curr in
                            (match Val.cmpu_bool (Mem.valid_pointer m) Ceq (Vptr p_b p_ofs) (Vptr q_b q_ofs) with
                             | Some true => (True, (p_b, (Ptrofs.add p_ofs (Ptrofs.repr (sizeof (M.empty composite) val)))))
                             | _ => 
                               (match Mem.load int_chunk m p_b (Ptrofs.unsigned p_ofs) with
                                | Some v7 => 
                                  (reachable_val_Codegen v m v7 q_b q_ofs, (p_b, (Ptrofs.add p_ofs (Ptrofs.repr (sizeof (M.empty composite) val)))))
                                | _ => curr
                                end)
                             end))                        
                        vs (False, (b,i))))
  | (cps.Vfun rho fds f), Vptr b i => False
  | _, _ => False
  end.


                                                                        
(*
Theorem repr_val_load_result: forall v6 m v7,
    repr_val_LambdaANF_Codegen v6 m (Val.load_result int_chunk v7)
                   <->
  repr_val_LambdaANF_Codegen v6 m v7.
Proof.
  intros.
  destruct v7; split; intro H; inv H; simpl in *; econstructor; eauto.
Qed.   *)

Theorem repr_val_L_load_result: forall v6 m v7 L,
    repr_val_L_LambdaANF_Codegen v6 m L (Val.load_result int_chunk v7)
                   <->
  repr_val_L_LambdaANF_Codegen v6 m L v7.
Proof.
  intros.
  unfold Val.load_result in *. unfold int_chunk in *.
  destruct Archi.ptr64 eqn:Harch;
  destruct v7; split; intro H; try (inv H; simpl in *; unfold make_vint; try (rewrite Harch); econstructor; eauto).
  apply repr_val_id_L_LambdaANF_Codegen_vint_or_vptr in H. simpl in H. rewrite Harch in H. inv H.
Qed. 





(* the memory blocks in the sequence (b, i), (b, i+off) ... (b, i+((n-1)*off)) are pairwise related with the sequence (b', i'), (b', i'+off) ... (b', i'+(n-1*off))  *)
Inductive For_N_blocks (P:(block * ptrofs) -> (block * ptrofs) -> Prop) (loc:block * ptrofs) (loc':block * ptrofs) (off: ptrofs) :  nat -> Prop :=
| FNb_O: For_N_blocks P loc loc' off 0
| FNb_S: forall n,
    P (fst loc, Ptrofs.add (snd loc) (Ptrofs.mul off (Ptrofs.repr (Z.of_nat n)))) (fst loc', Ptrofs.add (snd loc') (Ptrofs.mul off (Ptrofs.repr (Z.of_nat n)))) ->
    For_N_blocks P  loc loc' off n -> 
    For_N_blocks P loc  loc' off (S n). 


(* Related (deep copy) vals that may have been moved by the GC, in such way that they can be used in place of the other in repr_val_ptr_LambdaANF_Codegen 
 *)
Inductive related_boxed_Codegen: mem -> (block *  ptrofs) -> mem -> (block *  ptrofs) -> Prop :=
| SV_constr_boxed :
    forall m m' b i b' i' h h' n a,
    (* same tag *)
      Mem.load int_chunk m b (Ptrofs.unsigned (Ptrofs.sub i Ptrofs.one)) = Some (make_vint h) ->
      boxed_header n a  h ->
      Mem.load int_chunk m' b' (Ptrofs.unsigned (Ptrofs.sub i' Ptrofs.one)) = Some (make_vint h') ->
      boxed_header n a  h' ->      
      (* each of the a (arrity) fields are either same int shifted+1, same function or pointers (0-ended) related according to same_boxed *)
      For_N_blocks (fun loc loc' => related_boxed_or_same_val_Codegen m loc m' loc') (b,i) (b', i') (Ptrofs.repr (sizeof (M.empty composite) val)) (N.to_nat a) -> 
      related_boxed_Codegen m (b,i) m' (b', i')
with related_boxed_or_same_val_Codegen: mem -> (block *  ptrofs) -> mem -> (block * ptrofs) -> Prop :=
     | RBSI_fun :
         (* same fun *)
         forall m m' b i b' i' F,
           b = b' /\ i = i' ->
           Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
           related_boxed_or_same_val_Codegen m (b,i) m' (b', i')                                   
     | RBSI_int :
         (* same int/unboxed constructor *)
         forall m b i n m' b' i' h,
           Mem.load int_chunk m b (Ptrofs.unsigned i) = Some (make_vint h) ->
           Mem.load int_chunk m' b' (Ptrofs.unsigned i') = Some (make_vint h) ->
           repr_unboxed_Codegen n h ->
           related_boxed_or_same_val_Codegen m (b,i) m' (b', i')
     | RBSI_pointer:
         forall m b i  m' b' i' b1 i1 b2 i2,
         Mem.load int_chunk m b (Ptrofs.unsigned i) = Some (Vptr b1 i1) ->
         Mem.load int_chunk m' b' (Ptrofs.unsigned i') = Some (Vptr b2 i2) ->
         (* TODO: may be Vint h and h' that needs to be interpreted as pointers inside m *)
         (* TODO: make sure that *)
         related_boxed_Codegen m (b1, i1) m' (b2,i2) ->
         related_boxed_or_same_val_Codegen m (b,i) m' (b', i').

(* TODO: related or boxed which also checks that what is reachable is in L *)
(* 
Inductive val_tree: Type :=
| u_c_leaf :  int -> val_tree
| f_leaf : block -> int -> val_tree
| b_c_node : 
    (* header *) int ->
                 list val_tree -> val_tree.

Fixpoint eq_val_trees (v1:val_tree) (v2:val_tree): bool :=
  match v1, v2 with
  | u_c_leaf i1, u_c_leaf i2 => Int.eq i1 i2
  | f_leaf b1 ofs1, f_leaf b2 ofs2 =>
    andb (Pos.eqb b1 b2) (Int.eq ofs1 ofs2)
  | b_c_node h1 l1, b_c_node h2 l2 =>
    andb (Int.eq h1 h2) (utils.forallb2 eq_val_trees l1 l2)
  | _ , _ => false
  end.



(* need either fuel or assumption that blocks are increasing when allocated [thus decreasing while traversing] 
   fuel bounds the depth of the tree
*)
Fixpoint load_val_tree (m:mem) (v:Values.val) (fuel:nat) : option val_tree :=
  match fuel with
  | S fuel' => 
    (match v with
     | (Vptr b' i') =>
       if (Mem.valid_pointer m b' (Int.unsigned i')) then
         (* this is a b_c, load the header and then the rest of the tree *)
         (match Mem.load int_chunk m b' ((Int.unsigned i') - int_size) with
          | Some (Vint h) =>
            (* get arity from header *)
            let n := arity_of_header (Int.unsigned h) in
            (* 
            let fix load_val_tree_ptr (m:mem) (b:block) (ofs:Z) (i:nat): option (list val_tree) :=
                (match i with
                | 0 =>  Some nil
                | S i' =>
                  (match Mem.load int_chunk m b ofs with
                   | Some v =>
                     (match load_val_tree m v fuel, load_val_tree_ptr m b (ofs + int_size)%Z i' with
                      | Some vt, Some lv => Some (vt::lv)
                      | _, _ => None
                      end)
                   | None => None
                   end)
                 end) in
            
            (match load_val_tree_ptr m b' (Int.unsigned i') (N.to_nat n) with
             | Some vl => Some (b_c_node h vl)
             | None => None
             end) *)
            None
          | _ => None
          end) 
       else
         (* this is a function [ outside of m ]*)
         Some (f_leaf b' i')    
     | (Vint h) => Some (u_c_leaf h)
     | _ => None
     end)
  | 0 => None
  end
.

 

  *)
  



(* this is false, missing the boxed case which is off-shifted 
Theorem repr_val_ptr_load :
  forall v6 m b i,
    repr_val_ptr_LambdaANF_Codegen v6 m (b, i) ->
    (exists v7, Mem.load int_chunk m b (Int.unsigned i)  = Some v7 /\ repr_val_LambdaANF_Codegen v6 m v7)
             \/ exists F, Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F). *)

(* relational version of get_allocs *)
Inductive get_allocs_ind: exp -> list positive -> Prop :=
| GEI_constr: forall x t vs e l, get_allocs_ind e l -> get_allocs_ind (Econstr x t vs e) (x::l)
| GEI_case: forall x cs l, get_allocs_case_ind cs l -> get_allocs_ind (Ecase x cs) l
| GEI_proj: forall x t n v e l, get_allocs_ind e l -> get_allocs_ind (Eproj x t n v e) (x::l)
| GEI_eletapp: forall x f ft ys e l, get_allocs_ind e l -> get_allocs_ind (Eletapp x f ft ys e) (x::l)
| GEI_app: forall x t vs, get_allocs_ind (Eapp x t vs) []
| GEI_eprim_val: forall x p e l, get_allocs_ind e l -> get_allocs_ind (Eprim_val x p e) (x::l)
| GEI_prim: forall x p vs e l, get_allocs_ind e l -> get_allocs_ind (Eprim x p vs e) (x::l)
| GEI_halt: forall x, get_allocs_ind (Ehalt x) []
| GEI_fun: forall fnd e l l', get_allocs_fundefs_ind fnd l ->
                              get_allocs_ind e l' ->
                              get_allocs_ind (Efun fnd e) (l ++ l')
with get_allocs_case_ind: list (ctor_tag * exp) -> list positive -> Prop :=
   | GEI_nil: get_allocs_case_ind nil nil
   | GEI_cons: forall z e cs l l',
       get_allocs_ind e l ->
       get_allocs_case_ind cs l' ->
       get_allocs_case_ind (cons (z, e) cs) (l++l')
with get_allocs_fundefs_ind: fundefs -> list positive -> Prop :=
   | GEI_Fnil: get_allocs_fundefs_ind Fnil nil
   | GEI_Fcons:
       forall f t vs e fnd l l',
         get_allocs_ind e l ->
         get_allocs_fundefs_ind fnd l' ->
       get_allocs_fundefs_ind (Fcons f t vs e fnd)  (vs++l++l').



Theorem get_allocs_correct:
  (forall e,
      get_allocs_ind e (get_allocs e))
  /\
  (forall fds,
      get_allocs_fundefs_ind fds (get_allocs_fundefs fds)).
Proof.
  apply exp_def_mutual_ind'; intros; simpl;
    try (constructor; auto; fail);
    try (constructor; auto using app_nil_r; fail).
  - (* Ecase: need to build get_allocs_case_ind from Forall *)
    constructor. induction l as [| [z e0] l' IHl'].
    + constructor.
    + simpl in H. inv H.
      change (@nil positive) with ((@nil positive) ++ (@nil positive)).
      constructor; auto.
Qed.


  
(* TODO: write this to ensure that the GC nevers runs out of space in the middle of a function*)
Definition correct_alloc: exp -> Z -> Prop := fun e i => i =  Z.of_nat (max_allocs e ).

Theorem e_correct_alloc:
  forall e, exists i, correct_alloc e i.
Proof.
  intros.
  eexists. unfold correct_alloc. reflexivity.
Qed.



Theorem max_allocs_boxed: forall v c e l,
    l <> nil -> 
(max_allocs (Econstr v c l e) = 1 + (length l) + max_allocs e).
Proof.
  intros; simpl. induction l.
  exfalso; auto.
  destruct l. lia.
  simpl.
  simpl in IHl.
  rewrite <- IHl. lia.
  intro. inv H0.
Qed.


(* see make_fundef_info, this is w.r.t. some fenv, another prop should assert the fenv is correct w.r.t. all functions *)

Definition correct_fundef_info (m:mem) (f:positive) (t:fun_tag) (vs:list positive) e finfo :=
  exists n l b fi_0,
   (* the tag for f points to a record r *)
    M.get t fenv =  Some (n, l) /\
    n = N.of_nat (length l) /\
    length l = length vs /\
    (* no duplicate could be weaken if shared *)
    NoDup l /\
    Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z l /\
    (* id points to an array in global memory *)
    Genv.find_symbol (globalenv p) finfo = Some b /\
    
    (* 
 12/17 -- now looking this up in mem directly
Genv.find_var_info (globalenv p) b = Some finfo_init /\ 
*)
    
    (* the record has the right information w.r.t. vs and r 
       fi[0] = alloc(e)
       fi[1] = number of roots
       |fi| = 2+fi[1] *)
    Mem.loadv int_chunk m (Vptr b Ptrofs.zero) = Some (make_vint fi_0) /\
    
             Mem.loadv int_chunk m (Vptr b (Ptrofs.repr int_size)) = Some (make_vint (Z.of_N n)) /\

    (* gvar_init finfo_init = ((Init_int32 fi_0)::(Init_int32 fi_1)::fi_rest) /\ *)
             correct_alloc e fi_0 /\
             (int_size * fi_0 <= gc_size)%Z /\
                                         
    (forall (i:N), (i < n)%N ->
                   exists li, Mem.loadv int_chunk m (Vptr b (Ptrofs.repr (int_size*(Z.of_N (2+i)%N)))) = Some (make_vint (Z.of_N li)) /\
                                (nthN l i) = Some li).
(*
 12/17: probably need something w.r.t permissions 
/\

    (forall (j:N), (j < n + 2)%N -> 
        Mem.perm int_chunk m (Vptr b (Int.repr (int_size * (Z.of_N j)))) Readable) *)


              
(*     Forall2 (fun a i => exists i', i = Init_int32 i' /\ (Z.of_N a) = Int.unsigned i')  l fi_rest. *)
 
(* P is true of every fundefs in a bundle *)
(* TODO: move this to cps_util *)
Inductive Forall_fundefs: (cps.var -> fun_tag -> list cps.var -> exp -> Prop) -> fundefs -> Prop :=
| Ff_cons : forall (P:(cps.var -> fun_tag -> list cps.var -> exp -> Prop)) f t vs e fds,
         P f t vs e -> 
         Forall_fundefs P fds ->
         Forall_fundefs P (Fcons f t vs e fds)         
| Ff_nil: forall P, Forall_fundefs P Fnil.


Theorem Forall_fundefs_In:
  forall P f t vs e fds,
  Forall_fundefs P fds ->
  fun_in_fundefs fds (f,t,vs,e) ->
  P f t vs e.
Proof.
  induction fds; intros.
  - inv H; inv H0; subst.
    + inv H; auto.
    +  apply IHfds; auto.
  - inv H0.
Qed.
(* END TODO move *)


(* 1) finfo_env has the correct finfo
   2) fenv is consistent with the info
   3) global env holds a correct Codegen representation of the function *)
Definition correct_environments_for_function:
  genv -> fun_env -> M.t positive -> mem -> fundefs ->  cps.var ->
  fun_tag -> list cps.var -> exp ->  Prop
  := fun ge fenv finfo_env m fds f t vs e =>
       exists l locs finfo b, 
         (*1*)
         M.get f finfo_env = Some finfo /\
         correct_fundef_info m f t vs e finfo  /\
         (*2*)
         M.get t fenv = Some (l, locs) /\
         l = N.of_nat (length vs) /\
         (* may want to check that locs are distinct and same as in finfo? *)
         (*3*)
         Genv.find_symbol (globalenv p) f = Some b /\
         (* TODO: change this to repr_val_LambdaANF_Codegen *)
         repr_val_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m (Vptr b Ptrofs.zero).


Definition correct_environments_for_functions: fundefs -> genv -> fun_env -> M.t positive -> mem ->  Prop := fun fds ge fenv finfo_env m =>
                                                                                                            Forall_fundefs (correct_environments_for_function ge fenv finfo_env m fds) fds.


Definition is_protected_id  (id:positive)  : Prop :=
  List.In id protectedIdent.

Definition is_protected_tinfo_id (id:positive) : Prop :=
    id = allocIdent \/ id = limitIdent \/ id = argsIdent.

Theorem is_protected_tinfo_weak:
  forall x, is_protected_tinfo_id x ->
            is_protected_id x.
Proof.
  intros. unfold is_protected_tinfo_id in H. unfold is_protected_id, protectedIdent.
  repeat destruct H; subst; simpl; auto 20.
Qed.

                                               
(* Domain of find_symbol (globalenv p) is disjoint from bound_var e /\ \sum_rho (bound_var_val x \setminus names_in_fundef x) *)
(*  *)
Definition functions_not_bound (rho:eval.env) (e:exp): Prop :=
  (forall x,
    bound_var e x ->
    Genv.find_symbol (Genv.globalenv p) x = None)/\
  (forall x y v,
      M.get y rho = Some v ->
      bound_notfun_val v x ->
      Genv.find_symbol (Genv.globalenv p) x = None).



Inductive unique_bindings_val: cps.val -> Prop :=
| UB_Vfun: forall rho fds f,
    unique_bindings_fundefs fds ->
    unique_bindings_val (Vfun rho fds f)
| UB_Vconstr: forall c vs,
    Forall unique_bindings_val vs ->
    unique_bindings_val (Vconstr c vs)
|UB_VInt: forall z,
    unique_bindings_val (cps.Vint z)
.

      
(* UB + disjoint bound and in env *)
Definition unique_bindings_env (rho:eval.env) (e:exp) : Prop :=
      unique_bindings e  /\ 
      (forall x v,
        M.get x rho = Some v ->
    ~ bound_var e x /\ unique_bindings_val v). 

Theorem unique_bindings_env_prefix:
  forall e rho,
    unique_bindings_env rho e ->
    forall rho',
  prefix_ctx rho' rho ->
  unique_bindings_env rho' e.
Proof.
  intros.
  inv H.
  split; auto.
Qed.  


(* TODO: also need UB for the functions in rho
Theorem unique_bindings_env_weaken :
  unique_bindings_env rho e ->
  rho' subseteq rho
unique_bindings_env rho e *)

  
Lemma bound_var_dsubterm_e:
  forall e' e x,
    bound_var e' x -> dsubterm_e e' e -> bound_var e x.
Proof.
  intros e' e x Hbv Hsub. destruct Hsub.
  - apply Bound_Econstr2; auto.
  - apply Bound_Eproj2; auto.
  - apply Bound_Eprim_val2; auto.
  - apply Bound_Eprim2; auto.
  - apply Bound_Eletapp2; auto.
  - eapply Bound_Ecase; eauto.
  - apply Bound_Efun1. induction H.
    + apply Bound_Fcons3; auto.
    + apply Bound_Fcons2; auto.
  - apply Bound_Efun2; auto.
Qed.

Lemma bound_var_subterm_e:
  forall e' e x,
    bound_var e' x -> subterm_e e' e -> bound_var e x.
Proof.
  intros e' e x Hbv Hsub. induction Hsub.
  - eapply bound_var_dsubterm_e; eauto.
  - auto.
Qed.

Theorem functions_not_bound_subterm:
  forall rho e,
    functions_not_bound rho e ->
    forall e',
    subterm_e e' e ->
    functions_not_bound rho e'.
Proof.
  intros. split. intro; intros.
  apply H.
  eapply bound_var_subterm_e; eauto.
  apply H.
Qed.  

Theorem functions_not_bound_set:
    forall rho e y v,
      functions_not_bound rho e ->
      (forall x, bound_notfun_val v x -> Genv.find_symbol (globalenv p) x = None) ->
      functions_not_bound (M.set y v rho) e.
Proof.
  intros. split. apply H.
  intros. destruct (var_dec y0 y).
  - subst. rewrite M.gss in H1. inv H1. destruct H. apply H0. auto. 
  - rewrite M.gso in H1 by auto. inv H. eapply H4; eauto.
Qed.
    
Definition protected_id_not_bound  (rho:eval.env) (e:exp) : Prop :=
  (forall x y v, M.get x rho = Some v ->
                 is_protected_id  y ->
                 ~ (x = y \/ bound_var_val v y) )/\
  (forall y, is_protected_id  y ->
             ~ bound_var e y).


Theorem protected_id_not_bound_prefix:
  forall rho rho' e,
    protected_id_not_bound rho e ->
    prefix_ctx rho' rho ->
    protected_id_not_bound rho' e.
Proof.
  intros. inv H. split; intros.
  - apply H0 in H.
    apply H1; eauto.
  - eapply H2; eauto.
Qed.

 
    
Theorem find_def_bound_in_bundle:
  forall e y t xs f fds,
  bound_var e y ->
  find_def f fds = Some (t, xs, e) ->            
  bound_var_fundefs fds y.
Proof.
  induction fds; intros.
  simpl in H0. destruct (cps.M.elt_eq f v). inv H0. constructor 3; auto.
  constructor 2. apply IHfds; auto.
  inv H0.
Qed.
  
Theorem protected_id_not_bound_closure:
  forall rho e e' f' f fds rho' t xs,
    protected_id_not_bound rho e ->
    M.get f rho = Some (Vfun rho' fds f') ->
    find_def f' fds = Some (t, xs, e') ->
   protected_id_not_bound rho e'.
Proof.
  intros.
  inv H.
  split. auto.
  intros.
  intro.
  specialize (H2 _ _ _ H0 H).
  apply H2. right.
  constructor. 
  eapply find_def_bound_in_bundle; eauto.
Qed.

Theorem protected_id_closure:
  forall rho rho' f t0 ys fl f' t xs e' vs,
    protected_id_not_bound rho (Eapp f t0 ys) ->
    cps.M.get f rho = Some (Vfun (M.empty _) fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e') ->
    set_lists xs vs (def_funs fl fl (M.empty _) (M.empty _)) = Some rho' -> 
    protected_id_not_bound rho' e'.
Proof.
  intros.
  assert (protected_id_not_bound rho e') by (eapply protected_id_not_bound_closure; eauto).
  split. intros.
  assert (decidable (List.In x xs)). apply In_decidable. apply var_dec_eq. 
  inv H7.
  (* in vs *)
  { inv H.
    intro. inv H.
    - specialize (H7 _ _ _ H0 H6). apply H7. right.
      constructor. eapply shrink_cps_correct.name_boundvar_arg; eauto.
    - assert (List.In v vs) by (eapply set_lists_In; eauto).
      assert (Hgl := get_list_In_val _ _ _ _  H1 H). destruct Hgl.
      destruct H11. specialize (H7 _ _ _ H12 H6). apply H7. auto.
  }  
  erewrite <- set_lists_not_In in H5.
  2: eauto.
  2: eauto.
  assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
      inv H7.
        (*
          2) in fl *)
      rewrite def_funs_eq in H5. 2: eauto. inv H5.
      inv H.
      specialize (H5 _ _ _ H0 H6).
      intro. inv H.

      apply H5. right. constructor.
      apply name_in_fundefs_bound_var_fundefs. auto.

      apply H5. right. constructor. inv H10. auto.
      
      rewrite def_funs_neq in H5. 2: eauto.
      rewrite M.gempty in H5. inv H5.
        
        apply H4.
Qed.

Inductive empty_cont: cont -> Prop :=
| Kempty_stop: empty_cont Kstop
| Kempty_switch: forall k, empty_cont k ->
                           empty_cont (Kswitch k)
| Kempty_sbreak: forall k, empty_cont k ->
                           empty_cont (Kseq Sbreak k)
| Kempty_sskip: forall k, empty_cont k ->
                           empty_cont (Kseq Sskip k)
.
About int_size.
                                      
Definition protected_non_reachable_val_Codegen v6 m v7 (lenv:temp_env) : Prop :=
      exists alloc_b alloc_ofs limit_b limit_ofs args_b args_ofs,
        M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
        ~reachable_val_Codegen v6 m v7 alloc_b alloc_ofs /\
        M.get limitIdent lenv = Some (Vptr limit_b limit_ofs) /\
        ~reachable_val_Codegen v6 m v7 limit_b limit_ofs /\
        M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
        (forall i,
            Ptrofs.ltu i (Ptrofs.repr max_args) = true ->                   
            ~reachable_val_Codegen v6 m v7 args_b (Ptrofs.add args_ofs (Ptrofs.mul (Ptrofs.repr int_size) i))).

(* true if alloc, limit or args *)
Definition is_protected_loc lenv b ofs : Prop  :=
  M.get allocIdent lenv = Some (Vptr b ofs)
  \/
  M.get limitIdent lenv = Some (Vptr b ofs)
  \/
  (exists args_ofs i, M.get argsIdent lenv = Some (Vptr b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * i))))%Z /\
                      (0 <= i < max_args)%Z).


(* L is the current allocated memory for user's datastructure
   space between alloc_ofs and limit_ofs is not in L
   anything in the args array is not in L
   tinfo is not in L
   anything pointed to by global env is not in L 
*)
   
Definition protected_not_in_L (lenv:temp_env)  (L:block -> Z -> Prop): Prop :=
  exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
    (forall j : Z, ((Ptrofs.unsigned alloc_ofs) <= j <
                    Ptrofs.unsigned limit_ofs)%Z  ->
                   ~ L alloc_b j) /\
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
(*         (forall j : Z, ((Int.unsigned limit_ofs) <= j <
                    Int.unsigned limit_ofs + size_chunk int_chunk)%Z  ->
                   ~ L alloc_b_b j) *)
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
          (forall z j: Z,
              (0 <= z < max_args)%Z -> 
              ((Ptrofs.unsigned  (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z))))
               <= j <
               (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr (int_size * z)))) +  int_size)%Z ->

              ~ L args_b j) /\
          (* tinfo_b is disjoint from L *)
          M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
          (forall i, ~ L tinf_b i) /\
          (* anything pointed out by the global env is disjoint from l *)
          (forall x b,
              Genv.find_symbol (globalenv p) x = Some b ->
              b <> args_b /\ b <> alloc_b   (* these are also covered by correct_tinfo, but convenient here *)
            /\  
              forall i, ~ L b i) 
.

Theorem protected_not_in_L_proper:
  forall lenv lenv' L,
    protected_not_in_L lenv L ->
      map_get_r_l _ (cons argsIdent (cons limitIdent (cons allocIdent (cons tinfIdent nil)))) lenv lenv' ->
      protected_not_in_L lenv' L.
Proof.
  intros.
  inv H. destructAll. rewrite H0 in *; inList.
  do 7 eexists. repeat split; eauto.
  eapply H7; eauto.
  eapply H7; eauto.
  eapply H7; eauto. 
Qed.
  
Theorem protected_not_in_L_proper_weak:
  forall lenv lenv' L ,
  map_get_r _ lenv lenv' ->
  protected_not_in_L lenv  L ->
  protected_not_in_L lenv'  L.
Proof.
  intros.
  eapply protected_not_in_L_proper. eauto.
  intro. intro. apply H.
Qed.
 
Theorem protected_not_in_L_set:
  forall lenv  L x v ,
  protected_not_in_L lenv  L ->
  ~ is_protected_tinfo_id x ->
  x <> tinfIdent ->
  protected_not_in_L (M.set x v lenv)  L.
Proof.
  intros.
  destruct H.
  destructAll.
  exists x0, x1, x2, x3, x4, x5, x6.
  repeat split;auto.
  - destruct (var_dec allocIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      left; auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec limitIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      right; auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec argsIdent x).
    + exfalso; apply H0.
      rewrite <- e.
      unfold is_protected_id.
      right; auto.
    +  rewrite M.gso by auto. auto.
  - rewrite M.gso; auto.
  - eapply H8; eauto.
  - eapply H8; eauto.
  - eapply H8; eauto.
Qed.

Theorem protected_not_in_L_union :
  forall lenv L1 L2,
    protected_not_in_L lenv L1 ->
    protected_not_in_L lenv L2 ->
    protected_not_in_L lenv (fun b ofs => L1 b ofs \/ L2 b ofs).
Proof.
  intros lenv L1 L2 Hprot1 Hprot2.
  destruct Hprot1 as [alloc_b1 [alloc_ofs1 [limit_ofs1 [args_b1 [args_ofs1 [tinf_b1 [tinf_ofs1
    [Halloc1 [HallocL1 [Hlimit1 [Hargs1 [HargsL1 [Htinf1 [HtinfL1 Hglob1]]]]]]]]]]]]]].
  destruct Hprot2 as [alloc_b2 [alloc_ofs2 [limit_ofs2 [args_b2 [args_ofs2 [tinf_b2 [tinf_ofs2
    [Halloc2 [HallocL2 [Hlimit2 [Hargs2 [HargsL2 [Htinf2 [HtinfL2 Hglob2]]]]]]]]]]]]]].

  rewrite Halloc1 in Halloc2.
  inversion Halloc2; subst alloc_b2 alloc_ofs2.
  rewrite Hlimit1 in Hlimit2.
  inversion Hlimit2; subst limit_ofs2.
  rewrite Hargs1 in Hargs2.
  inversion Hargs2; subst args_b2 args_ofs2.
  rewrite Htinf1 in Htinf2.
  inversion Htinf2; subst tinf_b2 tinf_ofs2.

  exists alloc_b1, alloc_ofs1, limit_ofs1, args_b1, args_ofs1, tinf_b1, tinf_ofs1.
  split; [exact Halloc1|].
  split.
  - intros j Hj [HL1 | HL2].
    + eapply HallocL1; eauto.
    + eapply HallocL2; eauto.
  - split; [exact Hlimit1|].
    split; [exact Hargs1|].
    split.
    + intros z j Hz Hj [HL1 | HL2].
      * eapply HargsL1; eauto.
      * eapply HargsL2; eauto.
    + split; [exact Htinf1|].
      split.
      * intros i [HL1 | HL2].
        -- eapply HtinfL1; eauto.
        -- eapply HtinfL2; eauto.
      * intros x0 b0 Hsym.
        specialize (Hglob1 x0 b0 Hsym) as [Hneq_args [Hneq_alloc Hnot1]].
        specialize (Hglob2 x0 b0 Hsym) as [_ [_ Hnot2]].
        split; [exact Hneq_args|].
        split; [exact Hneq_alloc|].
        intros i [HL1 | HL2].
        -- eapply Hnot1; eauto.
        -- eapply Hnot2; eauto.
Qed.

Theorem lenv_param_refl :
  forall lenv lenv' vs, 
  lenv_param_asgn lenv lenv' [] vs
  -> map_get_r _ lenv lenv'.
Proof.
  intros.
  intro.
  specialize (H v).
  destruct H.
  symmetry.
  apply H0.
  intro.
  inv H1.
Qed.
 
Theorem lenv_param_asgn_not_in:
  forall lenv lenv' b ofs x (L:positive -> Prop) xs vs7,
M.get x lenv = Some (Vptr b ofs) ->
  L x ->
  (forall x6 : positive, List.In x6 xs -> ~ L x6) ->
  lenv_param_asgn lenv lenv' xs vs7 ->
  M.get x lenv' = Some (Vptr b ofs).
Proof.
  intros.
  specialize (H2 x).
  destruct H2.
  rewrite H3.
  auto.
  intro.
  eapply H1; eauto.
Qed.


Theorem lenv_param_asgn_map:
  forall lenv lenv' xs vs7 l,
  lenv_param_asgn lenv lenv' xs vs7 ->
  Disjoint _ (FromList xs) (FromList l) ->
  map_get_r_l _ l lenv lenv'.
Proof.  
  intros.
  intro.
  intro.
  specialize (H v); destruct H.
  rewrite H2.
  auto.
  inv H0. specialize (H3 v).
  intro.
  apply H3.
  auto.
Qed.

  
  Theorem protected_not_in_L_asgn:
  forall L xs vs7 lenv lenv',
protected_not_in_L lenv  L ->
lenv_param_asgn lenv lenv' xs vs7 ->
(forall x, List.In x xs -> ~ (is_protected_tinfo_id x \/ x = tinfIdent)) ->
protected_not_in_L lenv'  L.
  Proof.
    intros.
    inv H; destructAll.
    exists x, x0, x1, x2, x3, x4, x5.
    
    repeat split; auto; try (eapply lenv_param_asgn_not_in with (L :=  fun x => (is_protected_tinfo_id x \/ x = tinfIdent)); eauto).
    left; inList. left; inList.
    left; inList. reflexivity.
    eapply H8; eauto.
    eapply H8; eauto.
    eapply H8; eauto.
  Qed.    

  (* no longer needed without max_alloc *)
      (* Mono + extra assumptions to avoid overflow 
Theorem protected_not_in_L_mono:
  forall lenv alloc_b alloc_ofs z limit_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    ((Int.unsigned alloc_ofs) + int_size * z <=  Int.unsigned limit_ofs)%Z -> 
    forall L z', 
   protected_not_in_L lenv z L ->   
  (0 <= z' <= z)%Z ->
  protected_not_in_L lenv z' L.
Proof.
  intros.
  inv H2. destructAll.
  rewrite H4 in H. inv H.
  rewrite H6 in H0. inv H0.
  exists alloc_b, alloc_ofs, limit_ofs.
  do 4 (eexists). 
  repeat split; eauto.  
  intros. apply H5.
  unfold int_size in *; simpl size_chunk in *.
  assert (Int.unsigned limit_ofs <= Int.max_unsigned)%Z by apply Int.unsigned_range_2 .
  assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range_2 .
  unfold Int.add in *.
  rewrite Int.unsigned_repr with (z := (4 * z)%Z) by lia.
  rewrite Int.unsigned_repr with (z := (4 * z')%Z) in H by lia.
  rewrite Int.unsigned_repr by lia.
  rewrite Int.unsigned_repr in H by lia. lia.
  apply H11 in H; destructAll; auto.
  apply H11 in H; destructAll; auto.
  apply H11 in H; destructAll; auto.
Qed. *)
 
   
Definition Vint_or_Vconstr (v:cps.val): Prop :=
  (exists i, v = cps.Vint i) \/ (exists c vs, v = cps.Vconstr c vs).

Definition correct_fundef_id_info (m:mem) (fds:fundefs) (f:positive) :=
            exists finfo t t' vs e, (find_def f fds = Some (t, vs, e) /\                          
                                     M.get f finfo_env = Some (finfo , t') /\
                                     t = t' /\
                                     correct_fundef_info  m f t vs e finfo).

(* relates a LambdaANF evaluation environment to a Clight memory up to the free variables in e *)
(* If x is a free variable of e, then it might be in the generated code:
   1) a function (may want to handle this separately as they won't get moved by the GC) in the global environment, evaluates to a location related to f by repr_val_ptr_LambdaANF_Codegen
   2) a local variable in le related to (rho x) according to repr_val_LambdaANF_Codegen -- this happens when e.g. x := proj m, or after function initialization

All the values are in a space L which is disjoint form protected space

Note that parameters are heap allocated, and at function entry "free variables" are held in args and related according to repr_val_ptr_LambdaANF_Codegen
 
Now also makes sure none of the protected portion are reachable by the v7

TODO: second section needs that for any such f s.t. find_def f fl = Some (t, vs4, e),  e is closed by  var (FromList vsm4 :|: name_in_fundefs fl)
 may want something about functions in rho, i.e. that they don't need to be free to be repr_val_id, since they are the only thing that may appear free in other functions body (and not bound in the opening 
may need rho' also has the Vfun 
 *) 

    Definition rel_mem_LambdaANF_Codegen: exp -> eval.env -> mem -> temp_env -> Prop :=
      fun e rho m le =>
        exists L, protected_not_in_L le L /\
        (forall x,          
        (occurs_free e x ->
                  exists v6, M.get x rho = Some v6 /\
                             repr_val_id_L_LambdaANF_Codegen v6 m L le x)
        /\
        (forall rho' fds f v,
            M.get x rho = Some v ->
            subval_or_eq (Vfun rho' fds f) v ->
            repr_val_id_L_LambdaANF_Codegen (Vfun rho' fds f) m L le f /\
            closed_val (Vfun rho' fds f) /\
            correct_fundef_id_info m fds f)).
(* 
    Theorem rel_mem_LambdaANF_Codegen_set_vconstr:
      rel_mem_LambdaANF_Codegen e rho m lenv ->
      rel_mem_LambdaANF_Codegen e rho m (M.set x (Vconstr c vs)) *)

    (* this is wrong, the block after limit may be in L
    Theorem protected_not_L:
      forall e le b ofs L, 
      protected_not_in_L le (Z.of_nat (max_allocs e)) L ->
      is_protected_loc le b (Int.repr ofs) -> forall i : Z, (ofs <= i < ofs + size_chunk int_chunk)%Z -> ~ L b i. *)

Definition unchanged_globals: mem -> mem -> Prop :=
  fun m m' =>
    forall x b,
      Genv.find_symbol (globalenv p) x = Some b ->
      forall i chunk, Mem.loadv chunk m (Vptr b i) =  Mem.loadv chunk m' (Vptr b i).

Theorem unchanged_globals_trans:
  forall m1 m2 m3,
    unchanged_globals m1 m2 ->
    unchanged_globals m2 m3 ->
    unchanged_globals m1 m3.
Proof.
  intros.
  intro; intros.
  specialize (H _ _ H1 i chunk).
  specialize (H0 _ _ H1 i chunk).
  rewrite H; rewrite H0.
  reflexivity.
Qed.

Theorem correct_fundefs_unchanged_global:
  forall m m' fds f, 
    correct_fundef_id_info m fds f ->
    unchanged_globals m m' ->
    correct_fundef_id_info m' fds f.
Proof.
  intros.
  destruct H as [finfo [t [t' [vs [e H]]]]].
  exists finfo, t, t', vs, e.
  destruct H. destruct H1. destruct H2.
  split; auto.
  split; auto.
  split; auto.
  destruct H3 as [n [l [b [fi_0 [fi_1 H3]]]]].
  exists n, l, b, fi_0.
  destructAll.
  repeat split; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
  intros.
  apply H12 in H2.
  destruct H2 as [li H2].
  exists li.
  destructAll.
  split; auto.
  specialize (H0 finfo b); rewrite <- H0; auto.
Qed.

 
Theorem store_globals_unchanged:
  forall b' i m m' a,
     Mem.store int_chunk m b' i a = Some m' ->
 (forall (x : ident) (b : block),
          Genv.find_symbol (globalenv p) x = Some b -> b <> b') ->
  unchanged_globals m m'. 
Proof.
  intros. 
  intro; intros. apply H0 in H1.
  symmetry.
  eapply Mem.load_store_other. apply H.
  auto.
Qed.

Theorem mem_after_n_proj_store_globals_unchanged:
  forall b' i vs z  m m',
  mem_after_n_proj_store b' i vs z m m' ->
 (forall (x : ident) (b : block),
          Genv.find_symbol (globalenv p) x = Some b -> b <> b') ->
  unchanged_globals m m'. 
Proof.
  induction vs; intros. inv H.
  inv H.
  - eapply store_globals_unchanged; eauto.
  - specialize (IHvs _ _ _ H9 H0).
    eapply unchanged_globals_trans; eauto.
    eapply store_globals_unchanged; eauto. 
Qed.


Theorem rel_mem_update_protected:
  forall e rho m le args_b args_ofs i v m',
    rel_mem_LambdaANF_Codegen e rho m le ->
    M.get argsIdent le = Some (Vptr args_b args_ofs) ->
    (0 <= Z.of_N i < max_args)%Z ->
    Mem.store int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs  (Ptrofs.repr (int_size * Z.of_N i)))) v = Some m' ->
    rel_mem_LambdaANF_Codegen e rho m' le. 
Proof. 
  intros. destruct H as [L Hrel_mem].
  destruct Hrel_mem as [Hprotect Hof_v].      
  exists L.
  split; auto.
  intro.
  specialize (Hof_v x).
  destruct Hof_v as [Hof_v1 Hof_v2].
  split.
  * intros. apply Hof_v1 in H. 
    destructAll. exists x0. split; auto.
    eapply repr_val_id_L_unchanged.
    eauto.
    eapply Mem.store_unchanged_on. eauto.
    intros.
    inv Hprotect. destructAll. rewrite H10 in H0. inv H0.
    eapply H11. eauto. unfold int_size in *.
    split; auto.
    
  * intros. 
    specialize (Hof_v2 _ _ _ _ H H3). 
    destruct Hof_v2 as [Hof_v2 [Hv2_closed Hv2_f]]. split.
    eapply repr_val_id_L_unchanged.
    eauto.
    eapply Mem.store_unchanged_on. eauto.
    intros.     inv Hprotect. destructAll. rewrite H10 in H0. inv H0.
    eapply H11. eauto. unfold int_size in *.
    split; auto.
    auto.
    split. auto.
    eapply correct_fundefs_unchanged_global.
    eauto.
    intro finfo; intros. 
    inv Hprotect. destructAll.
    symmetry. eapply Mem.load_store_other.
    eauto. left.
    rewrite H9 in H0; inv H0. eapply H13. eauto.
Qed.
  
 Fixpoint mem_of_state (s:state) : mem :=
  match s with
  | State f s k e le m => m
  | Callstate f vs k m => m
  | Returnstate x k m =>  m
  end.


  
(* [pure] step with no built-in, i.e. trace is always E0 *)
Definition traceless_step2:  genv -> state -> state -> Prop := fun ge s s' => step2 ge s nil s'. 

Definition m_tstep2 (ge:genv):=  clos_trans state (traceless_step2 ge).

Lemma m_tstep2_step :
  forall ge s s',
    traceless_step2 ge s s' ->
    m_tstep2 ge s s'.
Proof.
  intros ge s s' Hstep.
  apply t_step.
  exact Hstep.
Qed.

Lemma m_tstep2_transitive :
  forall ge s1 s2 s3,
    m_tstep2 ge s1 s2 ->
    m_tstep2 ge s2 s3 ->
    m_tstep2 ge s1 s3.
Proof.
  intros ge s1 s2 s3 H12 H23.
  eapply t_trans; eauto.
Qed.

Lemma m_tstep2_seq_set :
  forall p0 fu k lenv m x rhs s v,
    eval_expr (globalenv p0) empty_env lenv m rhs v ->
    m_tstep2 (globalenv p0)
      (State fu (Ssequence (Sset x rhs) s) k empty_env lenv m)
      (State fu s k empty_env (M.set x v lenv) m).
Proof.
  intros p0 fu k lenv m x rhs s v Heval.
  eapply m_tstep2_transitive.
  - apply m_tstep2_step.
    constructor.
  - eapply m_tstep2_transitive.
    + apply m_tstep2_step.
      constructor.
      exact Heval.
    + apply m_tstep2_step.
      constructor.
Qed.

Lemma m_tstep2_of_rt :
  forall ge s1 s2,
    clos_refl_trans state (traceless_step2 ge) s1 s2 ->
    forall s3,
      m_tstep2 ge s2 s3 ->
      m_tstep2 ge s1 s3.
Proof.
  intros ge s1 s2 Hrt.
  induction Hrt; intros s3 H23.
  - eapply m_tstep2_transitive.
    + apply m_tstep2_step. exact H.
    + exact H23.
  - exact H23.
  - eapply IHHrt1.
    eapply IHHrt2.
    exact H23.
Qed.

Lemma m_tstep2_of_rt_then_step :
  forall ge s1 s2 s3,
    clos_refl_trans state (traceless_step2 ge) s1 s2 ->
    traceless_step2 ge s2 s3 ->
    m_tstep2 ge s1 s3.
Proof.
  intros ge s1 s2 s3 Hrt Hstep.
  eapply m_tstep2_of_rt; eauto.
  apply m_tstep2_step. exact Hstep.
Qed.

#[local] Hint Unfold Ptrofs.modulus Ptrofs.max_unsigned uint_range : core.
#[local] Hint Transparent Ptrofs.max_unsigned Ptrofs.modulus uint_range : core.
 
Inductive mem_after_n_proj_store_rev: block -> Z -> (list Values.val) -> mem -> mem -> Prop :=
| Mem_last_ind: forall m b ofs v m', 
    Mem.store int_chunk m b ofs v = Some m' ->
    mem_after_n_proj_store_rev b ofs [v] m m'
| Mem_next_ind:
    forall b ofs vs v m m' m'', 
    mem_after_n_proj_store_rev b (ofs + int_size) vs m m' ->
    Mem.store int_chunk m' b ofs v = Some m'' ->
    mem_after_n_proj_store_rev b ofs (v::vs) m m''.
  
Theorem set_commute:
  forall A (vx vy:A) (x y:positive) rho,
    x <> y ->
    M.set x vx (M.set y vy rho) = M.set y vy  (M.set x vx rho).
Proof.
  intros. apply M.extensionality. intros i.
  rewrite !M.gsspec.
  destruct (Coqlib.peq i x), (Coqlib.peq i y); subst; try reflexivity; congruence.
Qed.
  





Theorem mem_of_Forall_nth_projection_cast:
  forall x lenv b ofs f, 
    find_symbol_domain finfo_env ->
    finfo_env_correct ->
    M.get x lenv = Some (Vptr b ofs) ->
    forall l s i m k,
      (0 <= i /\ i + (Z.of_nat (List.length l)) <= Ptrofs.max_unsigned )%Z ->
      (forall j, 0 <= j < i + Z.of_nat (List.length l) -> Mem.valid_access m int_chunk b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr  (int_size * j)))) Writable)%Z ->
      Forall_statements_in_seq'
        (is_nth_projection_of_x x) l s i ->
      forall vs, 
      Forall2 (get_var_or_funvar lenv) l vs ->
      exists m', m_tstep2 (globalenv p) (State f s k empty_env lenv m)
               (State f Sskip k empty_env lenv m') /\ 
      mem_after_n_proj_store_cast b (Ptrofs.unsigned ofs) vs i m m'.
Proof with archi_red.
  intros x lenv b ofs f Hsym HfinfoCorrect Hxlenv.
  induction l; intros s i m k Hil_max; intros.
  - (* empty -- impossible *)
    inv H1. inv H0.
  -   assert (length (a :: l) = length vs) by (eapply Forall2_length'; eauto). rewrite H2 in *. clear H2.
      assert (Hi_range : uint_range i) by solve_uint_range.
     inv H1.
     assert (Hvas :  Mem.valid_access m int_chunk b
                                      (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size * i))))
                                      Writable).
     apply H. simpl. split.
     lia.
     rewrite <- Z.add_0_r with (n := i) at 1.
     apply Z.add_lt_mono_l.
     apply Pos2Z.is_pos.
     assert (Hvra := Mem.valid_access_store m int_chunk b  (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size* i)))) y Hvas).
     destruct Hvra as [m2 Hsm2].        
     inv H0.
     + (* last statement *)
       inv H6.
       inv H8.
       exists m2.
       split.
       2:{
       constructor. rewrite Ptrofs.repr_unsigned. auto. }
       inv H0.
       * inv H4. 
         2:{ exfalso. rewrite H1 in H0. inv H0. }
         
         rewrite H1 in H0; inv H0.
         constructor.
          
         destruct (Archi.ptr64) eqn:Harchi.
         {
           econstructor.
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         archi_red. constructor.
         archi_red. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         econstructor.  apply eval_Evar_global.  apply M.gempty.

         apply H1. constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor.
         eapply assign_loc_value.

         2:{ unfold Ptrofs.of_int64.
         rewrite Int64.unsigned_repr in *.
         rewrite int_z_mul. archi_red. apply Hsm2.
         solve_uint_range. archi_red. unfold Int64.max_unsigned. simpl; lia.
         archi_red. auto. }
         archi_red. reduce_val_access.
         constructor. }
         {
           econstructor.
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         archi_red. constructor.
         archi_red. constructor.

         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         econstructor. apply eval_Evar_global.  apply M.gempty.
         apply H1. constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor.
         eapply assign_loc_value.


         2:{ unfold ptrofs_of_int.  unfold Ptrofs.of_intu.
         unfold Ptrofs.of_int.
         rewrite Int.unsigned_repr in *.
         rewrite int_z_mul. archi_red. apply Hsm2.
         solve_uint_range. archi_red. solve_uint_range. lia.
         archi_red. auto. }
         archi_red. reduce_val_access.
         constructor.
         }
       * inv H4. exfalso; rewrite H1 in H0; inv H0.         
         constructor.
         destruct (Archi.ptr64) eqn:Harchi... 

         {
           eapply step_assign with (v2 := y) (v := y). 
           constructor. econstructor. econstructor.
           econstructor. apply Hxlenv. constructor.
           constructor. constructor. constructor. apply H2.
           simpl. destruct y; inv H3; auto.
           eapply assign_loc_value. 2:{  unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *.
           rewrite int_z_mul. archi_red. eauto. solve_uint_range.
           archi_red. unfold Int64.max_unsigned. simpl; lia.
           archi_red. auto. auto. } 
           constructor. }
         {
           eapply step_assign with (v2 := y) (v := y). 
           constructor. econstructor. econstructor.
           econstructor. apply Hxlenv. simpl. unfold sem_cast. simpl. try rewrite Harchi. constructor.
           constructor. constructor. constructor. apply H2.
           simpl.  destruct y; inversion H3; auto. try (simpl in H3; rewrite H3 in Harchi; inv Harchi).
           unfold sem_cast. simpl. try rewrite Harchi. try constructor.
           eapply assign_loc_value.
           2:{ unfold ptrofs_of_int. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
           rewrite Int.unsigned_repr. 
           rewrite int_z_mul. eauto. solve_uint_range.
           archi_red. solve_uint_range. lia.
           archi_red. auto.
           solve_uint_range. }
           archi_red. reduce_val_access. constructor. }
         
     +  (* IH *)
       inv H9.
       eapply IHl with (m := m2) in H5; eauto. destruct H5 as [m3 [H5a H5b]]. exists m3.       
       split.
       2:{ econstructor. rewrite Ptrofs.repr_unsigned. apply Hsm2. apply H5b. }

       inv H0.
       * inv H4.
         2:{ exfalso; rewrite H1 in H0; inv H0. }
         rewrite H1 in H0; inv H0.
         eapply t_trans.
         econstructor.  constructor.
         (* branch here *)
         destruct (Archi.ptr64) eqn:Harchi... 
         { 
         eapply t_trans. constructor. econstructor.
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor. 
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3. econstructor.   
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.  
         apply eval_Evar_global. apply M.gempty. eauto.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4. 
         constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4.
         constructor. eapply assign_loc_value. reduce_val_access. constructor.
          unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *. 
           rewrite int_z_mul. eauto. solve_uint_range.
           archi_red. unfold Int64.max_unsigned. simpl; lia.
           archi_red. auto. auto. 
         eapply t_trans. constructor. constructor.
         apply H5a. }
         { 
         eapply t_trans. constructor. econstructor.
         constructor. econstructor. econstructor. constructor. eauto. unfold sem_cast. simpl. archi_red. constructor.
         constructor. constructor.
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3.
         specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4. 
         econstructor.          
         apply eval_Evar_global.  apply M.gempty. eauto. constructor. constructor.
         unfold sem_cast. simpl. archi_red. 
         specialize (Hsym a). inv Hsym.
         destruct (H2 (ex_intro _ b1 H1)). destruct x0.
         unfold makeVar. rewrite H3. specialize (HfinfoCorrect _ _ _ H3). inv HfinfoCorrect.
         destruct x0. rewrite H4. constructor.  eapply assign_loc_value.
         2:{ unfold ptrofs_of_int. unfold Ptrofs.of_intu.
           unfold Ptrofs.of_int.
           rewrite Int.unsigned_repr.
           rewrite int_z_mul. archi_red. apply Hsm2.
           solve_uint_range. archi_red. solve_uint_range. lia.
           archi_red. auto.
           solve_uint_range. }
         reduce_val_access. constructor.
         eapply t_trans. constructor. constructor.
         apply H5a. }

       * inv H4. exfalso; rewrite H1 in H0; inv H0.
         (* branch here *)
         destruct (Archi.ptr64) eqn:Harchi... 
{         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. eapply step_assign with (v2 := y) (v := y). 
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor. econstructor. auto. simpl.
         destruct y; inv H3; auto.
         eapply assign_loc_value.
         2:{ unfold Ptrofs.of_int64.
           rewrite Int64.unsigned_repr in *.

           rewrite int_z_mul. apply Hsm2. solve_uint_range.  archi_red; eauto.
           unfold Int64.max_unsigned; simpl; lia. archi_red; auto. auto. }
           reduce_val_access. constructor.
         eapply t_trans. constructor. constructor.
         apply H5a. }

{         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. eapply step_assign with (v2 := y) (v := y).
         constructor. econstructor. econstructor. constructor. eauto. unfold sem_cast.
         simpl. archi_red. constructor.
         constructor.
         constructor. constructor.  auto. simpl.
         destruct y; inversion H3; auto. try (simpl in H3; rewrite H3 in Harchi; inv Harchi).
         unfold sem_cast. simpl. try rewrite Harchi. try constructor.
         eapply assign_loc_value.
         2:{ unfold ptrofs_of_int. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
           rewrite Int.unsigned_repr.
           rewrite int_z_mul. apply Hsm2. solve_uint_range.
           archi_red. solve_uint_range. lia.
           archi_red. auto. auto. }
         reduce_val_access. constructor.
         eapply t_trans. constructor. constructor.
         apply H5a. }


       * destruct Hil_max.
         split. apply Z.lt_le_incl. apply Z.lt_succ_r. auto.
         simpl in H2. rewrite Zpos_P_of_succ_nat in H2. rewrite Z.add_succ_comm. 
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).         
         rewrite Hll' in *. auto.
       * intros.
         eapply Mem.store_valid_access_1. apply Hsm2.
         apply H. simpl.
         rewrite Zpos_P_of_succ_nat.
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).         
         rewrite Hll' in *. 
         lia.
Defined.







End RELATION.


 

Section THEOREM.


Ltac archi_red :=
  int_red;
  unfold int_chunk in *;
  unfold val in *;
  unfold uval in *;
  unfold val_typ in *;
  unfold Init_int in *;
  unfold make_vint in *;
  unfold c_int' in *;
  unfold uint_range in *;
  try (rewrite ptrofs_mu in *);
  (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H in *)
   end).

Ltac reduce_val_access :=
  try unfold Ctypes.access_mode;
  try unfold Clight.typeof;
  try unfold AST.Mptr;
  try (match goal with
   | [ H : Archi.ptr64 = _ |- _] => try (rewrite H); try (cbv beta iota)
   end).

(* these ltac are agnostic on archi, useful for automation *)
   Ltac ptrofs_of_int :=
     unfold Ptrofs.of_int64 in *;
     unfold ptrofs_of_int in *;
     unfold Ptrofs.of_intu in *;
     unfold Ptrofs.of_int in *.

   Ltac int_unsigned_repr :=
     try (rewrite Int64.unsigned_repr in *);
     try (rewrite Int.unsigned_repr in *).
          
   Ltac int_max_unsigned:=  
     try (rewrite Int64.max_unsigned in *);
     try (rewrite Int.max_unsigned in *).
     


  
Notation vval := val. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Notation uval := val.

Notation valPtr := (Tpointer vval
                            {| attr_volatile := false; attr_alignas := None |}).


  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (bodyName : bytestring.String.t).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).
  Variable (prims : LambdaANF.toplevel.prim_env).

  Definition protectedIdent_thm := protectedIdent argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent.
  Variable (disjointIdent: NoDup protectedIdent_thm).
  
  Definition protectedNotTinfoIdent_thm: list ident := (gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).

  
  Definition is_protected_id_thm := is_protected_id argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent. 

  Definition is_protected_tinfo_id_thm := is_protected_tinfo_id argsIdent allocIdent limitIdent.

  Definition repr_val_id_L_LambdaANF_Codegen_thm := repr_val_id_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.

  Definition repr_val_LambdaANF_Codegen_thm := repr_val_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.
  


Theorem is_protected_not_tinfo:
  forall x, List.In x protectedNotTinfoIdent_thm ->
            ~ is_protected_tinfo_id_thm x.
Proof.
 intros.  
 intro.
 assert (H_dj := disjointIdent).
 inv H_dj. inv H4. inv H6. 
 inv H0.
 apply H5. right; auto.
 inv H1.
 apply H4; auto.
  apply H3. right; right; auto.
Qed.

Lemma caseIdent_is_protected :
  is_protected_id_thm caseIdent.
Proof.
  unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
  inList.
Qed.

Lemma caseIdent_not_tinfo :
  ~ is_protected_tinfo_id_thm caseIdent.
Proof.
  eapply is_protected_not_tinfo.
  unfold protectedNotTinfoIdent_thm.
  inList.
Qed.
 
(*
    Variable cenv:cps.ctor_env.
  Variable fenv:cps.fun_env.
  Variable finfo_env: M.t positive. (* map from a function name to its type info *)
  Variable p:program.
  
  
  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.
*)


  (* TODO: move this to cps_util *)
  Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) := 
    forall x t  ys e',
      subterm_or_eq (Econstr x t ys e') e -> P x t ys.
      

  Definition Forall_projections_in_e (P: var -> ctor_tag -> N -> var -> Prop) (e:exp) :=
    forall x t n v e',
      subterm_or_eq (Eproj x t n v e') e -> P x t n v.
  
  (* Note: the fundefs in P is the whole bundle, not the rest of the list *)
  Definition Forall_functions_in_e (P: var -> fun_tag -> list var -> exp ->  fundefs -> Prop) (e:exp) :=
    forall fds e' f t xs e'',  subterm_or_eq (Efun fds e') e ->
                               fun_in_fundefs fds (f, t, xs, e'') ->
                               P f t xs e'' fds.


  Definition Forall_exp_in_caselist (P: exp -> Prop) (cl:list (ctor_tag * exp)) := 
    forall g e, List.In (g, e) cl -> P e.



  
  Theorem crt_incl_ct:
          forall T P e e', 
          clos_trans T P e e' ->
          clos_refl_trans T P e e'.
  Proof.
    intros. induction H. constructor; auto.
    eapply rt_trans; eauto.
  Qed.    
    
  Theorem Forall_constructors_subterm:
    forall P e e' ,
    Forall_constructors_in_e P e ->
    subterm_e e' e ->
    Forall_constructors_in_e P e'. 
  Proof.
    intros. intro; intros.
    eapply H.
    assert (subterm_or_eq e' e).
    apply crt_incl_ct.
    apply H0.
    eapply rt_trans; eauto.
  Qed.
 
   
  (* END TODO move *)

  (* all constructors in the exp exists in cenv and are applied to the right number of arguments 
    May want to have "exists in cenv" also true for constructors in rho *)
  Definition correct_cenv_of_exp: cps.ctor_env -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (Build_ctor_ty_info _ _ _ a _) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.

  Definition correct_cenv_of_caselist: cps.ctor_env -> list (ctor_tag * exp) -> Prop :=
    fun cenv cl =>
      Forall_exp_in_caselist (correct_cenv_of_exp cenv) cl.


  
  Theorem correct_cenv_of_case:
    forall cenv v l, 
      correct_cenv_of_exp cenv (Ecase v l) ->
      correct_cenv_of_caselist cenv l.
  Proof.
    intros; intro; intros.
    eapply Forall_constructors_subterm. apply H.
    constructor. econstructor. eauto.
  Qed.  

  Theorem Forall_constructors_in_constr:
  forall P x t ys e,
  Forall_constructors_in_e P (Econstr x t ys e) ->
  P x t ys.
  Proof.
    intros.
    unfold Forall_constructors_in_e in *.
    eapply H.
    apply rt_refl.
  Qed.


  
  Theorem nodup_test:
    forall (x1 x2 x3 x4 x5: positive),
  NoDup [x1; x2; x3; x4; x5] ->
   x4 <> x2.
  Proof.
    intros.
    intro; subst.
    inversion H as [H1 | x l H1 H2]; subst.
    try (solve [apply H1; inList]).
    inversion H2 as [H3 | x l H3 H4]; subst.
    try (solve [apply H3; inList]).
  Qed.



Inductive correct_cenv_of_val: cps.ctor_env -> (cps.val) -> Prop :=
| CCV_constr:forall cenv c vs inf,
    Forall (correct_cenv_of_val cenv) vs ->
    M.get c cenv = Some inf ->
    N.of_nat (length vs) = ctor_arity inf ->
    correct_cenv_of_val cenv (Vconstr c vs)
| CCV_fun: forall cenv rho fds f,
    Forall_fundefs (fun v t xs e => correct_cenv_of_exp cenv e) fds -> 
    correct_cenv_of_val cenv (Vfun rho fds f)
| CCV_int: forall cenv z,
    correct_cenv_of_val cenv (cps.Vint z).
                          
  

(* everything in cenv is in ienv, AND there is a unique entry for it, AND its ord is not reused 
    Doesn't check that name of the i will be consistent (namei could be different from name') *)
  Definition correct_ienv_of_cenv: cps.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall x, forall i a ord name name', M.get x cenv = Some (Build_ctor_ty_info name name' i a ord) ->
                                   exists  namei cl, M.get i ienv = Some (namei, cl) /\ List.In (name, x, a, ord) cl /\ ~ (exists ord' name' a', (name', a', ord') <> (name, a, ord) /\ List.In (name', x, a', ord') cl) /\ ~ (exists name' x' a', (name', x', a') <> (name, x, a) /\ List.In (name', x', a', ord) cl).

  (* all constructors found in ienv are in cenv *) 
  Definition domain_ienv_cenv:  cps.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall i namei cl, M.get i ienv = Some (namei, cl)  ->
                         forall name x a ord, List.In (name, x, a, ord) cl ->
                                              exists namei', M.get x cenv = Some (Build_ctor_ty_info name namei' i a ord).              

                                   

(* stronger version of ienv_of_cenv that enforces uniqueness of name' for i and that nothing is in ienv and not in cenv *)
    Definition correct_ienv_of_cenv_strong: cps.ctor_env -> n_ind_env -> Prop :=
    fun cenv ienv =>
      forall x, forall i a ord name namei, M.get x cenv = Some (Build_ctor_ty_info name namei i a ord) ->
                                   exists   cl, M.get i ienv = Some (namei, cl) /\ List.In (name, x, a, ord) cl /\ ~ (exists ord' name' a', (name', a', ord') <> (name, a, ord) /\ List.In (name', x, a', ord') cl) /\ ~ (exists name' x' a', (name', x', a') <> (name, x, a) /\ List.In (name', x', a', ord) cl).
 
  
  

  (* OS 04/24: added in bound on n includes in this *) 
  Inductive correct_crep (cenv:ctor_env): ctor_tag -> ctor_rep -> Prop :=
  | rep_enum :
      forall c name namei it  n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it 0%N n) ->
        (* there should not be more than 2^(intsize - 1) unboxed constructors *)
        (0 <= (Z.of_N n) <   Ptrofs.half_modulus)%Z ->
      correct_crep cenv c (enum n)
  | rep_boxed:
      forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it (Npos a%N) n) ->
        (* there should not be more than 2^8 - 1 boxed constructors *)
        (0 <= (Z.of_N n) <  Zpower.two_p 8)%Z ->
        (* arity shouldn't be higher than 2^54 - 1  *)
        (0 <= Z.of_N (Npos a) <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z -> 
      correct_crep cenv c (boxed n (Npos a)).

  (* crep <-> make_ctor_rep cenv *)
  Definition correct_crep_of_env: cps.ctor_env -> M.t ctor_rep -> Prop :=
    fun cenv crep_env =>
      (forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it a n) ->
        exists crep, M.get c crep_env = Some crep /\
                     correct_crep cenv c crep) /\
      (forall c crep, M.get c crep_env = Some crep ->
                     correct_crep cenv c crep).


  Definition correct_cenv_of_env: ctor_env -> cps.M.t cps.val -> Prop :=
    fun cenv rho =>
      forall x v,
        M.get x rho = Some v ->
        correct_cenv_of_val cenv v.
   
  Definition correct_envs: ctor_env -> n_ind_env -> M.t ctor_rep ->  cps.M.t cps.val ->  exp -> Prop :=
    fun cenv ienv crep_env rho e =>
      correct_ienv_of_cenv cenv ienv /\
      correct_cenv_of_env cenv rho /\
      correct_cenv_of_exp cenv e /\
      correct_crep_of_env cenv crep_env. 
   
  Theorem correct_envs_subterm:
    forall cenv ienv crep rho e,
           correct_envs cenv ienv crep rho e ->
    forall e', subterm_e e' e ->
               correct_envs cenv ienv crep rho e'.
  Proof.
    intros.
    inv H. inv H2. inv H3. split; auto.
    split; auto. split; auto.
    eapply Forall_constructors_subterm; eauto.
  Qed.    

 
  Theorem correct_envs_set:
    forall cenv ienv crep rho x v e,
    correct_envs cenv ienv crep rho e ->
    correct_cenv_of_val cenv v ->
    correct_envs cenv ienv crep (M.set x v rho) e. 
  Proof.
    intros.
    inv H. inv H2. inv H3.
    split; auto. split; auto.
    intro; intros. destruct (var_dec x0 x).
    - subst.  rewrite M.gss in H3.
      inv H3. auto.
    - rewrite M.gso in H3 by auto.
      eapply H; eauto.
  Qed.
 
  
  (* 
   correct_tinfo alloc_id limit_id args_id alloc_max le m
  > alloc and limit are respectively valid and weak-valid pointers in memory, alloc is at least max before limit_id
  > args points to an array of size max_args in memory before alloc 

limit might be on the edge of current memory so weak_valid, alloc and args are pointing in mem. the int is the max number of blocks allocated by the function 

   *)
   
Definition correct_tinfo: program ->  Z -> temp_env ->  mem  -> Prop :=
  fun p max_alloc lenv m  =>
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs,
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      (align_chunk int_chunk | Ptrofs.unsigned alloc_ofs)%Z /\
      (* everything between alloc_ofs and limit_fs is writable *)
      Mem.range_perm m alloc_b (Ptrofs.unsigned alloc_ofs) (Ptrofs.unsigned limit_ofs) Cur Writable /\
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      (* alloc is at least max blocks from limit *)
      (int_size*max_alloc <= (Ptrofs.unsigned limit_ofs -  Ptrofs.unsigned alloc_ofs) <= gc_size)%Z /\
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      (* args is in a different block from alloc *) 
      args_b <> alloc_b /\
      (* the max_args int blocks after args are Writable *)
      ((Ptrofs.unsigned args_ofs)+ int_size * max_args <= Ptrofs.max_unsigned)%Z  /\
      (forall i, 0 <= i < max_args ->  Mem.valid_access m int_chunk args_b (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr i))))  Writable)%Z /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      tinf_b <> args_b /\
      tinf_b <> alloc_b /\
      (* valid access on four pointers in tinfo *)
      (forall i, 0 <= i < 4 -> Mem.valid_access m int_chunk tinf_b (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size*i)))) Writable)%Z
      /\  deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size*3))) Full (Vptr args_b args_ofs) /\
(* everything pointed to by globals is valid, and not alloc, tinf or args*)
      (forall x b,
          Genv.find_symbol (globalenv p) x = Some b ->
          b <> args_b /\ b <> alloc_b /\ b <> tinf_b /\ (exists chunk, Mem.valid_access m chunk b 0%Z Nonempty)).


Theorem range_perm_to_valid_access:
  forall alloc_b alloc_ofs limit_ofs size m,
    Mem.range_perm m alloc_b alloc_ofs limit_ofs Cur Writable ->
    forall ofs, 
      (align_chunk size | ofs)%Z ->
      (alloc_ofs <= ofs)%Z ->
      (ofs + size_chunk size <= limit_ofs)%Z ->
      Mem.valid_access m size alloc_b ofs Writable.
  Proof.
    intros.
    constructor; auto.
    intro. intro.
    eapply H.
    lia.
  Qed.      
    

Theorem correct_tinfo_mono:
  forall p z lenv m,
    correct_tinfo p z lenv m ->
    forall z', 
      (0 <= z' <= z)%Z ->
    correct_tinfo p z' lenv m. 
Proof.
  intros.
  inv H; destructAll.
  do 7 eexists.
  repeat (split; eauto).
  unfold int_size in *. chunk_red; lia.
Qed.  


Theorem correct_tinfo_proper:
  forall p z lenv m lenv',
  correct_tinfo p z lenv m ->
  map_get_r_l _ [argsIdent; limitIdent; allocIdent;  tinfIdent] lenv lenv' ->
  correct_tinfo p z lenv' m.
Proof.  
  intros.
  inv H; destructAll.
  exists x, x0, x1, x2, x3, x4, x5.
  repeat (split; auto; try (rewrite <- H0; auto; inList)).
Qed.  

Theorem correct_tinfo_not_protected:
  forall p z lenv m,
  correct_tinfo p z lenv m ->
  forall x v, 
    ~ is_protected_tinfo_id_thm x ->
    x <> tinfIdent ->
  correct_tinfo p z (M.set x v lenv) m. 
Proof.
  intros.
  destruct H as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs H]]]]]]].
  exists alloc_b, alloc_ofs, limit_ofs, args_b, args_ofs, tinf_b, tinf_ofs.
  destructAll.
  repeat (split; auto).
  rewrite M.gso; auto. intro. apply H0. left; auto. 
  rewrite M.gso; auto. intro. apply H0. right; auto. 
  rewrite M.gso; auto. intro. apply H0. right; auto.
  rewrite M.gso; auto. 
Qed.

  
Theorem correct_tinfo_param_asgn:
  forall p lenv m xs z vs7 lenv',
  correct_tinfo p z lenv m ->
  lenv_param_asgn lenv lenv' xs vs7 ->
  (forall x, List.In x xs -> ~ (is_protected_tinfo_id_thm x \/ x = tinfIdent)) ->
  correct_tinfo p z lenv' m.
Proof. 
  intros.
  destruct H.
  destructAll.
  exists x, x0, x1, x2, x3, x4, x5.
  repeat (split; auto; try (eapply lenv_param_asgn_not_in with (L :=  fun x => (is_protected_tinfo_id_thm x \/ x = tinfIdent)); eauto; try (left; inList); try (right; reflexivity))).
Qed.
  




Theorem mem_range_valid: forall m m', 
    (forall b ofs ofs'  p, Mem.range_perm m b ofs ofs' Cur p -> Mem.range_perm m' b ofs ofs' Cur p) <->
    (forall b ofs chunk  p, Mem.valid_access m chunk b ofs p -> Mem.valid_access m' chunk b ofs p).
Proof.
  split.
  - intros.
    inv H0.
    apply H in H1.
    constructor;  auto.
  - intros.
    intro.
    intros.
    specialize (H b ofs0  Mint8unsigned p).
    apply H0 in H1.
    assert ( Mem.valid_access m Mint8unsigned b ofs0 p).
    constructor. simpl. intro. intro. assert (ofs0 = ofs1)%Z by lia. subst; auto.
    simpl. apply Z.divide_1_l. apply H in H2. inv H2. simpl in H3.
    eapply H3. lia.
Qed.


Lemma ct_va_range_perm:
  forall m m' b lo hi,
    Mem.range_perm m b lo hi Cur Writable ->
    (forall b' lo' hi' p', Mem.range_perm m b' lo' hi' Cur p' -> Mem.range_perm m' b' lo' hi' Cur p') ->
    Mem.range_perm m' b lo hi Cur Writable.
Proof. auto. Qed.

Lemma ct_va_valid_access:
  forall m m' chunk b ofs p,
    Mem.valid_access m chunk b ofs p ->
    (forall b' lo hi p', Mem.range_perm m b' lo hi Cur p' -> Mem.range_perm m' b' lo hi Cur p') ->
    Mem.valid_access m' chunk b ofs p.
Proof. intros. destruct H. constructor; auto. Qed.

Lemma ct_va_deref_loc_ref:
  forall ty m m' b ofs v,
    deref_loc ty m b ofs Full v ->
    access_mode ty = By_reference ->
    deref_loc ty m' b ofs Full v.
Proof.
  intros. inversion H; subst.
  - rewrite H0 in H1. discriminate.
  - exact (deref_loc_reference ty m' b ofs H1).
  - rewrite H0 in H1. discriminate.
Qed.

Lemma ct_va_globals:
  forall (p0 : program) m m' args_b alloc_b tinf_b,
    (forall x b, Genv.find_symbol (globalenv p0) x = Some b ->
                 b <> args_b /\ b <> alloc_b /\ b <> tinf_b /\
                 (exists chunk, Mem.valid_access m chunk b 0%Z Nonempty)) ->
    (forall b' lo hi p', Mem.range_perm m b' lo hi Cur p' -> Mem.range_perm m' b' lo hi Cur p') ->
    (forall x b, Genv.find_symbol (globalenv p0) x = Some b ->
                 b <> args_b /\ b <> alloc_b /\ b <> tinf_b /\
                 (exists chunk, Mem.valid_access m' chunk b 0%Z Nonempty)).
Proof.
  intros p0 m0 m' args_b alloc_b tinf_b Hglob Hrp x b Hfs.
  destruct (Hglob x b Hfs) as [Ha [Hb [Hc [chunk Hva]]]].
  split; [exact Ha|].
  split; [exact Hb|].
  split; [exact Hc|].
  exists chunk. exact (ct_va_valid_access _ _ _ _ _ _ Hva Hrp).
Qed.

Theorem correct_tinfo_valid_access:
  forall  p z lenv m,
    correct_tinfo p z lenv m ->
    forall m',
    (forall b ofs ofs'  p, Mem.range_perm m b ofs ofs' Cur p -> Mem.range_perm m' b ofs ofs' Cur p) ->
    correct_tinfo p z lenv m'.
Proof.
  intros p0 z0 lenv0 m0 Hct m' Hrp.
  destruct Hct as [ab [ao [lo [arb [aro [tb [to
    [C1 [C2 [C3 [C4 [C5 [C6 [C7 [C8 [C9 [C10 [C11 [C12 [C13 [C14 C15]]]]]]]]]]]]]]]]]]]]].
  exists ab, ao, lo, arb, aro, tb, to.
  split; [exact C1|].
  split; [exact C2|].
  split; [exact (ct_va_range_perm _ _ _ _ _ C3 Hrp)|].
  split; [exact C4|].
  split; [exact C5|].
  split; [exact C6|].
  split; [exact C7|].
  split; [exact C8|].
  split; [intros i Hi; exact (ct_va_valid_access _ _ _ _ _ _ (C9 i Hi) Hrp)|].
  split; [exact C10|].
  split; [exact C11|].
  split; [exact C12|].
  split; [intros i Hi; exact (ct_va_valid_access _ _ _ _ _ _ (C13 i Hi) Hrp)|].
  split; [exact (ct_va_deref_loc_ref _ _ _ _ _ _ C14 eq_refl)|].
  exact (ct_va_globals _ _ _ arb ab tb C15 Hrp).
Qed.

Corollary correct_tinfo_after_store:
  forall p z lenv m,
    correct_tinfo p z lenv m ->
    forall m' chunk b ofs v,
      Mem.store chunk m b ofs v = Some m' ->
    correct_tinfo p z lenv m'. 
Proof. 
  intros. 
  eapply correct_tinfo_valid_access.
  apply H.
  eapply mem_range_valid. intros.
  eapply Mem.store_valid_access_1 in H0; eauto. 
Qed.    
     
Corollary valid_access_after_nstore:
  forall  vs m m' i b' ofs',
    forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
                          mem_after_n_proj_store b' ofs' vs i m m' ->
                         Mem.valid_access m' chunk b ofs p.
Proof.
  induction vs; intros.
  - inv H0.
  - inv H0.
    + eapply Mem.store_valid_access_1; eauto.
    + eapply IHvs.   
      2: apply H9.
      eapply Mem.store_valid_access_1; eauto.
Qed.      
      

Corollary correct_tinfo_after_nstore:
  forall p vs  z lenv m m' b ofs i,
    correct_tinfo p z lenv m ->
      mem_after_n_proj_store b ofs vs i m m' ->
      correct_tinfo p z lenv m'. 
Proof.
  induction vs; intros.
  - inv H0.
  -   inv H0.
      + eapply correct_tinfo_after_store; eauto. 
      + eapply IHvs. 2:{ apply H9. }
        eapply correct_tinfo_after_store; eauto.
Qed.         



        
Theorem var_names_app:
  forall l1 l2,
    (var_names (l1 ++ l2)) = (var_names l1 ++ var_names l2).
Proof.
  induction l1. reflexivity.
  intros.
  destruct a; simpl. rewrite IHl1. reflexivity.
Qed.

 
  



Definition repr_expr_LambdaANF_Codegen_id := repr_expr_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent
     isptrIdent caseIdent nParam.


Definition rel_mem_LambdaANF_Codegen_id := rel_mem_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent
   isptrIdent caseIdent nParam.


Definition repr_val_L_LambdaANF_Codegen_id := repr_val_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam.

Definition repr_val_id_L_LambdaANF_Codegen_id := repr_val_id_L_LambdaANF_Codegen
    argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent
     caseIdent nParam.
 
Definition protected_id_not_bound_id := protected_id_not_bound argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent
   caseIdent.

Definition protected_not_in_L_id := protected_not_in_L argsIdent allocIdent limitIdent tinfIdent.

Theorem Z_non_neg_add:
        forall n m p, 
        (n <= m -> 0 <= p -> n <= p + m)%Z.
Proof.   
  intros.
  etransitivity. eauto. lia.
Qed.
  
(* ident[n] contains either a Vint representing an enum or an integer OR a pointer to a function or the boxed representation of v *)
Inductive nth_arg_rel_LambdaANF_Codegen (fenv:fun_env) (finfo_env:fun_info_env) (p:program) (rep_env: M.t ctor_rep) : eval.env -> positive -> temp_env -> mem -> Z -> Prop :=
| is_in_and_rel:
    forall lenv args_b args_ofs rho m n x LambdaANFv Codegenv L,
       protected_not_in_L argsIdent allocIdent limitIdent tinfIdent p lenv  L -> 
      (* get the value rho(x)*)
      M.get x rho = Some LambdaANFv -> 
      (* get Vargs pointer and load the value from it *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
      Mem.load int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs  (Ptrofs.mul
                   (Ptrofs.repr (sizeof (M.empty composite) val))
                   (Ptrofs.repr n)))) = Some Codegenv ->
      (* relate both val *)
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env LambdaANFv m L Codegenv ->
          nth_arg_rel_LambdaANF_Codegen fenv finfo_env p rep_env rho x lenv m n.
 
 
Theorem caseConsistent_findtag_In_cenv:
  forall cenv t e l,
    caseConsistent cenv l t ->
    findtag l t = Some e ->
    exists (a aty:BasicAst.name) (ty:ind_tag) (n:N) (i:N), M.get t cenv = Some (Build_ctor_ty_info a aty ty n i).
Proof.
  destruct l; intros.
  - inv H0.
  - inv H. destruct info.
    exists ctor_name, ctor_ind_name, ctor_ind_tag,ctor_arity,ctor_ordinal; auto.
Qed.
 

Inductive isPtr_sem: Events.extcall_sem :=
| isPtr_true : forall genv m b ofs,
    isPtr_sem genv ((Vptr b ofs)::nil) m nil (Vtrue) m
| isPtr_false : forall genv m i, 
    isPtr_sem genv ((Vint i)::nil) m nil (Vfalse) m.
  

Definition bind_n_after_ptr (n:Z) (x:block) (x0:Z) (L: block -> Z -> Prop): block -> Z -> Prop :=
  fun b ofs =>
                   match Pos.eqb b x with
                   | true => (match Z.leb x0 ofs with
                              | true => 
                                (match Z.ltb ofs (x0 + n)%Z with
                                 | true => True
                                 | false => L b ofs
                                 end)
                              | false => L b ofs
                              end
                             ) 
                   | false => L b ofs
                   end.
       
Theorem bind_n_after_ptr_def:
  forall n x x0 L b ofs,
  bind_n_after_ptr n x x0 L b ofs
  <->
  (L b ofs \/ (b = x /\ x0 <= ofs < x0 + n))%Z.
Proof.
  intros. unfold bind_n_after_ptr. 
  destruct (b =? x)%positive eqn:bxeq.
  apply Peqb_true_eq in bxeq; subst.
  destruct (x0 <=? ofs)%Z eqn:x0ofsle.
  destruct (ofs <? x0 + n)%Z eqn:ofsx0lt.
  split; auto.
  intro. right; auto. split; auto.
  split.
  apply Z.leb_le in x0ofsle. auto.
  apply Z.ltb_lt in ofsx0lt. auto.
  split; auto. 
  intro. inv H; auto. destruct H0.
  apply OrdersEx.Z_as_DT.ltb_nlt in ofsx0lt.
  exfalso; lia.
  split; auto. intros.
  inv H; auto.
  destruct H0.
  apply Z.leb_nle in x0ofsle. exfalso; lia.
  split; auto. intro.
  inv H; auto.
  destruct H0.
  apply Pos.eqb_neq in bxeq. exfalso; auto.
Qed.


 
Inductive bind_n_after_ptr_rev: nat -> block -> Z ->  (block -> Z -> Prop) -> (block -> Z -> Prop) -> Prop :=
| Bind_0_ind: forall b ofs L,  bind_n_after_ptr_rev 0 b ofs L L
                                                    
| Bind_S_ind : forall n b ofs L L',
    bind_n_after_ptr_rev n b (ofs + int_size) L L' ->    
    bind_n_after_ptr_rev (S n) b ofs L (fun b' z => L' b' z \/ (b = b' /\ ofs <= z < ofs + int_size)%Z).
 




 
Theorem bind_n_after_ptr_exists':
forall n b ofs L,
exists L',
  bind_n_after_ptr_rev n b ofs L L'.
Proof.
  induction n; intros.
  eexists. constructor.
  specialize (IHn b (ofs+int_size)%Z L). inv IHn.
  eexists.  constructor. eauto.
Qed.
 

Theorem bind_n_after_ptr_from_rev:
forall n b ofs L L', 
  bind_n_after_ptr_rev n b ofs L L' -> (forall b' z', (bind_n_after_ptr ((Z.of_nat n) * int_size) b ofs L) b' z' <-> L' b' z'). 
Proof.
  induction n; intros.
  -  inv H. split.  intro. rewrite bind_n_after_ptr_def in H. inv H; auto. destruct H0.  simpl in H0.
    exfalso.  lia.
    rewrite bind_n_after_ptr_def. auto. 
  - inv H.
    specialize (IHn _ _ _ _ H1).
    split; intro.    
    + rewrite bind_n_after_ptr_def in H.
      inv H.
      * left.
        rewrite <- IHn.
        rewrite bind_n_after_ptr_def. auto.
      * (* either z is in the first portion OR it is in the rest of the binds *)
        rewrite <- IHn.
        rewrite bind_n_after_ptr_def.
        destruct H0.
        unfold int_size in *; simpl size_chunk in *.
        rewrite Nat2Z.inj_succ in H0.
        assert (0 <= Z.of_nat n)%Z by apply Nat2Z.is_nonneg.        
        assert (Hcase := Z.lt_ge_cases z' (ofs+int_size)%Z).
        destruct Hcase.
        right.  split; auto.  chunk_red; lia.
        left. right. split; auto. chunk_red; lia.        
    + inv H.
      rewrite <- IHn in H0.
      rewrite bind_n_after_ptr_def.
      rewrite bind_n_after_ptr_def in H0.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. destruct H0. auto. right.
      destruct H. split; auto. chunk_red; lia.
      rewrite bind_n_after_ptr_def.
      right.       unfold int_size in *; simpl size_chunk in *.
      destruct H0. split. auto.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. chunk_red; lia.      
Qed.
  

Theorem bind_n_after_ptr_exists:
forall n b ofs L,
exists L',
  bind_n_after_ptr_rev n b ofs L L' /\ (forall b' z', (bind_n_after_ptr ((Z.of_nat n) * int_size) b ofs L) b' z' <-> L' b' z'). 
Proof.
  intros.
  assert (H_L := bind_n_after_ptr_exists' n b ofs L).
  destruct H_L.
  exists x. split. auto.
  eapply bind_n_after_ptr_from_rev. auto.
Qed.


Theorem load_ptr_or_int:
  forall y,
    Vint_or_Vptr y = true ->
    Val.load_result int_chunk y = y.
Proof.
  intros. simpl. destruct y; inv H; auto.
Qed.


 
 
Theorem mem_after_n_proj_rev_unchanged:
  forall b  vs ofs m m',
    mem_after_n_proj_store_rev b ofs vs m m' ->
    forall L, 
  (forall j, ofs <= j < ofs+int_size*(Z.of_nat (length vs)) ->  ~ L b j)%Z -> 
  Mem.unchanged_on L m m'.
Proof.
  induction vs; intros; inv H.
  -  eapply Mem.store_unchanged_on. eauto.
     simpl in H0.
     simpl size_chunk. auto.
  - eapply IHvs with (L := L) in H5.
    + apply Mem.unchanged_on_trans with (m2 := m'0).
      auto.
      eapply Mem.store_unchanged_on; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      lia.
    + intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      chunk_red;
      lia.
Qed.

(* not true as state, m' are equivalent w.r.t. load, may not be equal. also 
need a lemma that says you can commute store which don't affect each other                           
Theorem mem_after_n_proj_eq_rev:
  forall b vs ofs i m m',
  mem_after_n_proj_store_rev b (ofs + (int_size * i)) vs m m' <->
  mem_after_n_proj_store b ofs vs i m m'.
Proof.
  induction vs.
  - intros.
    split; intro; inv H.
  - intros.
    split; intro; inv H.
    + constructor. auto.
    + rewrite <- Z.add_assoc in H4. rewrite <- Z.mul_succ_r in H4.
      econstructor.
      Search Mem.store. 
    + constructor. auto.
    +    
*)
Definition arg_val_LambdaANF_Codegen (fenv:fun_env) (finfo_env:fun_info_env) (p:program) (rep_env: M.t ctor_rep): cps.val -> mem -> temp_env -> Prop :=
  fun v m lenv =>
    exists args_b args_ofs Codegenv L,
(*       M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr 12)) (Vptr args_b args_ofs) /\ *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\ 
                                  Mem.load int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) = Some Codegenv /\
                                  repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L Codegenv.


Definition same_args_ptr lenv lenv' :=
  @M.get  Values.val argsIdent lenv = M.get argsIdent lenv'.

Definition same_tinf_ptr lenv lenv' :=
  @M.get Values.val tinfIdent lenv =  M.get tinfIdent lenv'.

Definition mem_same_block (b:block) (m m':mem) : Prop :=
  forall chunk ofs,
    Mem.load chunk m b ofs = Mem.load chunk m' b ofs.


Theorem max_allocs_case:
  forall c e y cl, 
  List.In (c, e) cl ->
  max_allocs e <= max_allocs (Ecase y cl).
Proof.
  induction cl; intros.
  inv H.
  simpl. destruct a. inv H.
  - inv H0.
    apply Nat.le_max_l.
  - apply IHcl in H0. simpl in H0.
    etransitivity. apply H0.
    apply Nat.le_max_r.
Qed.

Lemma max_allocs_econstr_ge_body :
  forall x t ys e,
    max_allocs e <= max_allocs (Econstr x t ys e).
Proof.
  intros x t ys e.
  destruct ys as [|y ys'].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma max_allocs_eproj_ge_body :
  forall x t n y e,
    max_allocs e <= max_allocs (Eproj x t n y e).
Proof.
  intros x t n y e.
  simpl.
  lia.
Qed.

Lemma max_allocs_eletapp_zero :
  forall x f t ys e,
    max_allocs (Eletapp x f t ys e) = 0.
Proof.
  intros x f t ys e.
  simpl.
  reflexivity.
Qed.

Lemma max_allocs_eapp_zero :
  forall f t ys,
    max_allocs (Eapp f t ys) = 0.
Proof.
  intros f t ys.
  simpl.
  reflexivity.
Qed.

Lemma max_allocs_ehalt_zero :
  forall x,
    max_allocs (Ehalt x) = 0.
Proof.
  intros x.
  simpl.
  reflexivity.
Qed.

Lemma correct_alloc_econstr_body :
  forall x t ys e z,
    correct_alloc (Econstr x t ys e) z ->
    (0 <= Z.of_nat (max_allocs e) <= z)%Z /\
    correct_alloc e (Z.of_nat (max_allocs e)).
Proof.
  intros x t ys e z Halloc.
  unfold correct_alloc in *.
  subst z.
  split.
  - split.
    + lia.
    + apply Nat2Z.inj_le.
      apply max_allocs_econstr_ge_body.
  - reflexivity.
Qed.

Lemma correct_alloc_eproj_body :
  forall x t n y e z,
    correct_alloc (Eproj x t n y e) z ->
    (0 <= Z.of_nat (max_allocs e) <= z)%Z /\
    correct_alloc e (Z.of_nat (max_allocs e)).
Proof.
  intros x t n y e z Halloc.
  unfold correct_alloc in *.
  subst z.
  split.
  - split.
    + lia.
    + apply Nat2Z.inj_le.
      apply max_allocs_eproj_ge_body.
  - reflexivity.
Qed.

Lemma correct_alloc_eletapp_zero :
  forall x f t ys e z,
    correct_alloc (Eletapp x f t ys e) z ->
    z = 0%Z.
Proof.
  intros x f t ys e z Halloc.
  unfold correct_alloc in Halloc.
  subst z.
  rewrite max_allocs_eletapp_zero.
  reflexivity.
Qed.

Lemma correct_alloc_eapp_zero :
  forall f t ys z,
    correct_alloc (Eapp f t ys) z ->
    z = 0%Z.
Proof.
  intros f t ys z Halloc.
  unfold correct_alloc in Halloc.
  subst z.
  rewrite max_allocs_eapp_zero.
  reflexivity.
Qed.

Lemma correct_alloc_ehalt_zero :
  forall x z,
    correct_alloc (Ehalt x) z ->
    z = 0%Z.
Proof.
  intros x z Halloc.
  unfold correct_alloc in Halloc.
  subst z.
  rewrite max_allocs_ehalt_zero.
  reflexivity.
Qed.

Lemma correct_alloc_ecase_branch :
  forall y cl c e z,
    List.In (c, e) cl ->
    correct_alloc (Ecase y cl) z ->
    (0 <= Z.of_nat (max_allocs e) <= z)%Z /\
    correct_alloc e (Z.of_nat (max_allocs e)).
Proof.
  intros y cl c e z Hin Halloc.
  unfold correct_alloc in *.
  subst z.
  split.
  - split.
    + lia.
    + apply Nat2Z.inj_le.
      eapply max_allocs_case; eauto.
  - reflexivity.
Qed.

Lemma correct_tinfo_econstr_body :
  forall p lenv m x t ys e max_alloc,
    correct_tinfo p max_alloc lenv m ->
    correct_alloc (Econstr x t ys e) max_alloc ->
    correct_tinfo p (Z.of_nat (max_allocs e)) lenv m.
Proof.
  intros p lenv m x t ys e max_alloc Hct Halloc.
  destruct (correct_alloc_econstr_body x t ys e max_alloc Halloc)
    as [Hbound _].
  eapply correct_tinfo_mono; eauto.
Qed.

Lemma correct_tinfo_eproj_body :
  forall p lenv m x t n y e max_alloc,
    correct_tinfo p max_alloc lenv m ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    correct_tinfo p (Z.of_nat (max_allocs e)) lenv m.
Proof.
  intros p lenv m x t n y e max_alloc Hct Halloc.
  destruct (correct_alloc_eproj_body x t n y e max_alloc Halloc)
    as [Hbound _].
  eapply correct_tinfo_mono; eauto.
Qed.

Lemma correct_tinfo_ecase_branch :
  forall p lenv m y cl c e max_alloc,
    correct_tinfo p max_alloc lenv m ->
    List.In (c, e) cl ->
    correct_alloc (Ecase y cl) max_alloc ->
    correct_tinfo p (Z.of_nat (max_allocs e)) lenv m.
Proof.
  intros p lenv m y cl c e max_alloc Hct Hin Halloc.
  destruct (correct_alloc_ecase_branch y cl c e max_alloc Hin Halloc)
    as [Hbound _].
  eapply correct_tinfo_mono; eauto.
Qed.
  
  
Theorem get_list_cons :
  forall A rho v ys vs,
    @get_list A ys rho = Some (v :: vs) ->
  exists y ys', ys = y::ys' /\
                cps.M.get y rho = Some v /\ 
                get_list ys' rho = Some vs. 
Proof.
  intros. destruct ys as [ | y ys'].
  inv H. exists y, ys'.
  split; auto.  simpl in H.
  destruct  (cps.M.get y rho).
  destruct (get_list ys' rho). inv H. auto.
  inv H. inv H.
Qed.
 
      
Theorem exists_getvar_or_funvar_list:
  forall lenv p rho L rep_env finfo_env argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv
         m xs vs,
            ( forall x, List.In x xs ->
                        exists v6 : cps.val,
         M.get x rho = Some v6 /\
         repr_val_id_L_LambdaANF_Codegen argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env
                             p rep_env v6 m L lenv x)
            ->
            get_list xs rho = Some vs  ->
            exists vs7 : list Values.val, get_var_or_funvar_list p lenv xs = Some vs7.
Proof.
  induction xs; intros.
  - exists nil. auto.
  - simpl in H0.
    destruct (cps.M.get a rho) eqn:Hgar.
    destruct (get_list xs rho) eqn:Hgxsr.
    inv H0.
    specialize (IHxs l).
    assert ((forall x : positive,
          List.In x xs ->
          exists v6 : cps.val,
            M.get x rho = Some v6 /\
            repr_val_id_L_LambdaANF_Codegen argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0 nParam0
                                fenv finfo_env p rep_env v6 m L lenv x)).
    {
      intros. apply H. constructor 2; auto.
    }
    apply IHxs in H0. destruct H0.
    assert
      (exists v6 : cps.val,
        M.get a rho = Some v6 /\
        repr_val_id_L_LambdaANF_Codegen argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0 nParam0 fenv
                            finfo_env p rep_env v6 m L lenv a).
    apply H. constructor. reflexivity.
    destruct H1. destruct H1.
    rewrite H1 in Hgar. inv Hgar.
    inv H2. eexists. simpl. rewrite H0. rewrite H3. reflexivity.
    destruct Archi.ptr64 eqn:Harchi; eexists; simpl; rewrite H0; rewrite H3; rewrite H4; inv H5; archi_red; reflexivity.
    reflexivity.
    inv H0.
    inv H0.
Qed.

 
  
Theorem store_unchanged_on' :
        forall m m'' m' L v b chunk ofs,
          Mem.unchanged_on L m m'' ->
          (forall i, ofs <= i < ofs + size_chunk chunk -> ~ L b i)%Z ->
          Mem.store chunk m' b ofs v = Some m'' ->
          Mem.unchanged_on L m m'.
Proof.
  intros. inv H. constructor.
  - apply Mem.nextblock_store in H1.
    rewrite <- H1. auto.
  - split; intros.
    eapply Mem.perm_store_2.
    apply H1. apply unchanged_on_perm; auto.
    apply unchanged_on_perm; auto.
    eapply Mem.perm_store_1; eauto.
  - intros.
    rewrite <- unchanged_on_contents; auto.        
    symmetry.
    erewrite Mem.store_mem_contents; eauto.
    rewrite Maps.PMap.gsspec.
    destruct (Coqlib.peq b0 b); auto. subst b0. apply Mem.setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (Coqlib.zlt ofs0 ofs); auto.
  destruct (Coqlib.zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). chunk_red; lia. auto.
Qed.  
 

    
   


    

Definition shr_ty := if Archi.ptr64 then ulongTy else uintTy.

Lemma classify_shift_shr_ty_64:
  Archi.ptr64 = true ->
  classify_shift shr_ty shr_ty = shift_case_ll Unsigned.
Proof.
  intros H. unfold shr_ty. rewrite H. reflexivity.
Qed.

Lemma classify_shift_shr_ty_32:
  Archi.ptr64 = false ->
  classify_shift shr_ty shr_ty = shift_case_ii Unsigned.
Proof.
  intros H. unfold shr_ty. rewrite H. reflexivity.
Qed.

Lemma ltu_one_iwordsize_64:
  Int64.ltu (Int64.repr 1) Int64.iwordsize = true.
Proof. reflexivity. Qed.

Lemma ltu_one_iwordsize_32:
  Int.ltu (Int.repr 1) Int.iwordsize = true.
Proof. reflexivity. Qed.

Lemma shru_one_shiftr_64:
  forall z, (0 <= z <= Int64.max_unsigned)%Z ->
    Int64.shru (Int64.repr z) (Int64.repr 1) = Int64.repr (Z.shiftr z 1).
Proof.
  intros.
  rewrite Int64.shru_div_two_p.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Int64.unsigned_repr by lia.
  unfold Int64.iwordsize, Int64.zwordsize. simpl.
  rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  reflexivity.
Qed.

Lemma shru_one_shiftr_32:
  forall z, (0 <= z <= Int.max_unsigned)%Z ->
    Int.shru (Int.repr z) (Int.repr 1) = Int.repr (Z.shiftr z 1).
Proof.
  intros.
  rewrite Int.shru_div_two_p.
  rewrite Zshiftr_div_two_p by lia.
  rewrite Int.unsigned_repr by lia.
  unfold Int.iwordsize, Int.zwordsize. simpl.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  reflexivity.
Qed.

Theorem sem_shr_unboxed:
  forall n,
    sem_shr (make_vint (Ptrofs.unsigned n)) shr_ty (make_vint 1) shr_ty = Some (make_vint (Z.shiftr (Ptrofs.unsigned n) 1)).
Proof.
  intros.
  assert (Hrange := uint_range_unsigned n).
  unfold sem_shr, sem_shift, make_vint, shr_ty.
  destruct Archi.ptr64 eqn:Harchi; simpl.
  - rewrite ltu_one_iwordsize_64. simpl.
    f_equal. f_equal. apply shru_one_shiftr_64.
    unfold uint_range in Hrange. rewrite ptrofs_mu in Hrange. rewrite Harchi in Hrange. lia.
  - rewrite ltu_one_iwordsize_32. simpl.
    f_equal. f_equal. apply shru_one_shiftr_32.
    unfold uint_range in Hrange. rewrite ptrofs_mu in Hrange. rewrite Harchi in Hrange. lia.
Qed.


Theorem sem_switch_and_255: forall h,
     (0 <= h <= Ptrofs.max_unsigned)%Z -> 
  sem_switch_arg (int_and h 255) shr_ty = Some (Z.land h 255).
Proof.
  intros.
  rewrite ptrofs_mu in H.
  unfold sem_switch_arg. unfold int_and. 
  destruct Archi.ptr64 eqn:Harchi;
    archi_red; unfold classify_shift.
  { unfold Int64.and.
    rewrite Int64.unsigned_repr with (z := h) by (archi_red; solve_uint_range; lia).
    rewrite Int64.unsigned_repr with (z := 255%Z) by (archi_red; solve_uint_range; lia).
    rewrite Int64.unsigned_repr. simpl. reflexivity.
    replace 255%Z with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones. unfold Int64.max_unsigned in *; simpl in *.
    assert ( (0 <= h mod Z.pow_pos 2 8 < Z.pow_pos 2 8)%Z).
    apply Z.mod_bound_pos.  lia. compute. reflexivity.
    destruct H0. split; auto.
    eapply OrdersEx.Z_as_OT.lt_le_incl.
    eapply OrdersEx.Z_as_DT.lt_le_trans.
    eauto. compute. intro. inv H2.
    lia.
  }
  { unfold shr_ty; rewrite Harchi. simpl. unfold Int.and.
    rewrite Int.unsigned_repr with (z := h) by (archi_red; solve_uint_range; lia).
    rewrite Int.unsigned_repr with (z := 255%Z) by (archi_red; solve_uint_range; lia).
    rewrite Int.unsigned_repr. reflexivity.
    replace 255%Z with (Z.ones 8) by reflexivity.
    rewrite Z.land_ones. unfold Int.max_unsigned in *; simpl in *.
    assert ( (0 <= h mod Z.pow_pos 2 8 < Z.pow_pos 2 8)%Z).
    apply Z.mod_bound_pos.  lia. compute. reflexivity.
    destruct H0. split; auto.
    eapply OrdersEx.Z_as_OT.lt_le_incl. 
    eapply OrdersEx.Z_as_DT.lt_le_trans.
    eauto. compute. intro. inv H2.
    lia.
  }
Qed.
    
Theorem sem_switch_arg_1: forall n,
     (0 <= n <= Ptrofs.max_unsigned)%Z -> 
        sem_switch_arg (int_shru n 1) shr_ty = Some (Z.shiftr n 1).
Proof.  
  intros. rewrite ptrofs_mu in H.
  unfold sem_switch_arg. unfold int_shru.
   
  destruct Archi.ptr64 eqn:Harchi;
    archi_red; unfold classify_shift; simpl.
  {   (* unfold Int64.ltu. rewrite Coqlib.zlt_true. *)
    rewrite Int64.shru_div_two_p.
    rewrite Z.shiftr_div_pow2 by lia.
      rewrite Int64.unsigned_repr with (z := n) by (archi_red; solve_uint_range; lia).
      rewrite Int64.unsigned_repr with (z := 1%Z) by (archi_red; solve_uint_range; lia).
      rewrite Int64.unsigned_repr. reflexivity.
      unfold Int64.max_unsigned; solve_uint_range.
    unfold  Zpower.two_power_pos.  simpl.
    inv H. split.
    apply Z.div_pos; lia.
    apply OrdersEx.Z_as_OT.div_le_upper_bound. lia. lia.
}
  { unfold shr_ty; rewrite Harchi; simpl.
        rewrite Int.shru_div_two_p.
    rewrite Zshiftr_div_two_p by lia.
      rewrite Int.unsigned_repr with (z := n) by (archi_red; solve_uint_range; lia).
      rewrite Int.unsigned_repr with (z := 1%Z) by (archi_red; solve_uint_range; lia).
      rewrite Int.unsigned_repr. reflexivity.
      unfold Int.max_unsigned; solve_uint_range.
    unfold  Zpower.two_power_pos.  simpl.
    inv H. split.
    apply Z.div_pos; lia.
    apply OrdersEx.Z_as_OT.div_le_upper_bound. lia. lia.
  }
Qed.


(* Two constructors of the same inductive cannot have the same ordinal *)
Theorem disjoint_ord:
  forall {cenv ienv c c' namec namec' namei namei' i a a' ord ord'}, 
    correct_ienv_of_cenv cenv ienv ->        
    M.get c cenv = Some (Build_ctor_ty_info namec namei i a ord) -> 
    M.get c' cenv = Some (Build_ctor_ty_info namec' namei' i a' ord') ->
    (c <> c' <-> ord <> ord').
Proof.
  intros.
  apply H in H0. apply H in H1. destructAll.
  rewrite H1 in H0. inv H0.
  split; intro; intro; subst.
  - (* c -> ord *)
    apply H7. exists namec', c', a'.  split. intro. inv H8. apply H0; auto. auto.
  - (* ord -> c *)
    apply H6. exists ord', namec', a'. split. intro. inv H8. apply H0; auto. auto.
Qed.



Theorem pos_iter_injective:
  forall A f,
         (forall a b, f a = f b -> a = b) ->
         forall p (a b:A),
  Pos.iter f a p = Pos.iter f b p ->
  a = b.
Proof.
  induction p; intros.
  simpl in H0.
  apply H in H0.
  apply IHp in H0. apply IHp in H0. auto.
  simpl in H0. apply IHp in H0. apply IHp; auto.
  simpl in H0. apply H; auto.
Qed.  
  
  
Theorem shiftl_injective:
  forall c a b,
    (0 <= c)%Z ->
  Z.shiftl a c = Z.shiftl b c ->
  a = b.
Proof.
  induction c; intros.
  simpl in *. auto.
  simpl in H0.
  apply pos_iter_injective in H0. auto.
  intros. lia.
  simpl in H0. exfalso.
  assert (Z.neg p < 0)%Z by apply Pos2Z.neg_is_neg.
  lia.
Qed.
 
Theorem unzip_vars:
  forall vs0 vars x, 
    Forall2 (fun (x0 : var) (xt : var * type) => xt = (x0, uval)) vs0 vars ->
    List.In x (var_names vars) <->
    List.In x vs0.
Proof.
  induction vs0; intros.
  inv H. split; intro H; inv H.
  inv H. simpl.
  apply IHvs0 with (x := x) in H4.
  rewrite <- H4. reflexivity.
Qed.

 

Theorem case_of_labeled_stm_unboxed:
  forall rep_env arr t  n0 e p fenv finfo_env ienv cenv ,
    correct_ienv_of_cenv cenv ienv ->
    M.get t rep_env = Some (enum arr) ->
    correct_crep_of_env cenv  rep_env ->
    repr_unboxed_Codegen arr n0 ->
    forall cl ls ls',
      caseConsistent cenv cl t ->
  findtag cl t = Some e ->
  repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
  exists s s', 
    seq_of_labeled_statement (select_switch (Z.shiftr n0 1) ls') = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof.
  intros rep_env arr t  n0 e p fenv finfo_env ienv cenv Hienv H H0 H1.
  induction cl;
  intros ls ls' Hcc; intros.
  (* impossible empty cl *)  inv H2.
  simpl in H2. destruct a. destruct (M.elt_eq c t).
  - (* is-case *)
    inv H2. inv H3.
    (* remove impossible boxed cases *)
    3:{   rewrite H10 in H. inv H. }
    3:{  rewrite H10 in H. inv H. }
    + (* default *)
      simpl. exists s, Sskip.
      split. reflexivity.
      auto.
    + rewrite H10 in H. inv H.
      exists s, (seq_of_labeled_statement ( (LScons lsa' lsb' lsc'))). split; auto.
      simpl. unfold select_switch. simpl.
      
      assert (tag = n0).
      inv H11; inv H1. auto.
      subst.
      rewrite Coqlib.zeq_true.
      simpl. reflexivity.
  - (*is not case -- IH *)
    inv H3.
    + (* impossible because rep_env is correct, t is in cl but cl -unboxed-> LSnil *)
      exfalso.
      eapply repr_branches_LSnil_no_unboxed; eauto.
     + simpl. (* c <> t so arr <> n1 and the headers are different *)
       unfold select_switch.
       simpl select_switch_case. 
       rewrite Coqlib.zeq_false.
       inv Hcc. 
       specialize (IHcl _ _ H14 H2 H7). apply IHcl.
       inv H0. apply H4 in H11.
       apply H4 in H. inv H. inv H11. 
       assert (it = it0). {
         inv Hcc.  rewrite H5 in H13; rewrite H0 in H14; inv H13; inv H14. auto.
       }
       subst.
       assert (n1 <> arr). {
         assert (Hdj := disjoint_ord Hienv H0 H5).
         apply Hdj. auto.
       }      
       inv Hcc. rewrite H5 in H14; inv H14. rewrite H0 in H15; inv H15.
       intro. do 2 (erewrite repr_unboxed_shiftr in H6 by eauto). 
       apply H. apply N2Z.inj. apply H6.
     + inv Hcc; eapply IHcl; eauto.       
     + inv Hcc; eapply IHcl; eauto.
Qed.
   
(* 
Definition z_and z1 z2 :=
  if Archi.ptr64 then (Int64.unsigned (Int64.and (Int.repr z1) (Int64.repr z2))) else
    (Int.unsigned (Int.and (Int.repr z1) (Int.repr z2))). *)
  
Theorem case_of_labeled_stm_boxed:
  forall rep_env n arr t  h e p fenv finfo_env ienv cenv ,
    correct_ienv_of_cenv cenv ienv ->
     M.get t rep_env = Some (boxed n arr)  ->
    correct_crep_of_env cenv rep_env ->
    boxed_header n arr  h ->
    forall cl ls ls',
      caseConsistent cenv cl t ->
  findtag cl t = Some e ->
  repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
  exists s s', 
                       (seq_of_labeled_statement (select_switch (Z.land  h 255) ls)) = (Ssequence (Ssequence s Sbreak) s') /\  repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof. 
  intros rep_env n arr t  h e p fenv finfo_env ienv cenv  Hienv H H0 H1.
  induction cl; intros ls ls' Hcc; intros.
  (* impossible empty cl *) inv H2.
  simpl in H2. destruct a. destruct (M.elt_eq c t).
  - (* is case *)
    inv H2. inv H3. rewrite H9 in H; inv H.
    rewrite H10 in H; inv H.
    + (* default *)
      simpl. exists s, Sskip.
      split; auto.
    + rewrite H10 in H. inv H.
      assert (tag = h). {
        inv H1; inv H11. auto.
      }
      rewrite <- H in *. clear H. clear H11.
      unfold select_switch. simpl. 
      rewrite Coqlib.zeq_true. simpl. 
      do 2 eexists.
      split. reflexivity. auto.
  - (* is-not-case -- IH *)    
    inv H3.
    + (* enum default *)
      inv Hcc; eapply IHcl; eauto.       
    + inv Hcc; eapply IHcl; eauto.            
    + exfalso.
      eapply repr_branches_LSnil_no_boxed; eauto.
    + (* c <> t so arr <> n1 and the header are different *)
      unfold select_switch.
      simpl select_switch_case. 
      rewrite Coqlib.zeq_false.
      inv Hcc. 
      specialize (IHcl _ _ H14 H2 H7). apply IHcl.
      do 2 (erewrite  repr_boxed_t; eauto).


      inv H0. apply H4 in H11.
      apply H4 in H. inv H. inv H11.          
      inv Hcc.
 
      rewrite H6 in H11. inv H11. rewrite H5 in H16. inv H16.
      simpl in H18. inv H18.
      
      assert (Hdj := disjoint_ord Hienv H5 H6).
      apply Hdj in n0. intro. apply n0.
      apply N2Z.inj. auto.
Qed.

(* CHANGE HERE *)

Lemma skipn_suc1  {A} n (x : A) (l1 l2 : list A) : skipn n l1 = x :: l2 -> skipn (S n) l1 = l2.
Proof.
  generalize n l2. induction l1; destruct n0; intros.
  - simpl in H. inv H.
  - inv H.
  - inv H. reflexivity.
  - apply (IHl1 n0 l0 H).
Qed.
 
Lemma skipn_suc2 {A} n (x y : A) (l1 l2 : list A) : skipn n (x :: l1) = y :: l2 -> skipn n l1 = l2.
Proof.
  generalize x y n l2. induction l1; destruct n0; intros; inv H; try reflexivity.
  - destruct n0; inv H1.
  - apply (IHl1 _ _ _ _ H1).
Qed.  

Lemma skipn_cons {A} n (x y : A) (l1 l2 : list A) : skipn n (x :: l1) = (y :: l2) -> skipn n l1 = l2.
Proof.
  induction l2 , l1; intros.
  - destruct n; reflexivity. 
  - destruct n; inv H.
    destruct n; intros.
    + inv H1. reflexivity.
    + inv H1. apply (skipn_suc1 n y l1 []). assumption.
  - apply (skipn_suc1 n y [x] (a :: l2)). assumption.
  - apply (skipn_suc2 _ x y). assumption.
Qed.   

Lemma skipn_cons_nil {A} n (x : A) (l : list A) : skipn n (x :: l) = [] -> skipn n l = [].
Proof.
  generalize n x. induction l; intros.
  - destruct n0; reflexivity. 
  - destruct n0.
    + inv H.
    + simpl in H. simpl.  apply (IHl n0 a). assumption.
Qed.

(* place values lenv(ys) into the inf slots of the args array
   something about allocPtr *)
Definition mem_of_asgn argsIdent p lenv (ys:list positive) (inf:list N) m :=
  exists args_b args_ofs, M.get argsIdent lenv = Some (Vptr args_b args_ofs)  /\ Forall2 (fun y i => exists v, Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v /\ get_var_or_funvar p lenv y v) ys inf.

(* same as above but with val list explicit *)
Inductive mem_of_asgn_v args_b args_ofs p lenv m: list positive -> list N -> list Values.val -> Prop :=
| moa_cons: forall y i v ys inf vs, 
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v ->
    get_var_or_funvar p lenv y v ->
     mem_of_asgn_v args_b args_ofs p lenv m (y::ys) (i::inf) (v::vs)
| moa_nil:
    mem_of_asgn_v args_b args_ofs p lenv m [] [] [].
 
(* same as above, but without lenv and ys 
   i.e. disregarding provenance *)
Inductive mem_after_asgn args_b args_ofs  m: list N -> list Values.val -> Prop :=
  | maa_cons: forall  i v  inf vs, 
    mem_after_asgn args_b args_ofs  m inf vs ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v ->
     mem_after_asgn args_b args_ofs  m (i::inf) (v::vs)
| maa_nil:
    mem_after_asgn args_b args_ofs  m [] [].



Theorem mem_of_asgn_nthN:
  forall {args_b args_ofs p lenv m ys inf vs y v n},
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs  ->
  nthN ys n = Some y ->
  nthN vs n = Some v ->
  get_var_or_funvar p lenv y v.
Proof.
  induction ys; intros.
  inv H0.
  destruct vs. inv H1.
  inv H.
  destruct n. inv H0; inv H1; auto.  
  apply nthN_pos_pred in H0.
  apply nthN_pos_pred in H1.
  eapply IHys; eauto.
Qed.

Theorem mem_of_asgn_after:
  forall args_b args_ofs p m lenv inf ys vs,
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  mem_after_asgn args_b args_ofs m inf vs.
Proof.
  induction inf; intros.
  - inv H; constructor.
  - inv H; constructor; eauto.
Qed.

Theorem mem_after_asgn_length:
  forall args_b args_ofs m  inf vs,
  mem_after_asgn args_b args_ofs m inf vs ->
  length inf = length vs. 
Proof.
  induction inf; intros.
  inv H; auto.
  inv H. simpl. erewrite IHinf; eauto.
Qed.

Theorem mem_of_asgn_exists_v:
  forall {argsIdent p lenv m args_b args_ofs ys inf},
  mem_of_asgn argsIdent p lenv ys inf m ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
  exists vs,
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs.
Proof.
  intros. inv H. destruct H1. destruct H.
  rewrite H in H0. inv H0. 
  clear H. revert dependent inf. induction ys; intros.
  -  inv H1.
     exists []. constructor.
  - inv H1. specialize (IHys _ H4).
    inv IHys. inv H2.
    exists (x0::x). destruct H0. constructor; eauto.
Qed.


Theorem mem_of_asgn_forall_v:
  forall {argsIdent p lenv m args_b args_ofs ys inf vs},
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
  mem_of_asgn argsIdent p lenv ys inf m.
Proof.
  induction ys; intros.
  - inv H. eexists. eexists. split; eauto.
  - inv H. specialize (IHys _ _ H3 H0).
    exists args_b, args_ofs. split; auto. constructor.
    exists v; eauto.
    inv IHys. destructAll. rewrite H in H0. inv H0.
    auto.
Qed.
 
    
Theorem mem_of_asgn_v_length:
  forall {p lenv m args_b args_ofs ys inf vs},
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    length inf = length vs.
Proof.
  induction ys; intros; inv H.
  reflexivity.
  simpl. erewrite IHys. reflexivity.
  eauto.
Qed.

Theorem mem_of_asgn_v_length13:
  forall {p lenv m args_b args_ofs ys inf vs},
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    length ys = length vs.
Proof.
  induction ys; intros; inv H.
  reflexivity.
  simpl. erewrite IHys. reflexivity.
  eauto.
Qed.




Theorem mem_of_asgn_v_disjoint:
  forall a v lenv args_b args_ofs p ys vs inf m,
    ~ List.In a ys ->
    mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
    mem_of_asgn_v args_b args_ofs p (Maps.PTree.set a v lenv) m ys inf vs.
Proof.
  induction ys; intros.
  - inv H0. constructor.
  - inv H0. constructor. apply IHys. intro; apply H. constructor 2; auto.
    auto. auto. inv H7.
    + constructor. auto.
    + constructor 2; auto.
      rewrite M.gso. auto. intro; apply H. subst.
      constructor. auto.
Qed.

Theorem mem_of_asgn_v_store:
  forall args_b args_ofs p v chunk b ofs lenv m m' ys inf vs,
  mem_of_asgn_v args_b args_ofs p lenv m ys inf vs ->
  Mem.store chunk m b ofs v  = Some m' ->
  b <> args_b ->
  mem_of_asgn_v args_b args_ofs p lenv m' ys inf vs.
Proof.  
  induction ys; intros.
  - inv H.
    constructor.
  - inv H.
    constructor; auto.
    unfold Mem.loadv in *.
    erewrite Mem.load_store_other; eauto.
Qed.    

Ltac solve_ptrofs_range:=
  solve_uint_range; uint_range_ptrofs; chunk_red; archi_red; unfold Int64.max_unsigned; unfold Int.max_unsigned; simpl; try lia.  

(* w/o destructing ptr64 *)
Ltac solve_ptrofs_range':=
  solve_uint_range; uint_range_ptrofs; archi_red; unfold Int64.max_unsigned; unfold Int.max_unsigned; simpl; try lia.  


Definition mem_of_asgn_cons:
  forall p y lenv ys inf m i max_alloc m' v args_ofs args_b,
  mem_of_asgn argsIdent p lenv ys inf m ->
  NoDup (i::inf) ->
  Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z (i::inf) ->
  (0 <= Ptrofs.unsigned args_ofs + int_size * max_args  <= Ptrofs.max_unsigned )%Z ->
  correct_tinfo p max_alloc lenv m ->
  M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->

  get_var_or_funvar p lenv y v ->
  
  
  Mem.storev int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) v = Some m' ->
  mem_of_asgn argsIdent p lenv (y::ys) (i::inf) m'.
Proof.
   intros. 
  destruct H3 as [alloc_b [alloc_ofs [limit_ofs [args_b' [args_ofs' [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
  rewrite Hget_args in H4. inv H4.
  destruct H as [args_b' [args_ofs' [H3]]]. rewrite H3 in Hget_args.  inv Hget_args. 
  exists args_b, args_ofs.
  split; auto.
  constructor.
  - exists v. split; auto.
    simpl in *. erewrite Mem.load_store_same; eauto.
    simpl.  destruct v; inv H5; inv H8; auto. 
  - eapply Forall2_monotonic_strong; eauto.
    intros. cbv beta in *.
    destruct H8. exists x.
    destruct H8. split; auto.
    unfold Mem.loadv in *. 
    erewrite Mem.load_store_other; eauto.
    right.  inv H0.
    assert (i <> x2).
    intro. apply H12. subst; auto.
    inv H1.
    eapply Forall_forall in H15; eauto.
    assert ( uint_range_l [int_size; Z.of_N i] ) by  (unfold max_args in *; solve_ptrofs_range).
    assert ( uint_range_l [int_size; Z.of_N x2] ) by (unfold int_size in *; unfold max_args in *; solve_ptrofs_range).
    assert (Hix2 := N.le_gt_cases x2 i).
    inv Hix2. 
    + left.
      assert (x2 < i)%N.
      apply N.le_neq. split; auto.
      clear H11.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.add_unsigned.
      repeat (rewrite Ptrofs.unsigned_repr_eq).
      rewrite Zdiv.Zplus_mod_idemp_r.
      rewrite Zdiv.Zplus_mod_idemp_r.

      destruct H2.  apply Z.lt_le_pred in H11.   
      rewrite Z.mod_small.
      rewrite Z.mod_small.
      assert (Z.of_N x2 + 1 <=  Z.of_N i)%Z.
      lia.
      rewrite <- Z.add_assoc. 
      replace (Z.add (Z.mul int_size (Z.of_N x2)) (size_chunk int_chunk)) with (int_size * (Z.of_N x2 + 1))%Z by (chunk_red; lia).


      chunk_red; uomega. 
      split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
      eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
      split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
      eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
    + right.
      rewrite Ptrofs.add_unsigned.
       rewrite Ptrofs.add_unsigned.
       repeat (rewrite Ptrofs.unsigned_repr_eq).
       rewrite Zdiv.Zplus_mod_idemp_r.
       rewrite Zdiv.Zplus_mod_idemp_r.

       destruct H2.
       unfold Ptrofs.max_unsigned in *. apply Z.lt_le_pred in H16.   
       rewrite Z.mod_small.
       rewrite Z.mod_small.
       assert (Z.of_N i + 1 <=  Z.of_N x2)%Z.
       lia.
       replace (int_size*Z.of_N i + int_size)%Z with (int_size * (Z.of_N i + 1))%Z  by (chunk_red; uomega).
       chunk_red; uomega.
       split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
       eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
       split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range. chunk_red; uomega.
       eapply OrdersEx.Z_as_OT.le_lt_trans; eauto. chunk_red; uomega.
Qed.

Lemma In_skipn : forall {A} n (x : A) l,
  List.In x (skipn n l) -> List.In x l.
Proof.
  induction n; intros.
  - simpl in H. auto.
  - destruct l. inversion H. simpl in H. right. eauto.
Qed.

(* Helper: step through right_param_asgn directly on the three lists *)
Lemma repr_asgn_fun_entry_aux:
  forall sxs slocs svs args_b args_ofs argsIdent F p m k asgn lenv lenv',
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    mem_after_asgn args_b args_ofs m slocs svs ->
    right_param_asgn argsIdent sxs slocs asgn ->
    lenv_param_asgn_i lenv lenv' sxs svs ->
    (forall x, List.In x sxs -> x <> argsIdent) ->
    Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) slocs ->
    clos_refl_trans state (traceless_step2 (globalenv p))
               (State F asgn k empty_env lenv m)
               (State F Sskip k empty_env lenv' m).
Proof.
  induction sxs as [| x sxs' IH]; intros.
  - inversion H1; subst. inversion H2; subst. apply rt_refl.
  - inversion H1; subst. inversion H2; subst. inversion H0; subst.
    assert (Harchi : Archi.ptr64 = true) by (vm_compute; reflexivity).
    assert (Hn_range: (0 <= Z.of_N n < max_args)%Z) by (inversion H4; assumption).
    (* step_seq *)
    eapply rt_trans. constructor. constructor.
    (* step_set *)
    eapply rt_trans. constructor.
    { constructor.
      eapply eval_Elvalue.
      + eapply eval_Ederef.
        eapply eval_Ebinop.
        * apply eval_Etempvar. exact H.
        * unfold c_int, LambdaANF_to_Clight.c_int. rewrite Harchi.
          apply eval_Econst_long.
        * { unfold add, LambdaANF_to_Clight.add, sem_binary_operation, sem_add.
          simpl typeof.
          unfold val, LambdaANF_to_Clight.val, uval, LambdaANF_to_Clight.uval,
                 c_int, LambdaANF_to_Clight.c_int.
          rewrite Harchi. unfold classify_add. simpl typeconv. cbv beta iota.
          f_equal. f_equal. f_equal. f_equal.
          unfold Ptrofs.mul, Ptrofs.of_int64, sizeof. simpl.
          unfold max_args in Hn_range.
          repeat (try rewrite Int64.unsigned_repr
            by (unfold Int64.max_unsigned; simpl; lia);
          try rewrite Ptrofs.unsigned_repr
            by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto;
                simpl; lia)).
          reflexivity. }
      + assert (Hofs_eq : Ptrofs.mul (Ptrofs.repr (if Archi.ptr64 then 8%Z else 4%Z))
                  (Ptrofs.of_int64 (Int64.repr (Z.of_N n)))
                = Ptrofs.repr (int_size * Z.of_N n)).
        { unfold Ptrofs.mul, Ptrofs.of_int64, int_size, int_chunk, LambdaANF_to_Clight.int_chunk.
          rewrite Harchi. simpl. unfold max_args in Hn_range.
          rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
          rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto; simpl; lia).
          rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto; simpl; lia).
          reflexivity. }
        rewrite Hofs_eq.
        apply deref_loc_value with (chunk := int_chunk).
        * unfold val, LambdaANF_to_Clight.val, int_chunk, LambdaANF_to_Clight.int_chunk;
          simpl; reflexivity.
        * eassumption. }
    (* step_skip_seq *)
    eapply rt_trans. constructor. constructor.
    (* IH *)
    eapply IH; try eassumption.
    + rewrite M.gso; [exact H |].
      apply not_eq_sym. apply H3. left; reflexivity.
    + intros. apply H3. right; assumption.
    + inversion H4; assumption.
Qed.

(* What is needed at function entry to unmarshal the parameters *)
Theorem repr_asgn_fun_entry:
  forall args_b args_ofs argsIdent F p m k xs locs vs7 asgn lenv lenv',
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    mem_after_asgn args_b args_ofs m (skipn nParam locs) (skipn nParam vs7) ->
    right_param_asgn argsIdent (skipn nParam xs) (skipn nParam locs) asgn ->
    lenv_param_asgn_i lenv lenv' (skipn nParam xs) (skipn nParam vs7) ->
    NoDup xs ->
    ~ List.In argsIdent xs ->
    Forall (fun i : N => (0 <= Z.of_N i < max_args)%Z) locs ->
    clos_refl_trans state (traceless_step2 (globalenv p))
               (State F asgn k empty_env lenv m)
               (State F Sskip k empty_env lenv' m).
Proof.
  intros. eapply repr_asgn_fun_entry_aux; eauto.
  - intros. intro; subst. apply H4. eapply In_skipn; eauto.
  - clear -H5. revert nParam. induction locs; intros; [destruct nParam; constructor|].
    destruct nParam; [exact H5|]. simpl. apply IHlocs. inversion H5; assumption.
Qed.

(* CHANGE THIS *)    
(* after stepping through a repr_asgn_fun', argsIdent[i] contain valuees y_i *)
(* rest of m is the same *)
(* maybe also have that L stays the same between the two *)
(* also wants NoDup on i *)
Theorem repr_asgn_fun_mem:
  forall fu lenv p rho e fenv max_alloc rep_env finfo_env,
  forall ys inf s m,
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
 rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
 correct_tinfo p max_alloc lenv m ->
 Forall (fun x => exists v, get_var_or_funvar p lenv x v) ys ->
 Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z inf ->
 NoDup inf ->
 repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p ys inf s ->
 exists m', 
  (forall k, clos_refl_trans state (traceless_step2 (globalenv p))
    (State fu s k empty_env lenv m)
    (State fu Sskip k empty_env lenv m')) /\ mem_of_asgn argsIdent p lenv ys inf m' /\rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e  rho m' lenv /\ correct_tinfo p max_alloc lenv m'.
Proof.
  intros fu lenv p rho e fenv max_alloc rep_env finfo_env.
  induction ys; intros inf s m Hsym HfinfoCorrect Hrel_mem Htinfo Hfys Hfinf Hnodub Hasgn; inv Hasgn.
  - (* ys = [] inf = [] *)
    assert (Htinfo' := Htinfo).
    destruct Htinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
    exists m.
    repeat split; try assumption.
    + intros. constructor 2.
    + econstructor. eauto.

  -  (* ys = a::ys0 inf = i::inf0 *)
    assert (Harchi : Archi.ptr64 = true) by (vm_compute; reflexivity).
    assert (Hfinf' := Hfinf).
    inv Hfys; inv Hfinf. destruct H1.
    assert (Hnodub' := Hnodub). inv Hnodub.
    specialize (IHys inf0 s0 m Hsym HfinfoCorrect Hrel_mem Htinfo H2 H5 H7 H3).
    destruct IHys as [m' [Hclo_m' [Hmem_m' [Hrel_m' Htinfo_m']]]].
    assert (Htinfo_m'c := Htinfo_m').
    destruct Htinfo_m' as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 Htinf2]]]]]]]]]]]]]]]]].
    assert (Hm'_valid : Mem.valid_access m' int_chunk args_b (Ptrofs.unsigned
                                                               (Ptrofs.add args_ofs
                                                                        (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr (Z.of_N i))))) Writable).
    apply Hrange_args. auto.
    assert (Hm' := Mem.valid_access_store _ _ _ _ x Hm'_valid).
    destruct Hm' as [m2 Hm2].
    exists m2.

    (* apply mem_of_asgn_cons *)
    assert (Hm2' := Hm2).
    rewrite int_z_mul in Hm2'.

    assert (Hargs_bound : (0 <= Ptrofs.unsigned args_ofs + int_size * max_args <= Ptrofs.max_unsigned)%Z).
    { split.
      apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Ptrofs.unsigned_range.
      unfold int_size, int_chunk, LambdaANF_to_Clight.int_chunk; rewrite Harchi; simpl size_chunk; unfold max_args; lia.
      auto. }
    assert (Hmem_of_asgn := mem_of_asgn_cons _ _ _ _ _ _ _ _ _ _ _ _ Hmem_m' Hnodub' Hfinf' Hargs_bound Htinfo_m'c Hget_args H Hm2').

    split.

    (* step through cons and then asgn *)
    { intro.
      eapply rt_trans.
      constructor. constructor.
      eapply rt_trans.
      apply Hclo_m'.
      eapply rt_trans. constructor. constructor.
      constructor. econstructor. constructor. econstructor. constructor. eauto.
      unfold c_int, LambdaANF_to_Clight.c_int; rewrite Harchi. constructor.
      { (* sem_add *)
        unfold add, LambdaANF_to_Clight.add, sem_binary_operation, sem_add.
        simpl typeof.
        unfold val, LambdaANF_to_Clight.val, uval, LambdaANF_to_Clight.uval,
               c_int, LambdaANF_to_Clight.c_int.
        rewrite Harchi. unfold classify_add. simpl typeconv. cbv beta iota.
        f_equal. f_equal. f_equal. f_equal.
        unfold Ptrofs.mul, Ptrofs.of_int64, sizeof. simpl.
        assert (Hn_range: (0 <= Z.of_N i < max_args)%Z) by auto.
        unfold max_args in Hn_range.
        repeat (try rewrite Int64.unsigned_repr
          by (unfold Int64.max_unsigned; simpl; lia);
        try rewrite Ptrofs.unsigned_repr
          by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto;
              simpl; lia)).
        reflexivity. }
      eapply get_var_or_funvar_eval; eauto.
      eapply get_var_or_funvar_semcast; eauto.
      { (* assign_loc *)
        assert (Hofs_eq : Ptrofs.mul (Ptrofs.repr (if Archi.ptr64 then 8%Z else 4%Z))
                    (Ptrofs.of_int64 (Int64.repr (Z.of_N i)))
                  = Ptrofs.repr (int_size * Z.of_N i)).
        { unfold Ptrofs.mul, Ptrofs.of_int64, int_size, int_chunk, LambdaANF_to_Clight.int_chunk.
          rewrite Harchi. simpl. unfold max_args in *.
          rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
          rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto; simpl; lia).
          rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto; simpl; lia).
          reflexivity. }
        eapply assign_loc_value.
        - unfold val, LambdaANF_to_Clight.val, int_chunk, LambdaANF_to_Clight.int_chunk;
          simpl; reflexivity.
        - rewrite Hofs_eq.
          unfold Mem.storev.
          assert (Hint_chunk_eq : int_chunk = Mptr).
          { unfold int_chunk, LambdaANF_to_Clight.int_chunk, AST.Mptr. rewrite Harchi. reflexivity. }
          rewrite Hint_chunk_eq in Hm2'. exact Hm2'. } }

    split; auto.
    split.
    eapply rel_mem_update_protected with (m := m'); eauto.

    eapply correct_tinfo_valid_access; eauto.
    eapply mem_range_valid. intros.
    eapply Mem.store_valid_access_1; eauto.
    unfold max_args in *. clear Harchi. solve_ptrofs_range.
Qed.




Definition program_isPtr_inv (p:program) :=
  exists b_isPtr name sg, Genv.find_symbol (globalenv p) isptrIdent = Some b_isPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_isPtr Ptrofs.zero) = Some (External (EF_external name sg) (Tcons val Tnil)  (Tint IBool Unsigned noattr)   {| cc_vararg := None; cc_unproto := false; cc_structret := false |}) /\
                                  (forall m n, Events.external_functions_sem name sg (Genv.globalenv p) [make_vint n] m [] Vfalse m) /\
                                  (forall m b i, Events.external_functions_sem name sg (Genv.globalenv p) [Vptr b i] m [] Vtrue m).


 (*  deprecated version
the lenv should actually be post asgn 

 e_lenv_param_asgn_i  vsm4 lenv_new' vs7 Hl_temp Hnd_vs0
where lenv_new' = (M.set limitIdent (Vptr alloc_b limit_ofs) (M.set allocIdent (Vptr alloc_b alloc_ofs) lenv_new))
Definition program_gc_inv (p:program) :=
  exists b_gcPtr name sg, Genv.find_symbol (globalenv p) gcIdent = Some b_gcPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_gcPtr Int.zero) = Some (External (EF_external name sg) (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                            {|
                              cc_vararg := None;
                              cc_unproto := false;
                              cc_structret := false |}) /\
                          forall lenv m rho rep_env finfo_env finfo_b finfo_maxalloc fenv e tinf_b tinf_ofs args_b args_ofs,
                            rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
                            M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
                            Mem.loadv int_chunk m (Vptr finfo_b Int.zero) = Some (Vint finfo_maxalloc) ->
                            deref_loc valPtr m tinf_b (Int.add tinf_ofs (Int.repr (3*int_size))) (Vptr args_b args_ofs) -> 
                          exists v m' alloc_b alloc_ofs limit_ofs,
                            (Events.external_functions_sem name sg (Genv.globalenv p) [Vptr finfo_b Int.zero; Vptr tinf_b tinf_ofs] m [] v m') /\
                            (* get new alloc *)                            
                            deref_loc valPtr m' tinf_b tinf_ofs (Vptr alloc_b alloc_ofs) /\
                             (* get new limit *)
                            deref_loc valPtr m' tinf_b (Int.add tinf_ofs (Int.repr int_size)) (Vptr alloc_b limit_ofs)  /\
                            (* same args block and offset *)
                            deref_loc valPtr m' tinf_b (Int.add tinf_ofs (Int.repr (3*int_size))) (Vptr args_b args_ofs)  /\
                            (* same thing in the args block *)
                             mem_same_block args_b m m' /\
                             (forall lenv' : temp_env,
                                 forall vsm4 vs7 vars, 
   lenv_param_asgn
     (M.set argsIdent (Vptr args_b args_ofs)
        (M.set limitIdent (Vptr alloc_b limit_ofs)
           (M.set allocIdent (Vptr alloc_b alloc_ofs)
                 (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs)
                    (create_undef_temps
                       vars)))))
     lenv' vsm4 vs7 ->
   rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m' lenv' /\
   correct_tinfo p (Int.unsigned finfo_maxalloc) lenv' m'). *)
                                          
(* deep version of mem_after_asgn  *)
 Inductive rel_mem_asgn {fenv finfo_env p rep_env} args_b args_ofs m L: list cps.val -> list N -> list Values.val -> Prop :=
  | rma_cons: forall  i v6 v7  vs6 inf vs7, 
    rel_mem_asgn args_b args_ofs  m L vs6 inf vs7 ->
    Mem.loadv int_chunk m (Vptr args_b (Ptrofs.add args_ofs (Ptrofs.repr (int_size * (Z.of_N i))))) = Some v7 ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L v7 ->
     rel_mem_asgn args_b args_ofs  m L (v6::vs6) (i::inf) (v7::vs7)
| rma_nil:
    rel_mem_asgn args_b args_ofs  m L [] [] []. 
 
 Theorem rel_mem_asgn_length:
   forall {fenv finfo_env p rep_env m L args_b args_ofs ys inf vs},
     @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L ys inf vs ->
    length ys = length vs.
 Proof.
   induction ys; intros.
   inv H; auto.
   inv H. simpl. erewrite IHys. reflexivity.
   eauto.
 Qed.

 
 Theorem rel_mem_asgn_nthN:
  forall {L rep_env finfo_env fenv args_b args_ofs p  m vs6 inf vs7 v6 v7 n},
  @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs  m L vs6 inf vs7 -> 
  nthN vs6 n = Some v6 ->
  nthN vs7 n = Some v7 ->
  repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L v7.
Proof.
  induction vs6; intros.
  inv H0.
  destruct vs7. inv H1.
  inv H.
  destruct n. inv H0; inv H1; auto.  
  apply nthN_pos_pred in H0.
  apply nthN_pos_pred in H1.
  eapply IHvs6; eauto.
Qed.


 Theorem cons_get_list: forall {A y ys rho vs},
   @get_list A (y::ys) rho = Some vs ->
   exists v vs',
     v::vs' = vs /\ M.get y rho = Some v /\ @get_list A ys rho = Some vs'.
 Proof.
   intros. simpl in H. destruct (M.get y rho) eqn:Hgy; destruct (get_list ys rho) eqn:Hgys.
   exists a, l. split. inv H; auto. split; reflexivity.
   inv H. inv H. inv H.
 Qed.


 Theorem rel_mem_after_asgn: 
   forall fenv finfo_env p rep_env args_b args_ofs m L vs6 locs vs7,
   @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs  m L vs6 locs vs7 ->
     mem_after_asgn args_b args_ofs m locs vs7.
 Proof.
   induction vs6; intros.
   - inv H.
     constructor.
   - inv H.
     constructor; eauto.
 Qed.
 
Theorem rel_mem_of_asgn: forall fenv finfo_env  rep_env args_b args_ofs p lenv m rho L ys inf vs7 vs6,
 mem_of_asgn_v args_b args_ofs p lenv m ys inf vs7 ->
 get_list ys rho = Some vs6 ->
 (forall x, List.In x ys ->
            exists v6, M.get x rho = Some v6 /\
                       repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L lenv x) ->
 @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L vs6 inf vs7.
Proof.
  induction ys; intros.
  -   inv H0; inv H. constructor.
  - apply cons_get_list in H0. destruct H0 as [v [vs' [Heqvs [Hgar Hgysr]]]]. subst.
    inv H. constructor.
    eapply IHys; eauto. intros. eapply H1. constructor 2; auto.
    eauto.
    assert (Hli: List.In a (a :: ys)) by (constructor; reflexivity).
    apply H1 in Hli. destruct Hli. destruct H. inv H7; inv H0.
    rewrite H2 in H5. inv H5. rewrite H in Hgar. inv Hgar. auto.
    rewrite H2 in H5; inv H5. rewrite H2 in H7; inv H7.
    rewrite H5 in H8; inv H8. rewrite H in Hgar. inv Hgar. auto.
Qed. 

(* invariant for GC, needs to be shown to be provable from GC proof *)
(* OS: Changed returned vs7 into vs7' s.t. the pointers can have changed (but represent the same values in LambdaANF) *)
 Definition program_gc_inv (p:program) :=
  exists b_gcPtr name sg, Genv.find_symbol (globalenv p) gcIdent = Some b_gcPtr /\
                          Genv.find_funct (globalenv p) (Vptr  b_gcPtr Ptrofs.zero) = Some (External (EF_external name sg) (Tcons (Tpointer val noattr) (Tcons (Tpointer (Tstruct threadInfIdent noattr) noattr) Tnil)) Tvoid
                            {|
                              cc_vararg := None;
                              cc_unproto := false;
                              cc_structret := false |}) /\
                          forall lenv m finfo_b finfo_env (p:program) rep_env finfo_maxalloc fenv tinf_b tinf_ofs args_b args_ofs L vs6 vs7 inf,
                            @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m L vs6 inf vs7 -> 
                            M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
                            Mem.loadv int_chunk m (Vptr finfo_b Ptrofs.zero) = Some (make_vint finfo_maxalloc) ->
                            (int_size * finfo_maxalloc <= gc_size)%Z ->
                            deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (3*int_size))) Full (Vptr args_b args_ofs) ->
                          exists v m' alloc_b alloc_ofs limit_ofs L' vs7',
                            (Events.external_functions_sem name sg (Genv.globalenv p) [Vptr finfo_b Ptrofs.zero; Vptr tinf_b tinf_ofs] m [] v m') /\
                            (* get new alloc *)
                            deref_loc valPtr m' tinf_b tinf_ofs Full (Vptr alloc_b alloc_ofs) /\
                             (* get new limit *)
                            deref_loc valPtr m' tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)) Full (Vptr alloc_b limit_ofs)  /\
                            (* same args block and offset *)
                            deref_loc (Tarray uval maxArgs noattr) m' tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr (3*int_size))) Full (Vptr args_b args_ofs)  /\
                            (* deep copied arguments *)
                            @rel_mem_asgn fenv finfo_env p rep_env args_b args_ofs m' L' vs6 inf vs7' /\
                            Mem.unchanged_on (fun b z => and (~(L b z)) (and (~ (L' b z)) (b <> tinf_b))) m m' /\
                            (* SEP :- this is just L' disjoint from m \ L + tinfo AND tinfo [args, alloc_b] is disjoint from global *) 
                            protected_not_in_L_id p  (M.set argsIdent (Vptr args_b args_ofs) (M.set limitIdent (Vptr alloc_b limit_ofs)
               (M.set allocIdent (Vptr alloc_b alloc_ofs)
                      (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) (M.empty _))))) L' /\
                            (* Some SEP, some GC :- enough space in nursey, aligned pointers, enough space in args *)
                            correct_tinfo p finfo_maxalloc (M.set argsIdent (Vptr args_b args_ofs)
            (M.set limitIdent (Vptr alloc_b limit_ofs)
               (M.set allocIdent (Vptr alloc_b alloc_ofs)
                     (Maps.PTree.set tinfIdent (Vptr tinf_b tinf_ofs) (M.empty _)))))  m'.




 (* Working towards a clearer interface with the gc 

 
About meminj.
About Mem.mem_inj.
   sep1) inject f m m'
       if not L or tinfo, then f = x -> Some (x, 0)

   gc1) deep roots are copied to L' (in m')
   sep2)
       If y in L', then either in L or did not exists in m, i.e. there doesn't exists an x, f x = y

   gc2) limit - alloc > tinfo.max_alloc

as injection, this looks like:


          

  *)

 


(* find the right co for threadInf *)

 
Definition program_threadinfo_inv (p:program) :=
  exists co, 
    Maps.PTree.get threadInfIdent (genv_cenv (globalenv p))= Some co /\
    co_members co =  (Member_plain allocIdent valPtr ::
                         Member_plain limitIdent valPtr :: Member_plain heapInfIdent (Tpointer (Tstruct heapInfIdent noattr) noattr) ::
                         Member_plain argsIdent (Tarray val maxArgs noattr) :: nil).

Ltac fold_ident_peq :=
  repeat match goal with
  | |- context [ident_eq ?x ?y] => change (ident_eq x y) with (Coqlib.peq x y)
  end.

Theorem allocIdent_delta:
  forall p,
      field_offset p allocIdent
    [Member_plain allocIdent valPtr; Member_plain limitIdent valPtr; Member_plain heapInfIdent (Tpointer (Tstruct heapInfIdent noattr) noattr);
       Member_plain argsIdent (Tarray uval maxArgs noattr)] = OK (0%Z, Full).
Proof.
   intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  fold_ident_peq;
  assert (Hnd := disjointIdent);
  inv Hnd; rewrite Coqlib.peq_true;
  reflexivity.
Qed.


Theorem limitIdent_delta:
  forall p,
      field_offset p limitIdent
    [Member_plain allocIdent valPtr; Member_plain limitIdent valPtr; Member_plain heapInfIdent (Tpointer (Tstruct heapInfIdent noattr) noattr);
       Member_plain argsIdent (Tarray uval maxArgs noattr)] = OK ((1*int_size)%Z, Full).
Proof.
   intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  fold_ident_peq;
  assert (Hnd := disjointIdent);
  inv Hnd.
  - rewrite Coqlib.peq_false; [| solve_nodup].
    rewrite Coqlib.peq_true. reflexivity.
  - vm_compute in Harchi. discriminate.
Qed.

Theorem argsIdent_delta:
  forall p,
  field_offset p argsIdent
    [Member_plain allocIdent valPtr; Member_plain limitIdent valPtr;
    Member_plain heapInfIdent (Tpointer (Tstruct heapInfIdent noattr) noattr);
    Member_plain argsIdent (Tarray uval maxArgs noattr)] = OK ((3*int_size)%Z, Full).
Proof.
  intro. chunk_red; archi_red; simpl; unfold field_offset; simpl;
  fold_ident_peq;
  assert (Hnd := disjointIdent);
  inv Hnd.

  - rewrite Coqlib.peq_false; [| solve_nodup].
    rewrite Coqlib.peq_false; [| solve_nodup].
    rewrite Coqlib.peq_false; [| solve_nodup].
    rewrite Coqlib.peq_true. reflexivity.
  - vm_compute in Harchi. discriminate.
Qed.    

Theorem find_symbol_map:
  forall p fenv m finfo_env id v, 
    find_symbol_domain p finfo_env ->
    var_or_funvar id m fenv finfo_env p v (makeVar id m v fenv finfo_env).
Proof. 
  intros. specialize (H v). inv H. 
  destruct (cps.M.get v finfo_env) eqn:Hgvm.
  - destruct (H0 (ex_intro _ p0 eq_refl)). econstructor. apply H.
  - unfold makeVar. rewrite Hgvm. econstructor.
    destruct (Genv.find_symbol (Genv.globalenv p) v) eqn:Hgpv; auto.
    exfalso.
    destruct (H1 (ex_intro _ b eq_refl)).
    inv H.
Qed.
 
Theorem find_symbol_map_f:
    forall p fenv m finfo_env id v, 
    find_symbol_domain p finfo_env ->
    var_or_funvar_f id m fenv finfo_env p v = makeVar id m v fenv finfo_env.
Proof. 
  intros. apply var_or_funvar_of_f.
  apply find_symbol_map; auto.
Qed.

Theorem asgnAppVars_correct:
  forall p fenv finfo_env,
    forall vs avs ind aind s,
    find_symbol_domain p finfo_env ->
      avs = skipn nParam vs ->
      aind = skipn nParam ind ->
      asgnAppVars' argsIdent threadInfIdent nParam vs ind fenv finfo_env = Some s ->
      repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p avs aind s.
Proof.
  intros p fenv finfo_env vs avs. generalize vs. clear vs.
  induction avs; intros vs ind aind s Hfinfo_env Hvs Hind Hasgn; unfold asgnAppVars' in Hasgn.
  - destruct aind; rewrite <- Hvs in Hasgn; rewrite <- Hind in Hasgn;
      destruct nParam; inv Hasgn; constructor.
  - destruct aind; rewrite <- Hvs in Hasgn; rewrite <- Hind in Hasgn; [ destruct nParam; inv Hasgn | ].
    destruct vs; [destruct nParam; inv Hvs | ].
    destruct ind; [destruct nParam; inv Hind | ].
    symmetry in Hvs.
    set (Hvs' := skipn_cons nParam p0 a vs avs Hvs).
    symmetry in Hvs'.
    symmetry in Hind.
    set (Hind' := skipn_cons nParam n0 n ind aind Hind).
    symmetry in Hind'.
    simpl in Hasgn.
    destruct (asgnAppVars'' argsIdent threadInfIdent nParam avs aind fenv) eqn:Happ.
    2: inv Hasgn.
    specialize (IHavs _ _ _ s0 Hfinfo_env Hvs' Hind').
    unfold asgnAppVars' in IHavs.
    rewrite <- Hvs' in IHavs.
    rewrite <- Hind' in IHavs.
    apply IHavs in Happ.
    inv Hasgn.
    erewrite <- find_symbol_map_f; eauto.
    exact (repr_asgn_cons _ _ _ _ _ _ _ _ _ _ s0 Happ).
Qed.    

Theorem repr_call_vars_length1 : forall p fenv map n l1 l2, repr_call_vars threadInfIdent nParam fenv map p  n l1 l2 -> length l1 = n.
Proof.
      induction n; intros l1 l2 Hr; destruct l1; inv Hr.
      + reflexivity. 
      + simpl. apply f_equal.
        eapply IHn. eauto.
Qed.   

 
Lemma var_or_funvar_f'_makeVar:
  forall p fenv finfo_env v,
    find_symbol_domain p finfo_env ->
    var_or_funvar_f' threadInfIdent fenv finfo_env p nParam v =
    makeVar threadInfIdent nParam v fenv finfo_env.
Proof.
  intros. unfold var_or_funvar_f'.
  specialize (H v). destruct H as [Hfwd Hrev].
  destruct (M.get v finfo_env) eqn:Hget.
  - destruct p0. destruct (Hfwd (ex_intro _ (p0, f) eq_refl)) as [b Hb].
    rewrite Hb. reflexivity.
  - destruct (Genv.find_symbol (Genv.globalenv p) v) eqn:Hfs.
    + exfalso. destruct (Hrev (ex_intro _ b eq_refl)) as [v1 Hv1].
      rewrite Hv1 in Hget. discriminate.
    + unfold makeVar. rewrite Hget. reflexivity.
Qed.

Theorem  mkCallVars_correct:
  forall p fenv map n vs bvs es,
    find_symbol_domain p map ->
    bvs = firstn nParam vs ->
    mkCallVars threadInfIdent nParam fenv map n bvs = Some es ->
    repr_call_vars threadInfIdent nParam fenv map p n bvs es.
Proof.
  intros p fenv map n vs bvs es Hsym bvsEq Hcall.
  unfold repr_call_vars.
  clear bvsEq vs.
  revert bvs es Hcall.
  induction n; intros bvs es Hcall;
    destruct bvs; simpl in Hcall; try discriminate.
  - inv Hcall. constructor.
  - destruct (mkCallVars threadInfIdent nParam fenv map n bvs) eqn:Hrest; inv Hcall.
    rewrite <- (var_or_funvar_f'_makeVar p fenv map) by auto.
    constructor.
    apply IHn. exact Hrest.
Qed.


Theorem repr_make_case_switch:
  forall x ls ls',
  repr_switch_LambdaANF_Codegen isptrIdent caseIdent x ls ls' (make_case_switch isptrIdent caseIdent x ls ls').
Proof.
  intros.
  constructor.
Qed.


Definition makeCases (p0:program) fenv cenv ienv map :=
 (fix makeCases (l : list (ctor_tag * exp)) :
            option (labeled_statements * labeled_statements) :=
            match l with
            | [] => Some (LSnil, LSnil)
            | q :: l' =>
                match
                  (@LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims (snd q) fenv cenv ienv map)
                with
                | None => None
                | Some prog =>
                   match (makeCases l') with
                   | None => None
                   | Some (ls, ls') =>
                      match make_ctor_rep cenv (fst q) with
                      | Some (enum t) =>
                        let tag := ((Z.shiftl (Z.of_N t) 1) + 1)%Z in
                          match ls' with
                          | LSnil =>
                              Some (ls, LScons None  (Ssequence prog Sbreak) ls')
                          | LScons _ _ _ =>
                              Some
                                (ls,
                                LScons (Some (Z.shiftr tag 1))
                                  (Ssequence prog Sbreak) ls')
                          end
                      | Some (boxed t a) =>
                        let tag := ((Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z in
                          match ls with
                          | LSnil =>
                              Some (LScons None (Ssequence prog Sbreak) ls, ls')
                          | LScons _ _ _ =>
                              Some
                                (LScons (Some (Z.land tag 255))
                                   (Ssequence prog Sbreak) ls,
                                ls')
                          end
                      | None => None
                      end
                   end
                end
            end).

Definition fmake_ctor_rep (p:positive) (c:ctor_ty_info) : ctor_rep :=
  let '(Build_ctor_ty_info name _ it  a  n) := c in
      match (a =? 0)%N with
      | true =>
        (enum n)
      | false =>
        (boxed n a)
      end.


Definition compute_rep_env (cenv:ctor_env): M.t ctor_rep :=
  M.map fmake_ctor_rep cenv.


  
Theorem crep_cenv_correct:
forall cenv rep_env, 
  correct_crep_of_env cenv rep_env ->
  forall c, 
    make_ctor_rep cenv c =  M.get c rep_env.
Proof.
  intros. unfold make_ctor_rep.
  destruct (cps.M.get c cenv) eqn:Hgc.
  - destruct c0.
    simpl.
    destruct (ctor_arity =? 0)%N eqn:Hn0.    
    + rewrite N.eqb_eq in Hn0. subst.
      inv H. specialize (H0 _ _ _ _ _ _ Hgc). destruct H0. destruct H. inv H0; rewrite H2 in Hgc; inv Hgc. auto.
    + rewrite N.eqb_neq in Hn0.
      inv H. specialize (H0 _ _ _ _ _ _ Hgc). destruct H0. destruct H. inv H0; rewrite H2 in Hgc; inv Hgc.  exfalso; apply Hn0; auto.
      auto. 
  -  simpl. symmetry.
     inv H. destruct (M.get c rep_env) eqn:Hcr.
     exfalso. apply H1 in Hcr. inv Hcr; rewrite H in Hgc; inv Hgc. auto.
Qed.
 
Theorem nth_proj_assign': 
      forall p fenv finfo_env,
        find_symbol_domain p finfo_env ->
        forall v l a n,
        Forall_statements_in_seq' (is_nth_projection_of_x threadInfIdent nParam fenv finfo_env p v) 
                                  (a :: l) (assignConstructorS' threadInfIdent nParam fenv finfo_env v n (a :: l)) (Z.of_nat n).
Proof.
  induction l; intros.
  - (* last *)
    simpl. constructor.
    constructor.
    apply find_symbol_map; eauto.
  - (* IH *)
    specialize (IHl a (S n)).
    remember (a::l) as l'. simpl.
    rewrite Heql'.  constructor.
    rewrite Nat2Z.inj_succ in IHl.
    rewrite <- Heql'. rewrite Nat.add_1_r. auto.
    constructor.
    apply find_symbol_map; eauto.
Qed.


Theorem nth_proj_assign:
      forall p fenv finfo_env ,
        find_symbol_domain p finfo_env ->
        forall v l,
          length l > 0 ->
      Forall_statements_in_seq (is_nth_projection_of_x threadInfIdent nParam fenv finfo_env p v) l (assignConstructorS' threadInfIdent nParam fenv finfo_env v 0 l).
Proof.
  induction l.
  intros Hl. inv Hl.
  intros. unfold Forall_statements_in_seq.
  apply nth_proj_assign'. auto.
Qed.

Theorem repr_asgn_constructorS:
  forall p cenv ienv  rep_env fenv finfo_env v c l s name iname it n,
      find_symbol_domain p finfo_env ->
  correct_crep_of_env cenv  rep_env ->
  M.get c cenv = Some  (Build_ctor_ty_info name iname it (N.of_nat (length l)) n) ->
        assignConstructorS allocIdent threadInfIdent nParam cenv ienv fenv finfo_env v c l = Some s -> 
repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env v c l s.
Proof.
  intros p cenv ienv rep_env fenv map v c l s name iname it n Hsymbol; intros.
  unfold assignConstructorS in *.
    destruct (makeTag cenv c) eqn:H_makeTag.
    destruct (make_ctor_rep cenv c) eqn:H_make_ctor_rep.
    simpl in H1. destruct c0; inv H1.
  - unfold make_ctor_rep in H_make_ctor_rep. rewrite H0 in H_make_ctor_rep. simpl in *.
    destruct ((N.of_nat (length l) =? 0)%N ) eqn:Hll; inv H_make_ctor_rep.
    rewrite OrdersEx.N_as_OT.eqb_eq in Hll.
    destruct l; inv Hll.
    unfold makeTag in *.
    destruct (makeTagZ cenv c) eqn:H_makeTagZ; inv H_makeTag.
    inv H. specialize (H1 _ _ _ _ _ _ H0). inv H1. inv H. inv H3; rewrite H0 in H; inv H.
    econstructor. apply H1. 
    {split.  unfold makeTagZ in *.  unfold make_ctor_rep in *. rewrite H0 in H_makeTagZ. simpl in H_makeTagZ. inv H_makeTagZ.
     reflexivity. 
     auto. }
  - unfold make_ctor_rep in H_make_ctor_rep. rewrite H0 in H_make_ctor_rep. simpl in *.
    destruct ((N.of_nat (length l) =? 0)%N ) eqn:Hll; inv H_make_ctor_rep.
    unfold makeTag in H_makeTag. 
    destruct (makeTagZ cenv c) eqn:H_makeTagZ; inv H_makeTag.
    inv H. specialize (H1 _ _ _ _ _ _ H0). destruct H1. destruct H.
    rewrite OrdersEx.N_as_OT.eqb_neq in Hll.
    inv H1; rewrite H3 in H0; inv H0. exfalso; auto.
    cbn [LambdaANF_to_Clight.allocPtr].
    econstructor 1; eauto.
    { split. unfold makeTagZ in *. unfold make_ctor_rep in *.
      rewrite H3 in H_makeTagZ. simpl in H_makeTagZ.
      inv H_makeTagZ; auto.
      split; auto.  }
    apply nth_proj_assign. auto.
    destruct l. exfalso; auto. lia.
  - simpl in H1; inv H1.
  - simpl in H1. inv H1.
Qed.






Theorem make_crep_none:
  forall c cenv,
  make_ctor_rep cenv c = None ->
  M.get c cenv = None.
Proof.
  intros.
  unfold make_ctor_rep in *.
  destruct (cps.M.get c cenv); auto.
  exfalso. destruct c0. inv H.
  destruct (ctor_arity =? 0)%N; inv H1.
Qed.

Theorem make_tagZ_none:
  forall c cenv,
  makeTagZ cenv c = None ->
  M.get c cenv = None.
Proof.
  intros.
  unfold makeTagZ in *.
  unfold make_ctor_rep in *.
  destruct (cps.M.get c cenv). destruct c0. simpl in H.
  destruct  (ctor_arity =? 0)%N; inv H. auto.
Qed.

(* Predicate: expression contains no primitive operations *)
Inductive no_primops : exp -> Prop :=
| np_constr : forall x t vs e, no_primops e -> no_primops (Econstr x t vs e)
| np_case : forall v cl, Forall (fun p => no_primops (snd p)) cl -> no_primops (Ecase v cl)
| np_proj : forall x t n v e, no_primops e -> no_primops (Eproj x t n v e)
| np_letapp : forall x f t ys e, no_primops e -> no_primops (Eletapp x f t ys e)
| np_fun : forall fds e, no_primops (Efun fds e)
| np_app : forall f t ys, no_primops (Eapp f t ys)
| np_halt : forall x, no_primops (Ehalt x).

(* Helper: makeCases produces branches related by repr_branches_LambdaANF_Codegen *)
Lemma makeCases_correct:
  forall fenv cenv ienv p rep_env map,
    find_symbol_domain p map ->
    finfo_env_correct fenv map ->
    correct_crep_of_env cenv rep_env ->
    forall cl ls ls',
      Forall (fun p => no_primops (snd p)) cl ->
      Forall (fun p => correct_cenv_of_exp cenv (snd p)) cl ->
      Forall (fun pe =>
        forall stm,
          no_primops (snd pe) ->
          correct_cenv_of_exp cenv (snd pe) ->
          @LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims (snd pe) fenv cenv ienv map = Some stm ->
          repr_expr_LambdaANF_Codegen_id fenv map p rep_env (snd pe) stm) cl ->
      makeCases p fenv cenv ienv map cl = Some (ls, ls') ->
      repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv map p rep_env cl ls ls'.
Proof.
  intros fenv cenv ienv p rep_env map Hsym HfinfoCorrect Hcrep.
  induction cl as [| [c e] cl' IHcl]; intros ls ls' Hnp Hcenv_cl Hrepr_cl Hmc.
  - simpl in Hmc. inv Hmc. constructor.
  - simpl in Hmc.
    destruct (@LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map) eqn:Htb; [| inv Hmc].
    destruct (makeCases p fenv cenv ienv map cl') eqn:Hmc'; [| inv Hmc].
    destruct p0 as [ls0 ls0'].
    inversion Hnp as [| [c1 e1] cl1 Hnp_hd Hnp_tl]; subst.
    inversion Hcenv_cl as [| [c2 e2] cl2 Hcenv_hd Hcenv_tl]; subst.
    inversion Hrepr_cl as [| [c3 e3] cl3 Hrepr_hd Hrepr_tl]; subst.
    assert (Hprog : repr_expr_LambdaANF_Codegen_id fenv map p rep_env e s).
    { eapply Hrepr_hd; eauto. }
    assert (Hcl' : repr_branches_LambdaANF_Codegen argsIdent allocIdent limitIdent threadInfIdent tinfIdent isptrIdent caseIdent nParam fenv map p rep_env cl' ls0 ls0').
    { eapply IHcl; eauto. }
    rewrite (crep_cenv_correct _ _ Hcrep) in Hmc.
    destruct (M.get c rep_env) eqn:Hrep; [| inv Hmc].
    destruct c0.
    + (* enum *)
      destruct ls0'; inv Hmc.
      * eapply Runboxed_default_br; eauto.
      * eapply Runboxed_br; eauto.
        inv Hcrep. apply H0 in Hrep. inv Hrep.
        split; auto.
    + (* boxed *)
      destruct ls0; inv Hmc.
      * eapply Rboxed_default_br; eauto.
      * eapply Rboxed_br; eauto.
        inv Hcrep. apply H0 in Hrep. inv Hrep.
        split; [reflexivity | split; auto].
Qed.

(* Main Theorem *)
Theorem translate_body_correct:
  forall fenv cenv ienv  p rep_env map,
    find_symbol_domain p map ->
    finfo_env_correct fenv map ->
    correct_crep_of_env cenv rep_env ->
    forall  e stm,
      no_primops e ->
      correct_cenv_of_exp cenv e ->
    @LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map = Some stm ->
    repr_expr_LambdaANF_Codegen_id fenv map p rep_env e stm.
Proof.
  intros fenv cenv ienv p rep_env map Hsym HfinfoCorrect Hcrep.
  pose (P :=
    fun e =>
      forall stm,
        no_primops e ->
        correct_cenv_of_exp cenv e ->
        @LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map = Some stm ->
        repr_expr_LambdaANF_Codegen_id fenv map p rep_env e stm).
  assert (HP : forall e, P e).
  {
    eapply (exp_mut_alt P (fun _ => True)); unfold P; intros.
    - (* Econstr *)
      simpl in H2.
      destruct (assignConstructorS allocIdent threadInfIdent nParam cenv ienv fenv map v t l) eqn:Has; [| inv H2].
      destruct (@LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map) eqn:Htb'; [| inv H2].
      inv H2.
      econstructor.
      + assert (Hcenv_constr := H1 v t l e (rt_refl _ _ _)).
        unfold correct_cenv_of_exp, Forall_constructors_in_e in Hcenv_constr.
        destruct (M.get t cenv) as [ci|] eqn:Hgc; [| contradiction].
        destruct ci.
        eapply repr_asgn_constructorS; eauto.
        rewrite <- Hcenv_constr in Hgc. exact Hgc.
      + eapply H; eauto.
        * inv H0. auto.
        * eapply Forall_constructors_subterm; [exact H1 |].
          constructor. constructor.
    - (* Ecase *)
      simpl in H2.
      change (
        match makeCases p fenv cenv ienv map l with
        | Some (ls0, ls0') => Some (make_case_switch isptrIdent caseIdent v ls0 ls0')
        | None => None
        end = Some stm) in H2.
      destruct (makeCases p fenv cenv ienv map l) as [[ls ls']|] eqn:Hmc in H2; [| inv H2].
      inv H2.
      assert (Hcenv_l : Forall (fun pe => correct_cenv_of_exp cenv (snd pe)) l).
      {
        apply Forall_forall.
        intros [g e0] Hin.
        eapply correct_cenv_of_case in H1.
        eapply H1; eauto.
      }
      econstructor.
      + eapply makeCases_correct.
        * exact Hsym.
        * exact HfinfoCorrect.
        * exact Hcrep.
        * inv H0; auto.
        * exact Hcenv_l.
        * exact H.
        * exact Hmc.
      + eapply repr_make_case_switch.
    - (* Eproj *)
      simpl in H2.
      destruct (@LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map) eqn:Htb'; [| inv H2].
      inv H2.
      econstructor.
      eapply H; eauto.
      * inv H0. auto.
      * eapply Forall_constructors_subterm; [exact H1 |].
        constructor. constructor.
    - (* Eletapp *)
      simpl in H2.
      destruct (@LambdaANF_to_Clight.translate_body argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent bodyName threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent nParam prims e fenv cenv ienv map) eqn:Htb'; [| inv H2].
      destruct (M.get ft fenv) as [p_ft|] eqn:Hfenv; [| inv H2].
      destruct p_ft as [nn locs].
      destruct (asgnAppVars argsIdent threadInfIdent tinfIdent nParam ys (snd (nn, locs)) fenv map) eqn:Hasn; [| inv H2].
      destruct (mkCall threadInfIdent tinfIdent nParam fenv map _ _ ys) eqn:Hmkc; [| inv H2].
      inv H2.
      unfold asgnAppVars in Hasn.
      destruct (asgnAppVars' argsIdent threadInfIdent nParam ys (snd (nn, locs)) fenv map) eqn:Hasn'; [| inv Hasn].
      inv Hasn.
      unfold mkCall in Hmkc.
      change (fst (nn, locs)) with nn in Hmkc.
      set (pnum := Init.Nat.min (N.to_nat nn) nParam) in *.
      destruct (mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam ys)) as [l_call|] eqn:Hmkcv in Hmkc; [| inv Hmkc].
      rename Hmkcv into Hmkcv_outer.
      pose proof Hmkcv_outer as Hmkcv_keep.
      try rewrite Hmkcv_outer in Hmkc.
      simpl in Hmkc.
      inversion Hmkc; subst; clear Hmkc.
      assert (Hs1 :
        s1 =
        Scall None
          (Ecast (makeVar threadInfIdent nParam f fenv map)
             (Tpointer (mkFunTy threadInfIdent pnum) noattr))
          (tinf threadInfIdent tinfIdent :: l_call)).
      {
        assert (Hmcall :
          match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam ys) with
          | Some v =>
              Some
                (Scall None
                   (Ecast (makeVar threadInfIdent nParam f fenv map)
                      (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                   (tinf threadInfIdent tinfIdent :: v))
          | None => None
          end = Some s1).
        { first [ exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8 ]. }
        rewrite Hmkcv_outer in Hmcall.
        simpl in Hmcall.
        inversion Hmcall; subst.
        reflexivity.
      }
      subst s1.
      rewrite <- (find_symbol_map_f p fenv nParam map threadInfIdent f Hsym).
      eapply (@R_letapp_e argsIdent allocIdent limitIdent threadInfIdent tinfIdent
               isptrIdent caseIdent nParam fenv map p rep_env
               x f (nn, locs) (skipn nParam (snd (nn, locs))) ys
               (skipn nParam ys) (firstn nParam ys) pnum ft
               _ l_call e s); try reflexivity.
      + exact Hfenv.
      + change (Tarray uval LambdaANF_to_Clight.maxArgs noattr) with (Tarray uval maxArgs noattr).
        change (Tarray val maxArgs noattr) with (Tarray uval maxArgs noattr).
        constructor.
        eapply asgnAppVars_correct.
        * exact Hsym.
        * reflexivity.
        * reflexivity.
        * exact Hasn'.
      + eapply mkCallVars_correct.
        * exact Hsym.
        * reflexivity.
        * exact Hmkcv_keep.
      + unfold repr_expr_LambdaANF_Codegen_id in H.
        eapply H.
        * inv H0. auto.
        * eapply Forall_constructors_subterm; [exact H1 |].
          constructor. constructor.
        * reflexivity.
      + change
          (match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam ys) with
           | Some v =>
               Some
                 (Scall None
                    (Ecast (makeVar threadInfIdent nParam f fenv map)
                       (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                    (tinf threadInfIdent tinfIdent :: v))
           | None => None
           end = Some s1) in H3.
        rewrite Hmkcv in H3.
        simpl in H3.
        discriminate.
    - (* Efun *)
      simpl in *. congruence.
    - (* Eapp *)
      simpl in H1.
      destruct (M.get t fenv) as [p_t|] eqn:Hfenv; [| inv H1].
      destruct (asgnAppVars argsIdent threadInfIdent tinfIdent nParam l (snd p_t) fenv map) eqn:Hasn; [| inv H1].
      destruct (mkCall threadInfIdent tinfIdent nParam fenv map _ _ l) eqn:Hmkc; [| inv H1].
      inv H1.
      destruct p_t as [nn locs].
      unfold asgnAppVars in Hasn.
      destruct (asgnAppVars' argsIdent threadInfIdent nParam l (snd (nn, locs)) fenv map) eqn:Hasn'; [| inv Hasn].
      inv Hasn.
      unfold mkCall in Hmkc.
      change (fst (nn, locs)) with nn in Hmkc.
      set (pnum := Init.Nat.min (N.to_nat nn) nParam) in *.
      destruct (mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l)) as [l_call|] eqn:Hmkcv in Hmkc; [| inv Hmkc].
      pose proof Hmkcv as Hmkcv_keep.
      assert (Hs0 :
        s0 =
        Scall None
          (Ecast (makeVar threadInfIdent nParam v fenv map)
             (Tpointer (mkFunTy threadInfIdent pnum) noattr))
          (tinf threadInfIdent tinfIdent :: l_call)).
      {
        assert (Hmcall :
          match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l) with
          | Some v0 =>
              Some
                (Scall None
                   (Ecast (makeVar threadInfIdent nParam v fenv map)
                      (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                   (tinf threadInfIdent tinfIdent :: v0))
          | None => None
          end = Some s0).
        {
          match goal with
          | Hm :
              (match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l) with
               | Some v0 =>
                   Some
                     (Scall None
                        (Ecast (makeVar threadInfIdent nParam v fenv map)
                           (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                        (tinf threadInfIdent tinfIdent :: v0))
               | None => None
               end = Some s0) |- _ => exact Hm
          end.
        }
        rewrite Hmkcv in Hmcall.
        simpl in Hmcall.
        inversion Hmcall; subst.
        reflexivity.
      }
      subst s0.
      rewrite <- (find_symbol_map_f p fenv nParam map threadInfIdent v Hsym).
      eapply (@R_app_e argsIdent allocIdent limitIdent threadInfIdent tinfIdent
               isptrIdent caseIdent nParam fenv map p rep_env
               v (nn, locs) (skipn nParam (snd (nn, locs))) l (skipn nParam l)
               (firstn nParam l) pnum t _ l_call); try reflexivity.
      + exact Hfenv.
      + change (Tarray uval LambdaANF_to_Clight.maxArgs noattr) with (Tarray uval maxArgs noattr).
        change (Tarray val maxArgs noattr) with (Tarray uval maxArgs noattr).
        constructor.
        eapply asgnAppVars_correct.
        * exact Hsym.
        * reflexivity.
        * reflexivity.
        * exact Hasn'.
      + eapply mkCallVars_correct.
        * exact Hsym.
        * reflexivity.
        * exact Hmkcv_keep.
      + match goal with
        | Hm :
            (match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l) with
             | Some v0 =>
                 Some
                   (Scall None
                      (Ecast (makeVar threadInfIdent nParam v fenv map)
                         (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                      (tinf threadInfIdent tinfIdent :: v0))
             | None => None
             end = Some ?s0),
          Hnone : mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l) = None |- _ =>
            change
              (match mkCallVars threadInfIdent nParam fenv map pnum (firstn nParam l) with
               | Some v0 =>
                   Some
                     (Scall None
                        (Ecast (makeVar threadInfIdent nParam v fenv map)
                           (Tpointer (mkFunTy threadInfIdent pnum) noattr))
                        (tinf threadInfIdent tinfIdent :: v0))
               | None => None
               end = Some s0) in Hm;
            rewrite Hnone in Hm;
            simpl in Hm;
            discriminate
        end.
    - (* Eprim_val *)
      inv H0.
    - (* Eprim *)
      inv H0.
    - (* Ehalt *)
      simpl in H1. inv H1.
      constructor.
      eapply (find_symbol_map p fenv nParam map threadInfIdent v); auto.
    - (* Fcons *)
      constructor.
    - (* Fnil *)
      constructor.
  }
  intros e stm Hnp Hcenv Htb.
  eapply HP; eauto.
Qed.

(* PROOFs on correct environments *)

(* ctor_ty_info is proper if a and ord are small enough to be represented *)
Inductive proper_ctor_ty_info: ctor_ty_info -> Prop :=
| PC_enum: forall name iname it ord,
    (0 <= (Z.of_N ord) <   Ptrofs.half_modulus)%Z ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it 0%N ord)
| PC_boxed: forall name iname it a ord,
    (* there should not be more than 2^8 - 1 boxed constructors *)
    (0 <= (Z.of_N ord) <  Zpower.two_p 8)%Z ->
    (* arity shouldn't be higher than 2^54 - 1  *)
    (0 <= Z.of_N (Npos a) <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it (Npos a)%N ord).

  
 
(* cenv is proper if ctor_ty_info is proper, and that there is a unique (ty, ord) pair for each constructors  *)
Definition proper_cenv (cenv:ctor_env):=
  forall c name iname it a ord,
    M.get c cenv = Some (Build_ctor_ty_info name iname it a ord) ->
    proper_ctor_ty_info (Build_ctor_ty_info name iname it a ord) /\
      ~ (exists c' name' iname' a', c <> c' /\
                    M.get c' cenv = Some (Build_ctor_ty_info name' iname' it a' ord)).

(* Definition proper_nenv ? *)



Theorem proper_cenv_set_none:
  forall k v m,
  proper_cenv (Maps.PTree.set k v m) ->
  M.get k m = None ->
  proper_cenv m.
Proof.
  intros; intro; intros.
  assert (c <> k). intro; subst. rewrite H1 in H0; inv H0.
  split.
  erewrite <- M.gso in H1. 2: eauto. apply H in H1. destruct H1; auto.
  intro; destructAll.  
  assert (x <> k). intro; subst. rewrite H4 in H0; inv H0.
  erewrite <- M.gso in H1.
  apply H in H1. destruct H1.
  apply H6.
  exists x, x0, x1, x2.
  split; auto.
  rewrite M.gso; auto.
  auto. 
Qed.





Theorem compute_proper_rep_env: forall cenv,
proper_cenv cenv -> 
  correct_crep_of_env cenv (compute_rep_env cenv).
Proof.
  intros. split; intros.
  - unfold compute_rep_env. rewrite M.gmap.
    unfold fmake_ctor_rep. rewrite H0.
    simpl.
    specialize (H _ _ _ _ _ _ H0). destructAll.
    destruct a.
    + eexists; split; auto. rewrite N.eqb_refl.  inv H. econstructor; eauto.
    + eexists; split; auto. assert (N.pos p <> 0%N). intro Hp; inv Hp. rewrite <- N.eqb_neq in H2.  rewrite H2. inv H. econstructor; eauto.
  - unfold compute_rep_env in H0.    
    rewrite M.gmap in H0.
    unfold fmake_ctor_rep in H0.
    destruct (M.get c cenv) eqn:Hccenv. 2: inv H0.
    destruct c0. simpl in H0.
    specialize (H _ _ _ _ _ _ Hccenv). destruct H.
    destruct ctor_arity.
    + rewrite N.eqb_refl in H0.  inv H0. inv H. econstructor; eauto.
    + assert (N.pos p <> 0%N). intro Hp; inv Hp. rewrite <- N.eqb_neq in H2.  rewrite H2 in H0. inv H0. inv H. econstructor; eauto.
Qed.


  Theorem compute_dc_ienv:
  forall cenv, 
    (fun cenv ienv => proper_cenv cenv ->
                      domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
  intro cenv.
  eapply Maps.PTree_Properties.fold_rec; intros.
  - assert (proper_cenv m).
    { intro; intros. rewrite H in H2. apply H1 in H2. destruct H2.
      split; auto. intro; apply H3.  destructAll. rewrite H in H5.
      exists x , x0 , x1 , x2. auto.
    }
    specialize (H0 H2). destruct H0. split.
    intro; intros. eapply H0 in H5; eauto. rewrite H in H5. auto.    
    intro; intros. rewrite <- H in H4. apply H3 in H4. auto. 
  - split; intro; intros; rewrite M.gempty in *; exfalso; inv H0. 
  - assert (proper_cenv  m) by (eapply proper_cenv_set_none; eauto).
    specialize (H1 H3). destruct H1.
    assert ( domain_ienv_cenv (Maps.PTree.set k v m) (update_ind_env a k v)).
    {
      intro; intros. destruct v. simpl in H5.
      destruct ( cps.M.get ctor_ind_tag a) eqn:Hgi0a.
      + destruct n.
        destruct (var_dec i ctor_ind_tag).
        * subst. rewrite M.gss in H5. inv H5. inv H6.
          (* k = x *)
          inv H5. eexists. apply M.gss.
          (* k <> x *)
          eapply H1 in H5; eauto. destruct H5. eexists.
          rewrite M.gso. eauto. intro; subst. rewrite H5 in H. inv H.
        * rewrite M.gso in H5 by auto.
          eapply H1 in H6; eauto. destruct H6. eexists.
          rewrite M.gso. eauto. intro; subst. rewrite H6 in H; inv H.
      + destruct (var_dec i ctor_ind_tag).
        * subst. rewrite M.gss in H5. inv H5. inv H6. inv H5. exists namei. apply M.gss. inv H5.
        * rewrite M.gso in H5 by auto. apply H1 in H5. apply H5 in H6. destruct H6.
          exists x0. rewrite M.gso. auto.  intro; subst. rewrite H in H6. inv H6.
    } split; auto.
    

      
    intro. intros.
    assert (H6' := H6).
    apply H2 in H6'. destruct H6' as [H6b H6'].
    destruct (cps_util.var_dec x k).
    + (* x = k  -> can update i and it still be proper *)
      subst. rewrite M.gss in H6. inv H6.
      simpl.  destruct (M.get i a) eqn:Hgia.
      * (* i was already in a *)
        destruct n. eexists. eexists. split.  apply M.gss.
        split. constructor. reflexivity.
        split; intro; intros; destructAll.
        inv H7. inv H8. apply H6; auto.
        eapply H1 in H8; eauto. inv H8. rewrite H7 in H; inv H.
        inv H7. inv H8. apply H6; auto.
        (* constructor shares the same ord, cannot be proper *)
        eapply H1 in H8; eauto. inv H8.
        destruct (var_dec x0 k); subst. rewrite H7 in H; inv H.
        apply H6'. exists x0. eexists. eexists. eexists.
        split; auto. rewrite M.gso by auto. eauto.
      * (* k is the first cons of i *)
        eexists. eexists. split. apply M.gss.
        split. constructor. reflexivity.
        split; intro; intros; destructAll.
        inv H7; inv H8. apply H6; auto.
        inv H7; inv H8. apply H6; auto.            
    + (* x <> k *)
      
      assert (H6'' := H6).
      rewrite M.gso in H6 by auto.
      apply H4 in H6. destructAll.
      {
        unfold update_ind_env. destruct v. 
        destruct  (cps.M.get ctor_ind_tag a) eqn:Hi0a.
        - destruct n0. 
          destruct (var_dec i ctor_ind_tag).
          + subst.
            rewrite Hi0a in H6. inv H6.
            eexists. exists  ((ctor_name, k, ctor_arity, ctor_ordinal) :: x1).
            split. rewrite M.gss; auto.
            split. constructor 2. auto.
            split. 
            * intro; intros.
              destructAll.
              inv H10.
              inv H11. apply n; auto.
              apply H8. eexists; eexists; eexists. split; eauto.
            * intro; intros.
              destructAll.
              inv H10.
              inv H11. apply H6'. eexists. eexists. eexists. eexists. split.
              apply n. rewrite M.gss. reflexivity.
              eapply H9.
              eexists. eexists. eexists. split; eauto.                          
          + exists x0, x1. rewrite M.gso; auto. 
        - exists x0, x1. rewrite M.gso. auto. intro; subst. rewrite H6 in Hi0a. inv Hi0a.
      }
Qed.



(* Note: can be proven directly *)
Corollary compute_domain_ienv:
  forall cenv, 
                    (fun cenv ienv => proper_cenv cenv -> 
                    domain_ienv_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
    assert ( forall cenv, 
           (fun cenv ienv => proper_cenv cenv ->
                              domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv)) by apply compute_dc_ienv. simpl; intros. simpl in H.  apply H in H0. destruct H0.
  auto.
Qed.


Corollary compute_correct_ienv:
  forall cenv, 
                    (fun cenv ienv => proper_cenv cenv -> 
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv).
Proof.
  assert ( forall cenv, 
           (fun cenv ienv => proper_cenv cenv ->
                              domain_ienv_cenv cenv ienv /\
                    correct_ienv_of_cenv cenv ienv) cenv (compute_ind_env cenv)) by apply compute_dc_ienv. simpl; intros. simpl in H.  apply H in H0. destruct H0.
  auto.
Qed.


Definition correct_fenv_for_function (fenv:fun_env):=
  fun f (t:fun_tag) (ys:list cps.var) (e:exp) =>
    exists n l, M.get f fenv = Some (n, l) /\
                n = N.of_nat (length l) /\
                length l = length ys /\
                    NoDup l /\
                    Forall (fun i => 0 <= (Z.of_N i) < max_args)%Z l. 

Search fun_tag. 
(* fun_tag are associated with an arity and a calling convention. 
   all functions and applications with this fun_tag have the right number of arguments *)

Definition correct_fenv (fenv:fun_env) (fds:fundefs):= Forall_fundefs (correct_fenv_for_function fenv) fds.


(* TODO: something that implies correct_fundef_info when ldefs are put in memory
Theorem make_fundef_info_correct:
  correct_fenv fenv fds ->
  make_fundef_info fds fenv nenv = Some (ldefs * finfo_env * nenv') -> 


*)
  
        




Definition program_inv (p:program) := program_isPtr_inv p /\ program_threadinfo_inv p /\ program_gc_inv p.
 
(* At the top level:
  correct_envs >
    > correct_ienv_of_cenv -> link ienv and crep
    > correct_cenv_of_env -> this is just correct_cenv_of_exp for all functions, which is to say correct_cenv_of_exp on the full initial term 
    > correct_cenv_of_exp -> see above, correct_cenv_of_exp (fds e) so correct_cenv_of_exp e
    > correct_crep_of_env -> correctness of crep
  protected_id_not_bound -> disjoint bound_var and protected_id
  unique_bindings_envs -> by unique_bindings on e
  functions_not_bound -> by unique_bindings, all bound vars in e are disjoint from functions which were added to globalenv
  rel_mem -> L can be empty since rho only has fun,
             repr_val_id for all funs
             closed_val for all funs 
             correct_fundefs_info for all funs
  correct_alloc -> just computed
  correct_tinfo ->  tinfo is initialized properly
 *)

Theorem sizeof_uval:
  forall p,
  (sizeof p uval) = int_size.
Proof.
  intro. unfold sizeof.
  chunk_red; archi_red; auto.
Qed.

Theorem sizeof_val:
  forall p,
  (sizeof p val) = int_size.
Proof.
  intro. unfold sizeof.
  chunk_red; archi_red; auto.
Qed.


Theorem ptrofs_of_int64:
  forall x, 
  Ptrofs.repr (Int64.unsigned (Int64.repr x)) = Ptrofs.repr x.
Proof.
  intro.
  symmetry.
  eapply Ptrofs.eqm_samerepr. apply Int64.eqm_unsigned_repr.
Qed.

Theorem ptrofs_of_int:
  forall x,
    Archi.ptr64 = false ->
  Ptrofs.repr (Int.unsigned (Int.repr x)) = Ptrofs.repr x.
Proof.
  intros.
  symmetry.
  eapply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm32; auto.
  apply Int.eqm_unsigned_repr.
Qed.

Theorem sem_cast_vint:
  forall n m, 
 sem_cast (make_vint n) uval uval m = Some (make_vint n).
Proof.
  intros. unfold sem_cast; chunk_red; simpl; archi_red; simpl; archi_red; auto.
Qed.


Theorem sem_notbool_val:
  forall n m,
    sem_notbool
          (Val.of_bool n) type_bool  m = Some (Val.of_bool (negb n)).
Proof.
  intros; destruct n; simpl; reflexivity.
Qed.  

Theorem eval_cint :
  forall p env lenv m z, 
 eval_expr (globalenv p) env lenv m
     (make_cint z val) (make_vint z).
Proof.
  intros.
  chunk_red; archi_red.
  constructor.
  unfold make_cint. archi_red. constructor.
Qed.

Theorem eval_cint_uval :
  forall p env lenv m z,
    eval_expr (globalenv p) env lenv m
      (LambdaANF_to_Clight.make_cint z LambdaANF_to_Clight.uval) (make_vint z).
Proof.
  intros.
  chunk_red; archi_red.
  constructor.
  unfold LambdaANF_to_Clight.make_cint, LambdaANF_to_Clight.uval.
  archi_red. constructor.
Qed.

Fixpoint mk_gc_call_lenv (p:program) (ys vs : list positive) (lenv_old lenv : temp_env) : temp_env :=
  match ys, vs with
  | nil, _ => lenv
  | _, nil => lenv
  | a :: ys', v :: vs' =>
    let val := match Genv.find_symbol (Genv.globalenv p) a with
               | Some b => Vptr b (Ptrofs.repr 0)
               | None => match M.get a lenv_old with
                         | Some w => w
                         | None => Vundef
                         end
               end in
    M.set v val (mk_gc_call_lenv p ys' vs' lenv_old lenv)
  end.

Theorem mk_gc_call_lenv_correct : forall (p:program) (ys vs : list positive) (lenv_old lenv : temp_env),
    Forall (fun x => exists v, get_var_or_funvar p lenv_old x v) ys ->
    length ys = length vs ->
    NoDup vs ->
    (forall x, List.In x vs -> Genv.find_symbol (Genv.globalenv p) x = None) ->
    Forall (fun x => exists v, get_var_or_funvar p (mk_gc_call_lenv p ys vs lenv_old lenv) x v) vs.
Proof.
  intros p. induction ys; intros vs lenv_old lenv Hys Hlen Hnd Hvs_sym;
    destruct vs; try (inv Hlen; fail); try constructor.
  - (* head: p0 *)
    simpl.
    destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:Hfs_a.
    + (* a is a function symbol *)
      exists (Vptr b (Ptrofs.repr 0)).
      constructor 2.
      * apply Hvs_sym. left; reflexivity.
      * rewrite M.gss. reflexivity.
      * auto.
    + (* a is not a function symbol *)
      destruct (M.get a lenv_old) eqn:Hget_a.
      * exists v.
        constructor 2.
        -- apply Hvs_sym. left; reflexivity.
        -- rewrite M.gss. reflexivity.
        -- inv Hys. destruct H1 as [v' Hv']. inv Hv'.
           { rewrite Hfs_a in H. inv H. }
           { rewrite Hget_a in H0. inv H0. auto. }
      * exfalso.
        inv Hys. destruct H1 as [v' Hv']. inv Hv'.
        { rewrite Hfs_a in H. inv H. }
        { rewrite Hget_a in H0. inv H0. }
  - (* tail: Forall for vs *)
    inv Hnd. inv Hys.
    assert (IH_result : Forall (fun x => exists v, get_var_or_funvar p (mk_gc_call_lenv p ys vs lenv_old lenv) x v) vs).
    { apply IHys; auto. intros; apply Hvs_sym; right; auto. }
    simpl.
    destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:Hfs_a;
      [ | destruct (M.get a lenv_old) eqn:Hget_a ];
      (apply Forall_forall; intros x Hx_in;
       assert (Hx_ne : x <> p0) by (intro; subst; auto);
       rewrite Forall_forall in IH_result;
       destruct (IH_result x Hx_in) as [v' Hv'];
       exists v'; inv Hv';
       [ constructor; auto
       | constructor 2; auto; rewrite M.gso; auto ]).
Qed.

Ltac unsigned_ptrofs_range :=
  split; [apply Ptrofs.unsigned_range |  etransitivity;  [apply Ptrofs.unsigned_range_2 | rewrite ptrofs_mu; archi_red; reflexivity] ].


Theorem type_of_mkFunTyList:
  forall nParam vsm4, 
  (mkFunTyList
     (Init.Nat.min (length vsm4)
             nParam)) = (type_of_params (map (fun x : ident => (x, uval))
                                              (firstn nParam vsm4))).
Proof.
  induction nParam0; intros; simpl.
  -  rewrite Nat.min_0_r.
     reflexivity.
  - destruct vsm4.
    + (* empty list *)
      reflexivity.
    + simpl. erewrite IHnParam0. reflexivity.
Qed.

Lemma same_args_ptr_refl :
  forall lenv, same_args_ptr lenv lenv.
Proof.
  reflexivity.
Qed.

Lemma same_args_ptr_trans :
  forall lenv1 lenv2 lenv3,
    same_args_ptr lenv1 lenv2 ->
    same_args_ptr lenv2 lenv3 ->
    same_args_ptr lenv1 lenv3.
Proof.
  intros lenv1 lenv2 lenv3 H12 H23.
  unfold same_args_ptr in *.
  congruence.
Qed.

Lemma same_args_ptr_sym :
  forall lenv1 lenv2,
    same_args_ptr lenv1 lenv2 ->
    same_args_ptr lenv2 lenv1.
Proof.
  intros lenv1 lenv2 H12.
  unfold same_args_ptr in *.
  symmetry.
  exact H12.
Qed.

Lemma same_args_ptr_set_left_other :
  forall lenv1 lenv2 x v,
    x <> argsIdent ->
    same_args_ptr lenv1 lenv2 ->
    same_args_ptr (M.set x v lenv1) lenv2.
Proof.
  intros lenv1 lenv2 x v Hneq Hsame.
  unfold same_args_ptr in *.
  rewrite M.gso by (symmetry; exact Hneq).
  exact Hsame.
Qed.

Lemma same_args_ptr_set_right_other :
  forall lenv1 lenv2 x v,
    x <> argsIdent ->
    same_args_ptr lenv1 lenv2 ->
    same_args_ptr lenv1 (M.set x v lenv2).
Proof.
  intros lenv1 lenv2 x v Hneq Hsame.
  unfold same_args_ptr in *.
  rewrite M.gso by (symmetry; exact Hneq).
  exact Hsame.
Qed.

Lemma same_args_ptr_set_both_args :
  forall lenv1 lenv2 v,
    same_args_ptr (M.set argsIdent v lenv1) (M.set argsIdent v lenv2).
Proof.
  intros lenv1 lenv2 v.
  unfold same_args_ptr.
  rewrite M.gss.
  rewrite M.gss.
  reflexivity.
Qed.

Lemma same_args_ptr_set_left_args_from_get :
  forall lenv1 lenv2 v,
    M.get argsIdent lenv2 = Some v ->
    same_args_ptr (M.set argsIdent v lenv1) lenv2.
Proof.
  intros lenv1 lenv2 v Hget.
  unfold same_args_ptr.
  rewrite M.gss.
  symmetry.
  exact Hget.
Qed.

Lemma same_args_ptr_set_right_args_from_get :
  forall lenv1 lenv2 v,
    M.get argsIdent lenv1 = Some v ->
    same_args_ptr lenv1 (M.set argsIdent v lenv2).
Proof.
  intros lenv1 lenv2 v Hget.
  unfold same_args_ptr.
  rewrite M.gss.
  exact Hget.
Qed.

Lemma same_args_ptr_get_right :
  forall lenv1 lenv2 v,
    same_args_ptr lenv1 lenv2 ->
    M.get argsIdent lenv1 = Some v ->
    M.get argsIdent lenv2 = Some v.
Proof.
  intros lenv1 lenv2 v Hsame Hget.
  unfold same_args_ptr in Hsame.
  rewrite <- Hsame.
  exact Hget.
Qed.

Lemma same_args_ptr_get_left :
  forall lenv1 lenv2 v,
    same_args_ptr lenv1 lenv2 ->
    M.get argsIdent lenv2 = Some v ->
    M.get argsIdent lenv1 = Some v.
Proof.
  intros lenv1 lenv2 v Hsame Hget.
  unfold same_args_ptr in Hsame.
  rewrite Hsame.
  exact Hget.
Qed.

Lemma rel_mem_has_args_ptr :
  forall fenv finfo_env p rep_env e rho m lenv,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    exists args_b args_ofs, M.get argsIdent lenv = Some (Vptr args_b args_ofs).
Proof.
  intros fenv finfo_env p rep_env e rho m lenv Hrel.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [Hprot _]].
  unfold protected_not_in_L in Hprot.
  destruct Hprot as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs Hprot]]]]]]].
  destruct Hprot as [Halloc Hprot].
  destruct Hprot as [_ Hprot].
  destruct Hprot as [_ Hprot].
  destruct Hprot as [Hargs _].
  exists args_b, args_ofs.
  exact Hargs.
Qed.

Lemma arg_val_has_args_ptr :
  forall fenv finfo_env p rep_env v m lenv,
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv ->
    exists args_b args_ofs, M.get argsIdent lenv = Some (Vptr args_b args_ofs).
Proof.
  intros fenv finfo_env p rep_env v m lenv Harg.
  destruct Harg as [args_b [args_ofs [Codegenv [L [Hargs _]]]]].
  exists args_b, args_ofs.
  exact Hargs.
Qed.

Lemma arg_val_intro :
  forall fenv finfo_env p rep_env v m lenv args_b args_ofs Codegenv L,
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    Mem.load int_chunk m args_b
      (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) = Some Codegenv ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L Codegenv ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv.
Proof.
  intros fenv finfo_env p rep_env v m lenv args_b args_ofs Codegenv L Hargs Hload Hrepr.
  exists args_b, args_ofs, Codegenv, L.
  repeat split; assumption.
Qed.

Lemma arg_val_load_repr :
  forall fenv finfo_env p rep_env v m lenv,
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv ->
    exists args_b args_ofs Codegenv L,
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      Mem.load int_chunk m args_b
        (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) = Some Codegenv /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L Codegenv.
Proof.
  intros fenv finfo_env p rep_env v m lenv Harg.
  destruct Harg as [args_b [args_ofs [Codegenv [L [Hargs [Hload Hrepr]]]]]].
  exists args_b, args_ofs, Codegenv, L.
  repeat split; assumption.
Qed.

Lemma arg_val_same_args_ptr_left :
  forall fenv finfo_env p rep_env v m lenv lenv',
    same_args_ptr lenv lenv' ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv' ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv.
Proof.
  intros fenv finfo_env p rep_env v m lenv lenv' Hsame Harg.
  destruct Harg as [args_b [args_ofs [Codegenv [L [Hargs [Hload Hrepr]]]]]].
  exists args_b, args_ofs, Codegenv, L.
  split.
  - eapply same_args_ptr_get_left; eauto.
  - split; assumption.
Qed.

Lemma arg_val_same_args_ptr_right :
  forall fenv finfo_env p rep_env v m lenv lenv',
    same_args_ptr lenv lenv' ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv'.
Proof.
  intros fenv finfo_env p rep_env v m lenv lenv' Hsame Harg.
  destruct Harg as [args_b [args_ofs [Codegenv [L [Hargs [Hload Hrepr]]]]]].
  exists args_b, args_ofs, Codegenv, L.
  split.
  - eapply same_args_ptr_get_right; eauto.
  - split; assumption.
Qed.

Lemma arg_val_same_args_ptr_iff :
  forall fenv finfo_env p rep_env v m lenv lenv',
    same_args_ptr lenv lenv' ->
    (arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv <->
     arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m lenv').
Proof.
  intros fenv finfo_env p rep_env v m lenv lenv' Hsame.
  split.
  - apply arg_val_same_args_ptr_right; assumption.
  - apply arg_val_same_args_ptr_left; assumption.
Qed.

Lemma compose_prefix_body_result :
  forall fenv finfo_env p rep_env v fu stm s k lenv lenv_mid m,
    m_tstep2 (globalenv p)
      (State fu stm k empty_env lenv m)
      (State fu s k empty_env lenv_mid m) ->
    same_args_ptr lenv lenv_mid ->
    (exists m' lenv',
       m_tstep2 (globalenv p)
         (State fu s k empty_env lenv_mid m)
         (State fu Sskip k empty_env lenv' m') /\
       same_args_ptr lenv_mid lenv' /\
       arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv') ->
    exists m' lenv',
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu Sskip k empty_env lenv' m') /\
      same_args_ptr lenv lenv' /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros fenv finfo_env p rep_env v fu stm s k lenv lenv_mid m
    Hpref Hsame_pref Hbody.
  destruct Hbody as [m' [lenv' [Hbody_step [Hsame_body Harg]]]].
  exists m', lenv'.
  split.
  - eapply m_tstep2_transitive; eauto.
  - split.
    + eapply same_args_ptr_trans; eauto.
    + exact Harg.
Qed.

Lemma compose_prefix_body_result_gen :
  forall fenv finfo_env p rep_env v fu stm s k lenv lenv_mid m m_mid,
    m_tstep2 (globalenv p)
      (State fu stm k empty_env lenv m)
      (State fu s k empty_env lenv_mid m_mid) ->
    same_args_ptr lenv lenv_mid ->
    (exists m' lenv',
       m_tstep2 (globalenv p)
         (State fu s k empty_env lenv_mid m_mid)
         (State fu Sskip k empty_env lenv' m') /\
       same_args_ptr lenv_mid lenv' /\
       arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv') ->
    exists m' lenv',
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu Sskip k empty_env lenv' m') /\
      same_args_ptr lenv lenv' /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros fenv finfo_env p rep_env v fu stm s k lenv lenv_mid m m_mid
    Hpref Hsame_pref Hbody.
  destruct Hbody as [m' [lenv' [Hbody_step [Hsame_body Harg]]]].
  exists m', lenv'.
  split.
  - eapply m_tstep2_transitive; eauto.
  - split.
    + eapply same_args_ptr_trans; eauto.
    + exact Harg.
Qed.

Lemma rel_mem_occurs_free_get :
  forall fenv finfo_env p rep_env e rho m lenv x,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    occurs_free e x ->
    exists v6, M.get x rho = Some v6.
Proof.
  intros fenv finfo_env p rep_env e rho m lenv x Hrel Hfree.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [_ Hrel]].
  specialize (Hrel x) as [Hocc _].
  apply Hocc in Hfree.
  destruct Hfree as [v6 [Hget _]].
  exists v6.
  exact Hget.
Qed.

Lemma rel_mem_same_args_ptr_has_args_ptr :
  forall fenv finfo_env p rep_env e rho m lenv lenv',
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    same_args_ptr lenv lenv' ->
    exists args_b args_ofs, M.get argsIdent lenv' = Some (Vptr args_b args_ofs).
Proof.
  intros fenv finfo_env p rep_env e rho m lenv lenv' Hrel Hsame.
  destruct (rel_mem_has_args_ptr _ _ _ _ _ _ _ _ Hrel) as [args_b [args_ofs Hget]].
  exists args_b, args_ofs.
  eapply same_args_ptr_get_right; eauto.
Qed.

Lemma rel_mem_occurs_free_repr :
  forall fenv finfo_env p rep_env e rho m lenv x,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    occurs_free e x ->
    exists v6 L,
      protected_not_in_L_id p lenv L /\
      M.get x rho = Some v6 /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v6 m L lenv x.
Proof.
  intros fenv finfo_env p rep_env e rho m lenv x Hrel Hfree.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [Hprot Hrel]].
  specialize (Hrel x) as [Hocc _].
  apply Hocc in Hfree.
  destruct Hfree as [v6 [Hget Hrepr]].
  exists v6, L.
  split.
  - exact Hprot.
  - split; assumption.
Qed.

Lemma rel_mem_set_protected_id :
  forall fenv finfo_env p rep_env e rho m lenv x vx,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    protected_id_not_bound_id rho e ->
    is_protected_id_thm x ->
    ~ is_protected_tinfo_id_thm x ->
    x <> tinfIdent ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m
      (M.set x vx lenv).
Proof.
  intros fenv finfo_env p rep_env e rho m lenv x vx Hrel Hprot Hxprot Hxtinfo Hxneq.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [HpinL Hmem]].
  exists L.
  split.
  { eapply protected_not_in_L_set.
    - exact HpinL.
    - exact Hxtinfo.
    - exact Hxneq. }
  { intros y.
    specialize (Hmem y) as [Hocc Hfun].
    split.
    + intros Hyfree.
      specialize (Hocc Hyfree) as [v6 [Hyget Hrepr]].
      exists v6.
      split; [exact Hyget|].
      eapply repr_val_id_set; [exact Hrepr|].
      intro Hyx.
      destruct Hprot as [Hrho _].
      specialize (Hrho y x v6 Hyget Hxprot) as Hn.
      apply Hn.
      left.
      exact Hyx.
    + intros rho' fds f v Hyget Hsub.
      specialize (Hfun _ _ _ _ Hyget Hsub)
        as [Hrepr_f [Hclosed_f Hinfo_f]].
      split.
      * eapply repr_val_id_set; [exact Hrepr_f|].
        intro Hfx.
        subst x.
        destruct Hprot as [Hrho _].
        specialize (Hrho y f v Hyget Hxprot) as Hn.
        apply Hn.
        right.
        eapply bound_var_subval; [|exact Hsub].
        destruct Hinfo_f as [finfo [t [t' [vs [e0 [Hfind _]]]]]].
        constructor.
        eapply name_in_fundefs_bound_var_fundefs.
        eapply find_def_name_in_fundefs; eauto.
      * split; [exact Hclosed_f|exact Hinfo_f].
  }
Qed.

Lemma rel_mem_fun_subval_info :
  forall fenv finfo_env p rep_env e rho m lenv x rho' fds f v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    M.get x rho = Some v ->
    subval_or_eq (Vfun rho' fds f) v ->
    exists L,
      protected_not_in_L_id p lenv L /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vfun rho' fds f) m L lenv f /\
      closed_val (Vfun rho' fds f) /\
      correct_fundef_id_info fenv finfo_env p m fds f.
Proof.
  intros fenv finfo_env p rep_env e rho m lenv x rho' fds f v Hrel Hget Hsub.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [Hprot Hrel]].
  specialize (Hrel x) as [_ Hfun].
  specialize (Hfun rho' fds f v Hget Hsub) as [Hrepr [Hclosed Hinfo]].
  exists L.
  split.
  - unfold protected_not_in_L_id.
    exact Hprot.
  - split.
    + exact Hrepr.
    + split; assumption.
Qed.

Lemma rel_mem_fun_get_info :
  forall fenv finfo_env p rep_env e rho m lenv x rho' fds f,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    M.get x rho = Some (Vfun rho' fds f) ->
    exists L,
      protected_not_in_L_id p lenv L /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vfun rho' fds f) m L lenv f /\
      closed_val (Vfun rho' fds f) /\
      correct_fundef_id_info fenv finfo_env p m fds f.
Proof.
  intros fenv finfo_env p rep_env e rho m lenv x rho' fds f Hrel Hget.
  eapply rel_mem_fun_subval_info; eauto.
  unfold subval_or_eq.
  apply rt_refl.
Qed.

Lemma repr_expr_efun_false :
  forall fenv finfo_env p rep_env fds e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Efun fds e) stm ->
    False.
Proof.
  intros fenv finfo_env p rep_env fds e stm Hrepr.
  inversion Hrepr.
Qed.

Lemma repr_expr_eprim_val_false :
  forall fenv finfo_env p rep_env x p0 e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim_val x p0 e) stm ->
    False.
Proof.
  intros fenv finfo_env p rep_env x p0 e stm Hrepr.
  inversion Hrepr.
Qed.

Lemma repr_expr_eprim_false :
  forall fenv finfo_env p rep_env x f ys e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim x f ys e) stm ->
    False.
Proof.
  intros fenv finfo_env p rep_env x f ys e stm Hrepr.
  inversion Hrepr.
Qed.

Lemma repr_expr_econstr_inv :
  forall fenv finfo_env p rep_env x t ys e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
    exists s s',
      repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env
        x t ys s /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s s'.
Proof.
  intros fenv finfo_env p rep_env x t ys e stm Hrepr.
  inversion Hrepr; subst.
  exists s, s'.
  repeat split; assumption.
Qed.

Lemma repr_expr_eproj_inv :
  forall fenv finfo_env p rep_env x t n y e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    exists s,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof.
  intros fenv finfo_env p rep_env x t n y e stm Hrepr.
  inversion Hrepr; subst.
  eauto.
Qed.

Lemma repr_expr_eapp_inv :
  forall fenv finfo_env p rep_env f t ys stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) stm ->
    exists s_pref s_tail,
      stm = Ssequence s_pref s_tail.
Proof.
  intros fenv finfo_env p rep_env f t ys stm Hrepr.
  inversion Hrepr; subst.
  eexists; eexists.
  reflexivity.
Qed.

Lemma repr_asgn_fun_inv :
  forall fenv finfo_env p ys inf s,
    repr_asgn_fun argsIdent threadInfIdent tinfIdent nParam fenv finfo_env p ys inf s ->
    exists s_inner,
      repr_asgn_fun' argsIdent threadInfIdent nParam fenv finfo_env p ys inf s_inner.
Proof.
  intros fenv finfo_env p ys inf s Hasgn.
  inversion Hasgn; subst.
  eauto.
Qed.

Lemma repr_expr_eapp_full_inv :
  forall fenv finfo_env p rep_env f t ys stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) stm ->
    exists s_pref s_tail,
      stm = Ssequence s_pref s_tail.
Proof.
  intros fenv finfo_env p rep_env f t ys stm Hrepr.
  eapply repr_expr_eapp_inv; eauto.
Qed.


Lemma repr_expr_eletapp_inv :
  forall fenv finfo_env p rep_env x f t ys e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    exists s' s_pref,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s_pref s'.
Proof.
  intros fenv finfo_env p rep_env x f t ys e stm Hrepr.
  inversion Hrepr; subst.
  eexists; eexists.
  split; eauto.
Qed.

Lemma repr_expr_eletapp_full_inv :
  forall fenv finfo_env p rep_env x f t ys e stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    exists s_body,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s_body.
Proof.
  intros fenv finfo_env p rep_env x f t ys e stm Hrepr.
  destruct (repr_expr_eletapp_inv _ _ _ _ _ _ _ _ _ _ Hrepr)
    as [s_body [s_pref [Hrepr_e Hstm]]].
  exists s_body.
  exact Hrepr_e.
Qed.

Lemma repr_expr_ehalt_inv :
  forall fenv finfo_env p rep_env x stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    exists e,
      var_or_funvar threadInfIdent nParam fenv finfo_env p x e.
Proof.
  intros fenv finfo_env p rep_env x stm Hrepr.
  inversion Hrepr; subst.
  eauto.
Qed.

Lemma repr_expr_ecase_inv :
  forall fenv finfo_env p rep_env y cl stm,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    exists ls ls',
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm.
Proof.
  intros fenv finfo_env p rep_env y cl stm Hrepr.
  inversion Hrepr; subst.
  eauto.
Qed.

Lemma protected_id_not_bound_subterm :
  forall rho e e',
    protected_id_not_bound_id rho e ->
    subterm_e e' e ->
    protected_id_not_bound_id rho e'.
Proof.
  intros rho e e' Hprot Hsub.
  destruct Hprot as [Hrho Hexp].
  split.
  - exact Hrho.
  - intros y Hy Hbv.
    eapply Hexp; eauto.
    eapply bound_var_subterm_e; eauto.
Qed.

Lemma unique_bindings_env_set :
  forall rho e x v,
    unique_bindings_env rho e ->
    ~ bound_var e x ->
    unique_bindings_val v ->
    unique_bindings_env (M.set x v rho) e.
Proof.
  intros rho e x v Hub_env Hx_not_bound Huv.
  destruct Hub_env as [Hub Henv].
  split.
  - exact Hub.
  - intros y vy Hget.
    destruct (var_dec y x).
    + subst.
      rewrite M.gss in Hget.
      inversion Hget; subst.
      split; assumption.
    + rewrite M.gso in Hget by assumption.
      specialize (Henv _ _ Hget) as [Hnb Huvy].
      split; assumption.
Qed.

Lemma protected_id_not_bound_set :
  forall rho e x v,
    protected_id_not_bound_id rho e ->
    ~ is_protected_id_thm x ->
    (forall y, is_protected_id_thm y -> ~ bound_var_val v y) ->
    protected_id_not_bound_id (M.set x v rho) e.
Proof.
  intros rho e x v Hprot Hx_prot Hvb.
  destruct Hprot as [Hrho Hexp].
  split.
  - intros x0 y v0 Hget Hy.
    destruct (var_dec x0 x).
    + subst.
      rewrite M.gss in Hget.
      inversion Hget; subst.
      intro Hor.
      destruct Hor as [Heq | Hbound].
      * subst. contradiction.
      * eapply Hvb; eauto.
    + rewrite M.gso in Hget by assumption.
      eapply Hrho; eauto.
  - exact Hexp.
Qed.

Lemma protected_id_not_bound_econstr_head :
  forall rho x t ys e,
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    ~ is_protected_id_thm x.
Proof.
  intros rho x t ys e Hprot Hx.
  destruct Hprot as [_ Hexp].
  eapply Hexp; eauto.
Qed.

Lemma protected_id_not_bound_eproj_head :
  forall rho x t n y e,
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    ~ is_protected_id_thm x.
Proof.
  intros rho x t n y e Hprot Hx.
  destruct Hprot as [_ Hexp].
  eapply Hexp; eauto.
Qed.

Lemma protected_id_not_bound_eletapp_head :
  forall rho x f t ys e,
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    ~ is_protected_id_thm x.
Proof.
  intros rho x f t ys e Hprot Hx.
  destruct Hprot as [_ Hexp].
  eapply Hexp; eauto.
Qed.

Lemma functions_not_bound_set_constr :
  forall p rho e x t ys vs,
    functions_not_bound p rho e ->
    get_list ys rho = Some vs ->
    functions_not_bound p (M.set x (Vconstr t vs) rho) e.
Proof.
  intros p rho e x t ys vs Hfnb Hgl.
  eapply functions_not_bound_set; [exact Hfnb |].
  intros z Hb.
  inversion Hb; subst.
  match goal with
  | Hbn : bound_notfun_val ?v z, Hin : List.In ?v vs |- _ =>
      destruct (get_list_In_val _ _ _ _ Hgl Hin) as [y [Hyin Hgety]];
      destruct Hfnb as [_ Hrho];
      eapply Hrho; eauto
  end.
Qed.

Lemma nthN_in :
  forall {A} (ls : list A) n x,
    nthN ls n = Some x ->
    List.In x ls.
Proof.
  induction ls as [|a ls IH]; intros n x Hnth.
  - destruct n; inversion Hnth.
  - destruct n.
    + simpl in Hnth. inversion Hnth; subst. left; reflexivity.
    + simpl in Hnth. right. eapply IH; eauto.
Qed.

Lemma get_list_forall_from_env :
  forall {A} (rho : M.t A) (ys : list var) (vs : list A) (P : A -> Prop),
    get_list ys rho = Some vs ->
    (forall x v, M.get x rho = Some v -> P v) ->
    Forall P vs.
Proof.
  intros A rho ys.
  induction ys as [|y ys IH]; intros vs P Hgl Henv.
  - simpl in Hgl. inversion Hgl; subst. constructor.
  - simpl in Hgl.
    destruct (M.get y rho) as [vy|] eqn:Hgy; try discriminate.
    destruct (get_list ys rho) as [vst|] eqn:Hgst; try discriminate.
    inversion Hgl; subst.
    constructor.
    + eapply Henv; eauto.
    + eapply IH; eauto.
Qed.

Lemma get_list_length :
  forall {A} (rho : M.t A) ys (vs : list A),
    get_list ys rho = Some vs ->
    length ys = length vs.
Proof.
  intros A rho ys.
  induction ys as [|y ys IH]; intros vs Hgl.
  - simpl in Hgl. inversion Hgl; reflexivity.
  - simpl in Hgl.
    destruct (M.get y rho) as [vy|] eqn:Hgy; try discriminate.
    destruct (get_list ys rho) as [vst|] eqn:Hgst; try discriminate.
    inversion Hgl; subst.
    simpl. f_equal. eapply IH; eauto.
Qed.

Lemma Forall_fundefs_find_def :
  forall P f t xs e fds,
    Forall_fundefs P fds ->
    find_def f fds = Some (t, xs, e) ->
    P f t xs e.
Proof.
  intros P f t xs e fds Hforall.
  induction Hforall
    as [P0 f0 t0 xs0 e0 fds0 Hhead Htail IH | P0];
    intros Hfind.
  - simpl in Hfind.
    destruct (cps.M.elt_eq f f0).
    + inversion Hfind; subst.
      assumption.
    + eapply IH; eauto.
  - inversion Hfind.
Qed.

Lemma correct_cenv_of_exp_find_def_from_env :
  forall cenv rho f rho_clo fl f' t xs e,
    correct_cenv_of_env cenv rho ->
    M.get f rho = Some (Vfun rho_clo fl f') ->
    find_def f' fl = Some (t, xs, e) ->
    correct_cenv_of_exp cenv e.
Proof.
  intros cenv rho f rho_clo fl f' t xs e Hcenv Hgetf Hfind.
  specialize (Hcenv _ _ Hgetf) as Hcv_fun.
  inversion Hcv_fun; subst.
  match goal with
  | Hfds : Forall_fundefs (fun _ _ _ e0 => correct_cenv_of_exp cenv e0) ?fds0 |- _ =>
      eapply (Forall_fundefs_find_def
                (fun _ _ _ e0 => correct_cenv_of_exp cenv e0)
                f' t xs e fds0);
      [exact Hfds | exact Hfind]
  end.
Qed.

Lemma unique_bindings_val_nth_constr :
  forall t vs n v,
    unique_bindings_val (Vconstr t vs) ->
    nthN vs n = Some v ->
    unique_bindings_val v.
Proof.
  intros t vs n v Huv Hnth.
  inversion Huv; subst.
  apply Forall_forall with (x := v) in H0.
  - exact H0.
  - eapply nthN_in; eauto.
Qed.

Lemma correct_cenv_of_val_nth_constr :
  forall cenv t vs n v,
    correct_cenv_of_val cenv (Vconstr t vs) ->
    nthN vs n = Some v ->
    correct_cenv_of_val cenv v.
Proof.
  intros cenv t vs n v Hcv Hnth.
  inversion Hcv; subst.
  match goal with
  | Hfor : Forall (correct_cenv_of_val cenv) vs |- _ =>
      apply Forall_forall with (x := v) in Hfor;
      [exact Hfor | eapply nthN_in; eauto]
  end.
Qed.

Lemma unique_bindings_env_econstr_body_set :
  forall rho x t ys e vs,
    unique_bindings_env rho (Econstr x t ys e) ->
    get_list ys rho = Some vs ->
    unique_bindings_env (M.set x (Vconstr t vs) rho) e.
Proof.
  intros rho x t ys e vs Hub_env Hgl.
  destruct Hub_env as [Hub Henv].
  inversion Hub; subst.
  assert (Hub_e : unique_bindings e).
  { match goal with
    | H : unique_bindings e |- _ => exact H
    end. }
  assert (Hx_not_bound : ~ bound_var e x).
  { match goal with
    | H : ~ bound_var e x |- _ => exact H
    end. }
  assert (Hfor_vs : Forall unique_bindings_val vs).
  {
    eapply get_list_forall_from_env; eauto.
    intros y v Hy.
    destruct (Henv y v Hy) as [_ Huv].
    exact Huv.
  }
  assert (Huv_constr : unique_bindings_val (Vconstr t vs)).
  { constructor; exact Hfor_vs. }
  assert (Hub_env_e : unique_bindings_env rho e).
  {
    split.
    - exact Hub_e.
    - intros y v Hy.
      destruct (Henv y v Hy) as [Hnb Huv].
      split.
      + intro Hbv.
        apply Hnb.
        eapply bound_var_subterm_e; eauto.
        constructor. constructor.
      + exact Huv.
  }
  eapply unique_bindings_env_set; eauto.
Qed.

Lemma protected_id_not_bound_econstr_body_set :
  forall rho x t ys e vs,
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    get_list ys rho = Some vs ->
    protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e.
Proof.
  intros rho x t ys e vs Hprot Hgl.
  assert (Hprot_e : protected_id_not_bound_id rho e).
  {
    eapply protected_id_not_bound_subterm; eauto.
    constructor. constructor.
  }
  eapply protected_id_not_bound_set.
  - exact Hprot_e.
  - eapply protected_id_not_bound_econstr_head; eauto.
  - intros y Hy Hbv.
    inversion Hbv; subst.
    match goal with
    | Hin : List.In ?v vs |- _ =>
        destruct (get_list_In_val _ _ _ _ Hgl Hin) as [z [Hzin Hgetz]]
    end.
    destruct Hprot as [Hrho _].
    specialize (Hrho z y v Hgetz Hy).
    tauto.
Qed.

Lemma unique_bindings_env_eproj_body_set :
  forall rho x t n y e vs v,
    unique_bindings_env rho (Eproj x t n y e) ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    unique_bindings_env (M.set x v rho) e.
Proof.
  intros rho x t n y e vs v Hub_env Hy Hnth.
  destruct Hub_env as [Hub Henv].
  inversion Hub; subst.
  assert (Hub_e : unique_bindings e).
  { match goal with
    | H : unique_bindings e |- _ => exact H
    end. }
  assert (Hx_not_bound : ~ bound_var e x).
  { match goal with
    | H : ~ bound_var e x |- _ => exact H
    end. }
  assert (Hub_env_e : unique_bindings_env rho e).
  {
    split.
    - exact Hub_e.
    - intros z vz Hz.
      destruct (Henv z vz Hz) as [Hnb Huv].
      split.
      + intro Hbv.
        apply Hnb.
        eapply bound_var_subterm_e; eauto.
        constructor. constructor.
      + exact Huv.
  }
  assert (Huv_v : unique_bindings_val v).
  {
    destruct (Henv y (Vconstr t vs) Hy) as [_ Huvy].
    eapply unique_bindings_val_nth_constr; eauto.
  }
  eapply unique_bindings_env_set; eauto.
Qed.

Lemma protected_id_not_bound_eproj_body_set :
  forall rho x t n y e vs v,
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    protected_id_not_bound_id (M.set x v rho) e.
Proof.
  intros rho x t n y e vs v Hprot Hy Hnth.
  assert (Hprot_e : protected_id_not_bound_id rho e).
  {
    eapply protected_id_not_bound_subterm; eauto.
    constructor. constructor.
  }
  eapply protected_id_not_bound_set.
  - exact Hprot_e.
  - eapply protected_id_not_bound_eproj_head; eauto.
  - intros z Hz Hbv.
    assert (Hbv_constr : bound_var_val (Vconstr t vs) z).
    {
      eapply Bound_Vconstr.
      - exact Hbv.
      - eapply nthN_in; eauto.
    }
    destruct Hprot as [Hrho _].
    specialize (Hrho y z (Vconstr t vs) Hy Hz).
    tauto.
Qed.

Lemma correct_envs_eproj_body_set :
  forall cenv ienv rep_env rho x t n y e vs v,
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    correct_envs cenv ienv rep_env (M.set x v rho) e.
Proof.
  intros cenv ienv rep_env rho x t n y e vs v Hcenvs Hy Hnth.
  assert (Hcenvs_e : correct_envs cenv ienv rep_env rho e).
  { eapply correct_envs_subterm; eauto.
    constructor. constructor. }
  destruct Hcenvs as [_ [Hcenv_rho _]].
  assert (Hcv_constr : correct_cenv_of_val cenv (Vconstr t vs)).
  { eapply Hcenv_rho; eauto. }
  assert (Hcv_v : correct_cenv_of_val cenv v).
  { eapply correct_cenv_of_val_nth_constr; eauto. }
  eapply correct_envs_set; [exact Hcenvs_e| exact Hcv_v].
Qed.

Lemma correct_envs_econstr_body_set :
  forall cenv ienv rep_env rho x t ys e vs,
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    get_list ys rho = Some vs ->
    correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e.
Proof.
  intros cenv ienv rep_env rho x t ys e vs Hcenvs Hgl.
  assert (Hcenvs_e : correct_envs cenv ienv rep_env rho e) by
      (eapply correct_envs_subterm; eauto; constructor; constructor).
  destruct Hcenvs as [_ [Hcenv_rho [Hcenv_exp _]]].
  assert (Hfor_vs : Forall (correct_cenv_of_val cenv) vs) by
      (eapply get_list_forall_from_env; [exact Hgl|];
       intros y v Hy; eapply Hcenv_rho; eauto).
  assert (Hct :
    match M.get t cenv with
    | Some (Build_ctor_ty_info _ _ _ a _) => N.of_nat (length ys) = a
    | None => False
    end).
  {
    unfold correct_cenv_of_exp in Hcenv_exp.
    eapply (Forall_constructors_in_constr
              (fun _ t0 ys0 =>
                 match M.get t0 cenv with
                 | Some (Build_ctor_ty_info _ _ _ a0 _) =>
                     N.of_nat (length ys0) = a0
                 | None => False
                 end)
              x t ys e).
    exact Hcenv_exp.
  }
  destruct (M.get t cenv) as [info|] eqn:Hgt; [| contradiction].
  destruct info as [name iname it a ord].
  simpl in Hct.
  assert (Hlen : N.of_nat (length vs) = a) by
      (rewrite <- (get_list_length _ _ _ Hgl); exact Hct).
  eapply correct_envs_set; [exact Hcenvs_e|].
  econstructor; eauto.
Qed.

Lemma functions_not_bound_set_proj :
  forall p rho e x y t vs n v,
    functions_not_bound p rho e ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    functions_not_bound p (M.set x v rho) e.
Proof.
  intros p rho e x y t vs n v Hfnb Hgety Hnth.
  eapply functions_not_bound_set; [exact Hfnb |].
  intros z Hbn.
  assert (Hbn_constr : bound_notfun_val (Vconstr t vs) z).
  { eapply Bound_FVconstr; eauto.
    apply nthN_in with (n := n); exact Hnth. }
  destruct Hfnb as [_ Hrho].
  eapply Hrho; eauto.
Qed.

Lemma rel_mem_halt_get_repr :
  forall fenv finfo_env p rep_env rho m lenv x v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    exists L,
      protected_not_in_L_id p lenv L /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L lenv x.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v Hrel Hget.
  assert (Hfree : occurs_free (Ehalt x) x) by constructor.
  destruct (rel_mem_occurs_free_repr _ _ _ _ _ _ _ _ _ Hrel Hfree)
    as [v6 [L [Hprot [Hget6 Hrepr]]]].
  rewrite Hget in Hget6.
  inversion Hget6; subst.
  exists L.
  split; assumption.
Qed.

Lemma rel_mem_halt_get_var_or_funvar :
  forall fenv finfo_env p rep_env rho m lenv x v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    exists L v7,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv x v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v Hrel Hget.
  destruct (rel_mem_halt_get_repr _ _ _ _ _ _ _ _ _ Hrel Hget)
    as [L [Hprot Hrepr_id]].
  inversion Hrepr_id; subst.
  - exists L, (Vptr b Ptrofs.zero).
    split; [exact Hprot |].
    split.
    + constructor.
      exact H.
    + exact H0.
  - exists L, v7.
    split; [exact Hprot |].
    split.
    + econstructor 2; eauto.
      eapply repr_val_id_L_LambdaANF_Codegen_vint_or_vptr; eauto.
    + exact H1.
Qed.

Lemma rel_mem_eproj_get_var_or_funvar :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    M.get y rho = Some (Vconstr t vs) ->
    exists L v7,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv y v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vconstr t vs) m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs Hrel Hget.
  assert (Hfree : occurs_free (Eproj x t n y e) y).
  { constructor. }
  destruct (rel_mem_occurs_free_repr _ _ _ _ _ _ _ _ _ Hrel Hfree)
    as [v6 [L [Hprot [Hget6 Hrid]]]].
  rewrite Hget in Hget6.
  inversion Hget6; subst.
  inversion Hrid; subst; clear Hrid; try solve [inversion H].
  exists L, v7.
  split; [exact Hprot |].
  split.
  - econstructor 2; eauto.
    eapply repr_val_id_L_LambdaANF_Codegen_vint_or_vptr; eauto.
  - assumption.
Qed.

Lemma rel_mem_eproj_get_local_repr :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    M.get y rho = Some (Vconstr t vs) ->
    exists L v7,
      protected_not_in_L_id p lenv L /\
      Genv.find_symbol (globalenv p) y = None /\
      M.get y lenv = Some v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vconstr t vs) m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs Hrel Hget.
  assert (Hfree : occurs_free (Eproj x t n y e) y).
  { constructor. }
  destruct (rel_mem_occurs_free_repr _ _ _ _ _ _ _ _ _ Hrel Hfree)
    as [v6 [L [Hprot [Hget6 Hrid]]]].
  rewrite Hget in Hget6.
  inversion Hget6; subst.
  inversion Hrid; subst; clear Hrid; try solve [inversion H].
  exists L, v7.
  repeat split; auto.
Qed.

Lemma rel_mem_ecase_get_var_or_funvar :
  forall fenv finfo_env p rep_env rho m lenv y cl t vl,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
    M.get y rho = Some (Vconstr t vl) ->
    exists L v7,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv y v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vconstr t vl) m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv y cl t vl Hrel Hget.
  assert (Hfree : occurs_free (Ecase y cl) y).
  { constructor. }
  destruct (rel_mem_occurs_free_repr _ _ _ _ _ _ _ _ _ Hrel Hfree)
    as [v6 [L [Hprot [Hget6 Hrid]]]].
  rewrite Hget in Hget6.
  inversion Hget6; subst.
  inversion Hrid; subst; clear Hrid; try solve [inversion H].
  exists L, v7.
  split; [exact Hprot |].
  split.
  - econstructor 2; eauto.
    eapply repr_val_id_L_LambdaANF_Codegen_vint_or_vptr; eauto.
  - assumption.
Qed.

Lemma rel_mem_ecase_branch :
  forall fenv finfo_env p rep_env rho m lenv y cl t e,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
    findtag cl t = Some e ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv.
Proof.
  intros fenv finfo_env p rep_env rho m lenv y cl t e Hrel Hfind.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [Hprot Hrel]].
  exists L.
  split; [exact Hprot|].
  intros x.
  specialize (Hrel x) as [Hocc Hfun].
  split.
  - intros Hocc_e.
    apply Hocc.
    eapply occurs_free_Ecase_Included.
    + eapply findtag_In; eauto.
    + exact Hocc_e.
  - intros rho' fds f v Hget Hsub.
    eapply Hfun; eauto.
Qed.

Lemma repr_val_constr_cases :
  forall fenv finfo_env p rep_env t vl m L v7,
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vconstr t vl) m L v7 ->
    (exists arr n,
      M.get t rep_env = Some (enum arr) /\
      vl = nil /\
      repr_unboxed_Codegen arr n /\
      v7 = make_vint n) \/
    (exists n a b i h,
      M.get t rep_env = Some (boxed n a) /\
      boxed_header n a h /\
      v7 = Vptr b i).
Proof.
  intros fenv finfo_env p rep_env t vl m L v7 Hrepr.
  remember (Vconstr t vl) as vc eqn:Heqvc.
  destruct Hrepr as
      [L0 z r m0 Hunboxed_int
      |t0 arr0 n0 m0 L0 Hget_enum Hunboxed
      |L0 t0 vs0 n0 a0 b0 i0 m0 h0 Hget_boxed Hloc Hload Hboxed Hvals
      |L0 vars avars fds f m0 b0 t0 t'0 vs0 pvs avs e0 asgn body l locs alocs finfo gccall
       Hfinddef Hgetfun Hgetfinfo Ht Hsym Hgc Hfun Hforall Hpvs Havs Halocs Havar Hright Hrepr_body].
  - inversion Heqvc.
  - inversion Heqvc; subst; clear Heqvc.
    left.
    exists arr0, n0.
    split; [exact Hget_enum |].
    split; [reflexivity |].
    split; [exact Hunboxed | reflexivity].
  - inversion Heqvc; subst; clear Heqvc.
    right.
    exists n0, a0, b0, i0, h0.
    split; [exact Hget_boxed |].
    split; [exact Hboxed | reflexivity].
  - inversion Heqvc.
Qed.

Lemma repr_val_constr_nth_boxed :
  forall fenv finfo_env p rep_env t vl m L v7 n v,
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env (Vconstr t vl) m L v7 ->
    nthN vl n = Some v ->
    exists n0 a b i h,
      M.get t rep_env = Some (boxed n0 a) /\
      boxed_header n0 a h /\
      v7 = Vptr b i.
Proof.
  intros fenv finfo_env p rep_env t vl m L v7 n v Hrepr Hnth.
  destruct (repr_val_constr_cases
              fenv finfo_env p rep_env t vl m L v7 Hrepr)
    as [[arr [n1 [Hget_enum [Hvl [Hunboxed Hv7]]]]]
       | [n0 [a [b [i [h [Hget_boxed [Hboxed Hvptr]]]]]]]].
  - subst vl.
    inversion Hnth.
  - exists n0, a, b, i, h.
    split; [exact Hget_boxed|].
    split; [exact Hboxed| exact Hvptr].
Qed.

Lemma rel_mem_eproj_nth_boxed :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    exists L v7 n0 a b i h,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv y v7 /\
      M.get t rep_env = Some (boxed n0 a) /\
      boxed_header n0 a h /\
      v7 = Vptr b i.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs v
    Hrel Hgety Hnth.
  destruct (rel_mem_eproj_get_var_or_funvar
              fenv finfo_env p rep_env rho m lenv x t n y e vs Hrel Hgety)
    as [L [v7 [Hprot [Hgvof Hrepr]]]].
  destruct (repr_val_constr_nth_boxed
              fenv finfo_env p rep_env t vs m L v7 n v Hrepr Hnth)
    as [n0 [a [b [i [h [Hget_boxed [Hboxed Hvptr]]]]]]].
  exists L, v7, n0, a, b, i, h.
  split; [exact Hprot|].
  split; [exact Hgvof|].
  split; [exact Hget_boxed|].
  split; [exact Hboxed|].
  exact Hvptr.
Qed.

Lemma rel_mem_eproj_nth_load_repr :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    exists L b i v7,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv y (Vptr b i) /\
      Mem.load int_chunk m b
        (Ptrofs.unsigned
           (Ptrofs.add i
              (Ptrofs.mul (Ptrofs.repr (Z.of_N n)) (Ptrofs.repr int_size)))) = Some v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs v
    Hrel Hgety Hnth.
  destruct (rel_mem_eproj_get_var_or_funvar
              fenv finfo_env p rep_env rho m lenv x t n y e vs Hrel Hgety)
    as [L [vy [Hprot [Hgvof Hrepr]]]].
  remember (Vconstr t vs) as vc eqn:Heqvc.
  destruct Hrepr as
      [L0 z r m0 Hunboxed_int
      |t0 arr0 n0 m0 L0 Hget_enum Hunboxed
      |L0 t0 vs0 n0 a0 b0 i0 m0 h0 Hget_boxed Hloc Hload_hdr Hboxed Hvals
      |L0 vars avars fds f m0 b0 t0 t'0 vs0 pvs avs e0 asgn body l locs alocs finfo gccall
       Hfinddef Hgetfun Hgetfinfo Ht Hsym Hgc Hfun Hforall Hpvs Havs Halocs Havar Hright Hrepr_body].
  - inversion Heqvc.
  - inversion Heqvc; subst; clear Heqvc.
    inversion Hnth.
  - inversion Heqvc; subst; clear Heqvc.
    destruct (repr_val_ptr_list_L_nth
                argsIdent allocIdent limitIdent gcIdent
                threadInfIdent tinfIdent isptrIdent caseIdent nParam
                fenv finfo_env p rep_env
                Hvals Hnth)
      as [vload [Hload_n Hrepr_v]].
    exists L0, b0, i0, vload.
    split; [exact Hprot|].
    split.
    + exact Hgvof.
    + split; [exact Hload_n| exact Hrepr_v].
  - inversion Heqvc.
Qed.

Lemma repr_val_id_fun_set :
  forall fenv finfo_env p rep_env rho' fds f m L lenv x vx,
    repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env
      (Vfun rho' fds f) m L lenv f ->
    repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env
      (Vfun rho' fds f) m L (M.set x vx lenv) f.
Proof.
  intros fenv finfo_env p rep_env rho' fds f m L lenv x vx Hrid.
  inversion Hrid; subst.
  - econstructor; eauto.
  - exfalso.
    inversion H1; subst; congruence.
Qed.

Lemma rel_mem_eproj_body_set :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs v,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
      (Eproj x t n y e) rho m lenv ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    exists v7,
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
        e (M.set x v rho) m (M.set x v7 lenv).
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs v
    Hrel Hprot_id Hfnb Hgety Hnth.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L [HprotL HrelL]].
  pose proof HrelL as HrelL_saved.
  destruct Hfnb as [Hfnb_exp Hfnb_rho].
  assert (Hx_none : Genv.find_symbol (globalenv p) x = None).
  { eapply Hfnb_exp. constructor. }
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxeq; subst.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  assert (Hfree_y : occurs_free (Eproj x t n y e) y).
  { constructor. }
  specialize (HrelL y) as [Hocc_y Hfun_y].
  specialize (Hocc_y Hfree_y) as [vy [Hgety' Hrid_y]].
  rewrite Hgety in Hgety'.
  inversion Hgety'; subst; clear Hgety'.
  inversion Hrid_y; subst; clear Hrid_y; try solve [inversion H].
  lazymatch goal with
  | Hrepr_constr : ?R (Vconstr t vs) m L ?vy7 |- _ =>
      remember (Vconstr t vs) as vc eqn:Heqvc;
      destruct Hrepr_constr as
        [L0 z r m0 Hunboxed_int
        |t0 arr0 n0 m0 L0 Hget_enum Hunboxed
        |L0 t0 vs0 n0 a0 b0 i0 m0 h0 Hget_boxed Hloc Hload_hdr Hboxed Hvals
        |L0 vars avars fds0 f0 m0 b0 t0 t'0 vs0 pvs avs e0 asgn body l locs alocs finfo gccall
         Hfinddef Hgetfun Hgetfinfo Ht Hsym Hgc Hfun Hforall Hpvs Havs Halocs Havar Hright Hrepr_body]
  end.
    + inversion Heqvc.
    + inversion Heqvc; subst; clear Heqvc.
      inversion Hnth.
    + inversion Heqvc; subst; clear Heqvc.
      destruct (repr_val_ptr_list_L_nth
                  argsIdent allocIdent limitIdent gcIdent
                  threadInfIdent tinfIdent isptrIdent caseIdent nParam
                  fenv finfo_env p rep_env
                  Hvals Hnth)
        as [v7 [Hload Hrepr_v]].
      exists v7.
      exists L0.
      split.
      * eapply protected_not_in_L_set; eauto.
      * intros z.
        specialize (HrelL_saved z) as [Hocc_z Hfun_z].
        split.
        -- intros Hfree_e.
           destruct (var_dec z x) as [Heqzx | Hneqzx].
           ++ subst z.
              exists v.
              split.
              ** rewrite M.gss. reflexivity.
              ** econstructor 2.
                 --- exact Hx_none.
                 --- rewrite M.gss. reflexivity.
                 --- exact Hrepr_v.
           ++ assert (Hfree_union :
                        Ensembles.Union var (occurs_free (Eproj x t n y e))
                          (Ensembles.Singleton var x) z).
              { eapply occurs_free_Eproj_Included; eauto. }
              destruct Hfree_union as [z0 Hfree_whole | z0 Hsingle].
              ** specialize (Hocc_z Hfree_whole) as [vz [Hgetz Hrid_z]].
                 exists vz.
                 split.
                 --- rewrite M.gso; eauto.
                 --- eapply repr_val_id_set; eauto.
              ** exfalso.
                 apply Hneqzx.
                 inversion Hsingle; reflexivity.
        -- intros rho' fds f vf Hgetz' Hsub.
           destruct (var_dec z x) as [Heqzx | Hneqzx].
           ++ subst z.
              rewrite M.gss in Hgetz'.
              inversion Hgetz'; subst; clear Hgetz'.
              assert (Hsub_constr :
                        subval_or_eq (Vfun rho' fds f) (Vconstr t vs)).
              { eapply subval_or_eq_constr; eauto.
                eapply nthN_in; eauto. }
              specialize (Hfun_y rho' fds f (Vconstr t vs) Hgety Hsub_constr)
                as [Hrid_f [Hclosed_f Hinfo_f]].
              split.
              ** eapply repr_val_id_fun_set; eauto.
              ** split; assumption.
           ++ rewrite M.gso in Hgetz' by assumption.
              specialize (Hfun_z rho' fds f vf Hgetz' Hsub)
                as [Hrid_f [Hclosed_f Hinfo_f]].
              split.
              ** eapply repr_val_id_fun_set; eauto.
              ** split; assumption.
    + inversion Heqvc.
Qed.

Lemma rel_mem_eproj_body_set_with_repr :
  forall fenv finfo_env p rep_env rho m lenv x t n y e vs v L v7,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
      (Eproj x t n y e) rho m lenv ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    protected_not_in_L_id p lenv L ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
      e (M.set x v rho) m (M.set x v7 lenv).
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e vs v L v7
    Hrel Hprot_id Hfnb Hgety Hnth HprotL Hrepr_v.
  unfold rel_mem_LambdaANF_Codegen_id in Hrel.
  unfold rel_mem_LambdaANF_Codegen in Hrel.
  destruct Hrel as [L0 [HprotL0 HrelL]].
  pose proof HrelL as HrelL_saved.
  destruct Hfnb as [Hfnb_exp _].
  assert (Hx_none : Genv.find_symbol (globalenv p) x = None).
  { eapply Hfnb_exp. constructor. }
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxeq; subst.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  set (L' := fun b ofs => L0 b ofs \/ L b ofs).
  exists L'.
  split.
  {
    eapply protected_not_in_L_set; eauto.
    eapply protected_not_in_L_union; eauto.
  }
  {
    intro z.
    specialize (HrelL_saved z) as [Hocc_z Hfun_z].
    split.
    {
      intro Hfree_e.
      destruct (var_dec z x) as [Heqzx | Hneqzx].
      {
        subst z.
        exists v.
        split.
        {
          rewrite M.gss. reflexivity.
        }
        {
          econstructor 2;
            [exact Hx_none
            |rewrite M.gss; reflexivity
            |].
          eapply repr_val_L_sub_locProp.
          - exact Hrepr_v.
          - unfold sub_locProp, L'. intros b ofs HL.
            right. exact HL.
        }
      }
      {
        assert (Hfree_union :
                  Ensembles.Union var (occurs_free (Eproj x t n y e))
                    (Ensembles.Singleton var x) z).
        { eapply occurs_free_Eproj_Included; eauto. }
        destruct Hfree_union as [z0 Hfree_whole | z0 Hsingle].
        {
          specialize (Hocc_z Hfree_whole) as [vz [Hgetz Hrid_z]].
          exists vz.
          split.
          {
            rewrite M.gso by exact Hneqzx.
            exact Hgetz.
          }
          {
            eapply repr_val_id_set.
            - eapply repr_val_id_L_sub_locProp.
              + exact Hrid_z.
              + unfold sub_locProp, L'. intros b ofs HL.
                left. exact HL.
            - exact Hneqzx.
          }
        }
        {
          exfalso.
          apply Hneqzx.
          inversion Hsingle; reflexivity.
        }
      }
    }
    {
      intros rho' fds f vf Hgetz' Hsub.
      destruct (var_dec z x) as [Heqzx | Hneqzx].
      {
        subst z.
        rewrite M.gss in Hgetz'.
        inversion Hgetz'; subst; clear Hgetz'.
        assert (Hsub_constr :
                  subval_or_eq (Vfun rho' fds f) (Vconstr t vs)).
        { eapply subval_or_eq_constr; eauto.
          eapply nthN_in; eauto. }
        specialize (HrelL y) as [_ Hfun_y].
        specialize (Hfun_y rho' fds f (Vconstr t vs) Hgety Hsub_constr)
          as [Hrid_f [Hclosed_f Hinfo_f]].
        split.
        {
          eapply repr_val_id_fun_set.
          eapply repr_val_id_L_sub_locProp.
          - exact Hrid_f.
          - unfold sub_locProp, L'. intros b ofs HL.
            left. exact HL.
        }
        {
          split; assumption.
        }
      }
      {
        rewrite M.gso in Hgetz' by exact Hneqzx.
        specialize (Hfun_z rho' fds f vf Hgetz' Hsub)
          as [Hrid_f [Hclosed_f Hinfo_f]].
        split.
        {
          eapply repr_val_id_fun_set.
          eapply repr_val_id_L_sub_locProp.
          - exact Hrid_f.
          - unfold sub_locProp, L'. intros b ofs HL.
            left. exact HL.
        }
        {
          split; assumption.
        }
      }
    }
  }
Qed.

Lemma arg_val_after_args_store :
  forall fenv finfo_env p rep_env v lenv m m' L args_b args_ofs v7,
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    Mem.store int_chunk m args_b
      (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m' ->
    Mem.unchanged_on L m m' ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv.
Proof.
  intros fenv finfo_env p rep_env v lenv m m' L args_b args_ofs v7 Hargs Hstore Hunch Hrepr.
  exists args_b, args_ofs, (Val.load_result int_chunk v7), L.
  split.
  - exact Hargs.
  - split.
    + eapply Mem.load_store_same in Hstore.
      exact Hstore.
    + eapply repr_val_L_unchanged; eauto.
      eapply repr_val_L_load_result; eauto.
Qed.

Lemma repr_bs_post_has_args_ptr :
  forall fenv finfo_env p rep_env v lenv k fu stm m m',
    (exists lenv',
       m_tstep2 (globalenv p) (State fu stm k empty_env lenv m)
         (State fu Sskip k empty_env lenv' m') /\
       same_args_ptr lenv lenv' /\
       arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv') ->
    exists args_b args_ofs, M.get argsIdent lenv = Some (Vptr args_b args_ofs).
Proof.
  intros fenv finfo_env p rep_env v lenv k fu stm m m' Hpost.
  destruct Hpost as [lenv' [_ [Hsame Harg]]].
  destruct (arg_val_has_args_ptr _ _ _ _ _ _ _ Harg) as [args_b [args_ofs Hget']].
  exists args_b, args_ofs.
  eapply same_args_ptr_get_left; eauto.
Qed.

Lemma bstep_e_halt_inv :
  forall pr cenv rho x v n,
    bstep_e pr cenv rho (Ehalt x) v n ->
    n = 0 /\ M.get x rho = Some v.
Proof.
  intros pr cenv rho x v n Hbs.
  inversion Hbs; subst.
  split; auto.
Qed.

Lemma bstep_e_econstr_inv :
  forall pr cenv rho x t ys e v n,
    bstep_e pr cenv rho (Econstr x t ys e) v n ->
    exists rho' vs,
      get_list ys rho = Some vs /\
      M.set x (Vconstr t vs) rho = rho' /\
      bstep_e pr cenv rho' e v n.
Proof.
  intros pr cenv rho x t ys e v n Hbs.
  inversion Hbs; subst.
  eauto.
Qed.

Lemma bstep_e_eproj_inv :
  forall pr cenv rho x t n y e ov c,
    bstep_e pr cenv rho (Eproj x t n y e) ov c ->
    exists vs v,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e pr cenv (M.set x v rho) e ov c.
Proof.
  intros pr cenv rho x t n y e ov c Hbs.
  inversion Hbs; subst.
  eauto.
Qed.

Lemma bstep_e_ecase_inv :
  forall pr cenv rho y cl v n,
    bstep_e pr cenv rho (Ecase y cl) v n ->
    exists t vl e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e pr cenv rho e v n.
Proof.
  intros pr cenv rho y cl v n Hbs.
  remember (Ecase y cl) as ecase eqn:Heq.
  induction Hbs; inversion Heq; subst; clear Heq.
  eexists; eexists; eexists.
  repeat split; eauto.
Qed.

Lemma bstep_e_efun_inv :
  forall pr cenv rho fl e v n,
    bstep_e pr cenv rho (Efun fl e) v n ->
    bstep_e pr cenv (def_funs fl fl rho rho) e v n.
Proof.
  intros pr cenv rho fl e v n Hbs.
  inversion Hbs; subst.
  assumption.
Qed.

Lemma bstep_e_eprim_val_inv :
  forall pr cenv rho x p e v n,
    bstep_e pr cenv rho (Eprim_val x p e) v n ->
    exists rho',
      M.set x (Vprim p) rho = rho' /\
      bstep_e pr cenv rho' e v n.
Proof.
  intros pr cenv rho x p e v n Hbs.
  inversion Hbs; subst.
  eauto.
Qed.

Lemma bstep_e_eprim_inv :
  forall pr cenv rho x f ys e v n,
    bstep_e pr cenv rho (Eprim x f ys e) v n ->
    exists vs f' vx rho',
      get_list ys rho = Some vs /\
      M.get f pr = Some f' /\
      f' vs = Some vx /\
      M.set x vx rho = rho' /\
      bstep_e pr cenv rho' e v n.
Proof.
  intros pr cenv rho x f ys e v n Hbs.
  inversion Hbs; subst; try discriminate.
  exists vs, f', v0, (M.set x v0 rho).
  repeat split; eauto.
Qed.

Lemma bstep_e_eapp_inv :
  forall pr cenv rho f t ys v n,
    bstep_e pr cenv rho (Eapp f t ys) v n ->
    exists rho_clo fl f' vs xs e rho_call c,
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e pr cenv rho_call e v c /\
      n = c + 1.
Proof.
  intros pr cenv rho f t ys v n Hbs.
  inversion Hbs; subst; try discriminate.
  exists rho', fl, f', vs, xs, e, rho'', c.
  repeat split; eauto.
Qed.

Lemma bstep_e_eletapp_inv :
  forall pr cenv rho x f t ys e v n,
    bstep_e pr cenv rho (Eletapp x f t ys e) v n ->
    exists rho_clo fl f' vs xs e_body rho_call v_body c c',
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e pr cenv rho_call e_body v_body c /\
      bstep_e pr cenv (M.set x v_body rho) e v c' /\
      n = c + c' + 1.
Proof.
  intros pr cenv rho x f t ys e v n Hbs.
  inversion Hbs; subst; try discriminate.
  exists rho', fl, f', vs, xs, e_body, rho'', v0, c, c'.
  repeat split; eauto.
Qed.

Lemma bstep_e_eapp_cost_pos :
  forall pr cenv rho f t ys v n,
    bstep_e pr cenv rho (Eapp f t ys) v n ->
    (0 < n)%nat.
Proof.
  intros pr cenv rho f t ys v n Hbs.
  destruct (bstep_e_eapp_inv _ _ _ _ _ _ _ _ Hbs)
    as [rho_clo [fl [f' [vs [xs [e [rho_call [c [_ [_ [_ [_ [_ Hn]]]]]]]]]]]]].
  subst n.
  lia.
Qed.

Lemma bstep_e_eletapp_cost_pos :
  forall pr cenv rho x f t ys e v n,
    bstep_e pr cenv rho (Eletapp x f t ys e) v n ->
    (0 < n)%nat.
Proof.
  intros pr cenv rho x f t ys e v n Hbs.
  pose proof (bstep_e_eletapp_inv _ _ _ _ _ _ _ _ _ _ Hbs) as Hinv.
  destruct Hinv as
    [rho_clo [fl [f0 [vs [xs [e_body [rho_call [v_body [c [c1 Hrest]]]]]]]]]].
  destruct Hrest as [_ [_ [_ [_ [_ [_ Hn]]]]]].
  subst n.
  lia.
Qed.

Lemma bstep_repr_efun_false :
  forall pr cenv rho fenv finfo_env p rep_env fds e v n stm,
    bstep_e pr cenv rho (Efun fds e) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Efun fds e) stm ->
    False.
Proof.
  intros pr cenv rho fenv finfo_env p rep_env fds e v n stm _ Hrepr.
  eapply repr_expr_efun_false; eauto.
Qed.

Lemma bstep_repr_eprim_val_false :
  forall pr cenv rho fenv finfo_env p rep_env x p0 e v n stm,
    bstep_e pr cenv rho (Eprim_val x p0 e) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim_val x p0 e) stm ->
    False.
Proof.
  intros pr cenv rho fenv finfo_env p rep_env x p0 e v n stm _ Hrepr.
  eapply repr_expr_eprim_val_false; eauto.
Qed.

Lemma bstep_repr_eprim_false :
  forall pr cenv rho fenv finfo_env p rep_env x f ys e v n stm,
    bstep_e pr cenv rho (Eprim x f ys e) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim x f ys e) stm ->
    False.
Proof.
  intros pr cenv rho fenv finfo_env p rep_env x f ys e v n stm _ Hrepr.
  eapply repr_expr_eprim_false; eauto.
Qed.

Lemma bstep_repr_supported_shape :
  forall pr cenv rho fenv finfo_env p rep_env e v n stm,
    bstep_e pr cenv rho e v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm ->
    match e with
    | Efun _ _ => False
    | Eprim_val _ _ _ => False
    | Eprim _ _ _ _ => False
    | _ => True
    end.
Proof.
  intros pr cenv rho fenv finfo_env p rep_env e v n stm Hbs Hrepr.
  destruct e; simpl; auto.
  - eapply bstep_repr_efun_false; eauto.
  - eapply bstep_repr_eprim_val_false; eauto.
  - eapply bstep_repr_eprim_false; eauto.
Qed.

Lemma int_chunk_eq_Mptr :
  int_chunk = Mptr.
Proof.
  unfold int_chunk, LambdaANF_to_Clight.int_chunk, Mptr.
  destruct Archi.ptr64; reflexivity.
Qed.

Lemma eval_tinfd_expr :
  forall p lenv m tinf_b tinf_ofs,
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    eval_expr (globalenv p) empty_env lenv m
      (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
              (Tstruct threadInfIdent noattr))
      (Vptr tinf_b tinf_ofs).
Proof.
  intros p lenv m tinf_b tinf_ofs Htinf.
  eapply eval_Elvalue.
  - eapply eval_Ederef.
    eapply eval_Etempvar.
    exact Htinf.
  - apply deref_loc_copy.
    simpl.
    reflexivity.
Qed.

Lemma eval_lvalue_tinfo_alloc :
  forall p lenv m tinf_b tinf_ofs,
    program_threadinfo_inv p ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    eval_lvalue (globalenv p) empty_env lenv m
      (Efield
         (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                 (Tstruct threadInfIdent noattr))
         allocIdent valPtr)
      tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr 0)) Full.
Proof.
  intros p lenv m tinf_b tinf_ofs Hpti Htinf.
  destruct Hpti as [co [Hco Hmembers]].
  eapply eval_Efield_struct
    with (id := threadInfIdent) (co := co) (att := noattr)
         (delta := 0%Z) (bf := Full).
  - eapply eval_tinfd_expr; eauto.
  - reflexivity.
  - exact Hco.
  - rewrite Hmembers.
    eapply allocIdent_delta.
Qed.

Lemma eval_lvalue_tinfo_limit :
  forall p lenv m tinf_b tinf_ofs,
    program_threadinfo_inv p ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    eval_lvalue (globalenv p) empty_env lenv m
      (Efield
         (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                 (Tstruct threadInfIdent noattr))
         limitIdent valPtr)
      tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)) Full.
Proof.
  intros p lenv m tinf_b tinf_ofs Hpti Htinf.
  destruct Hpti as [co [Hco Hmembers]].
  eapply eval_Efield_struct
    with (id := threadInfIdent) (co := co) (att := noattr)
         (delta := int_size) (bf := Full).
  - eapply eval_tinfd_expr; eauto.
  - reflexivity.
  - exact Hco.
  - rewrite Hmembers.
    eapply limitIdent_delta.
Qed.

Lemma sem_cast_vptr_valPtr :
  forall m b ofs,
    sem_cast (Vptr b ofs) valPtr valPtr m = Some (Vptr b ofs).
Proof.
  intros m b ofs.
  unfold sem_cast.
  simpl.
  destruct Archi.ptr64; reflexivity.
Qed.

Lemma eval_allocPtr_from_get :
  forall p lenv m alloc_b alloc_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    eval_expr (globalenv p) empty_env lenv m
      (LambdaANF_to_Clight.allocPtr allocIdent)
      (Vptr alloc_b alloc_ofs).
Proof.
  intros p lenv m alloc_b alloc_ofs Halloc.
  cbn [LambdaANF_to_Clight.allocPtr].
  apply eval_Etempvar.
  exact Halloc.
Qed.

Lemma eval_limitPtr_from_get :
  forall p lenv m alloc_b limit_ofs,
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    eval_expr (globalenv p) empty_env lenv m
      (Etempvar limitIdent valPtr)
      (Vptr alloc_b limit_ofs).
Proof.
  intros p lenv m alloc_b limit_ofs Hlimit.
  apply eval_Etempvar.
  exact Hlimit.
Qed.

Lemma step_assign_tinfo_alloc :
  forall p fu k lenv m m1 tinf_b tinf_ofs alloc_b alloc_ofs,
    program_threadinfo_inv p ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    Mem.store int_chunk m tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr 0)))
      (Vptr alloc_b alloc_ofs) = Some m1 ->
    traceless_step2 (globalenv p)
      (State fu
         (Sassign
            (Efield
               (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                       (Tstruct threadInfIdent noattr))
               allocIdent valPtr)
            (LambdaANF_to_Clight.allocPtr allocIdent))
         k empty_env lenv m)
      (State fu Sskip k empty_env lenv m1).
Proof.
  intros p fu k lenv m m1 tinf_b tinf_ofs alloc_b alloc_ofs
    Hpti Htinf Halloc Hstore.
  eapply step_assign with (v2 := Vptr alloc_b alloc_ofs) (v := Vptr alloc_b alloc_ofs).
  - eapply eval_lvalue_tinfo_alloc; eauto.
  - eapply eval_allocPtr_from_get; eauto.
  - apply sem_cast_vptr_valPtr.
  - eapply assign_loc_value.
    2:{ exact Hstore. }
    reduce_val_access. constructor.
Qed.

Lemma step_assign_tinfo_limit :
  forall p fu k lenv m1 m2 tinf_b tinf_ofs alloc_b limit_ofs,
    program_threadinfo_inv p ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    Mem.store int_chunk m1 tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)))
      (Vptr alloc_b limit_ofs) = Some m2 ->
    traceless_step2 (globalenv p)
      (State fu
         (Sassign
            (Efield
               (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                       (Tstruct threadInfIdent noattr))
               limitIdent valPtr)
            (Etempvar limitIdent valPtr))
         k empty_env lenv m1)
      (State fu Sskip k empty_env lenv m2).
Proof.
  intros p fu k lenv m1 m2 tinf_b tinf_ofs alloc_b limit_ofs
    Hpti Htinf Hlimit Hstore.
  eapply step_assign with (v2 := Vptr alloc_b limit_ofs) (v := Vptr alloc_b limit_ofs).
  - eapply eval_lvalue_tinfo_limit; eauto.
  - eapply eval_limitPtr_from_get; eauto.
  - apply sem_cast_vptr_valPtr.
  - eapply assign_loc_value.
    2:{ exact Hstore. }
    reduce_val_access. constructor.
Qed.

Lemma m_tstep2_tinfo_assigns :
  forall p fu k lenv m m1 m2 tinf_b tinf_ofs alloc_b alloc_ofs limit_ofs,
    program_threadinfo_inv p ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    Mem.store int_chunk m tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr 0)))
      (Vptr alloc_b alloc_ofs) = Some m1 ->
    Mem.store int_chunk m1 tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)))
      (Vptr alloc_b limit_ofs) = Some m2 ->
    m_tstep2 (globalenv p)
      (State fu
         (Ssequence
            (Sassign
               (Efield
                  (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                          (Tstruct threadInfIdent noattr))
                  allocIdent valPtr)
               (LambdaANF_to_Clight.allocPtr allocIdent))
            (Sassign
               (Efield
                  (Ederef (Etempvar tinfIdent (Tpointer (Tstruct threadInfIdent noattr) noattr))
                          (Tstruct threadInfIdent noattr))
                  limitIdent valPtr)
               (Etempvar limitIdent valPtr)))
         k empty_env lenv m)
      (State fu Sskip k empty_env lenv m2).
Proof.
  intros p fu k lenv m m1 m2 tinf_b tinf_ofs alloc_b alloc_ofs limit_ofs
    Hpti Htinf Halloc Hlimit Hs0 Hs1.
  eapply m_tstep2_transitive.
  - apply m_tstep2_step. constructor.
  - eapply m_tstep2_transitive.
    + apply m_tstep2_step.
      eapply step_assign_tinfo_alloc; eauto.
    + eapply m_tstep2_transitive.
      * apply m_tstep2_step. constructor.
      * apply m_tstep2_step.
        eapply step_assign_tinfo_limit; eauto.
Qed.

Lemma eval_lvalue_args1 :
  forall p lenv m args_b args_ofs,
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    eval_lvalue (globalenv p) empty_env lenv m
      (Ederef
         (add (Etempvar argsIdent valPtr)
              (c_int (Z.of_nat 1) LambdaANF_to_Clight.uval))
         val)
      args_b (Ptrofs.add args_ofs (Ptrofs.repr int_size)) Full.
Proof.
  intros p lenv m args_b args_ofs Hargs.
  assert (Harchi : Archi.ptr64 = true) by (vm_compute; reflexivity).
  eapply eval_Ederef.
  eapply eval_Ebinop.
  - apply eval_Etempvar.
    exact Hargs.
  - unfold c_int, LambdaANF_to_Clight.c_int.
    rewrite Harchi.
    apply eval_Econst_long.
  - unfold add, LambdaANF_to_Clight.add, sem_binary_operation, sem_add.
    simpl typeof.
    unfold val, LambdaANF_to_Clight.val, LambdaANF_to_Clight.uval,
      c_int, LambdaANF_to_Clight.c_int.
    rewrite Harchi.
    unfold classify_add.
    simpl typeconv.
    cbv beta iota.
    f_equal. f_equal. f_equal. f_equal.
    unfold Ptrofs.mul, Ptrofs.of_int64, sizeof.
    simpl.
    repeat (rewrite Int64.unsigned_repr
      by (unfold Int64.max_unsigned; simpl; lia);
      rewrite Ptrofs.unsigned_repr
      by (unfold Ptrofs.max_unsigned; rewrite Ptrofs.modulus_eq64 by auto; simpl; lia)).
    reflexivity.
Qed.

Lemma step_assign_args1 :
  forall p fu k lenv m m' args_b args_ofs e v7,
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    eval_expr (globalenv p) empty_env lenv m e v7 ->
    sem_cast v7 (typeof e) val m = Some v7 ->
    Mem.store int_chunk m args_b
      (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m' ->
    traceless_step2 (globalenv p)
      (State fu
         (Sassign
            (Ederef
               (add (Etempvar argsIdent valPtr)
                    (c_int (Z.of_nat 1) LambdaANF_to_Clight.uval))
               val)
            e)
         k empty_env lenv m)
      (State fu Sskip k empty_env lenv m').
Proof.
  intros p fu k lenv m m' args_b args_ofs e v7
    Hargs Heval Hcast Hstore.
  eapply step_assign with (v2 := v7) (v := v7).
  - eapply eval_lvalue_args1; eauto.
  - exact Heval.
  - exact Hcast.
  - eapply assign_loc_value.
    2:{ exact Hstore. }
    reduce_val_access.
    constructor.
Qed.

Lemma get_var_or_funvar_local_ptr_from_none :
  forall p lenv y b i,
    Genv.find_symbol (globalenv p) y = None ->
    get_var_or_funvar p lenv y (Vptr b i) ->
    M.get y lenv = Some (Vptr b i).
Proof.
  intros p lenv y b i Hnone Hgvof.
  change (Genv.find_symbol (Genv.globalenv p) y = None) in Hnone.
  inversion Hgvof; subst; try congruence; auto.
Qed.

Lemma eval_eproj_field_from_load :
  forall p lenv m y n b i v7,
    M.get y lenv = Some (Vptr b i) ->
    Mem.load int_chunk m b
      (Ptrofs.unsigned
         (Ptrofs.add i
            (Ptrofs.mul (Ptrofs.repr (Z.of_N n)) (Ptrofs.repr int_size)))) = Some v7 ->
    eval_expr (globalenv p) empty_env lenv m
      (Ederef
         (add (Ecast (Etempvar y val) valPtr)
              (c_int (Z.of_N n) LambdaANF_to_Clight.uval))
         val) v7.
Proof.
  intros p lenv m y n b i v7 Hylenv Hload.
  assert (Harchi : Archi.ptr64 = true) by (vm_compute; reflexivity).
  eapply eval_Elvalue.
  - eapply eval_Ederef.
    eapply eval_Ebinop.
    + eapply eval_Ecast.
      * apply eval_Etempvar.
        exact Hylenv.
      * unfold sem_cast.
        simpl.
        reflexivity.
    + unfold c_int, LambdaANF_to_Clight.c_int.
      rewrite Harchi.
      apply eval_Econst_long.
    + unfold add, LambdaANF_to_Clight.add, sem_binary_operation, sem_add.
      simpl typeof.
      unfold val, LambdaANF_to_Clight.val, LambdaANF_to_Clight.uval,
        c_int, LambdaANF_to_Clight.c_int.
      rewrite Harchi.
      unfold classify_add.
      simpl typeconv.
      cbv beta iota.
      f_equal. f_equal. f_equal. f_equal.
      unfold Ptrofs.mul, Ptrofs.of_int64, sizeof.
      simpl.
      repeat rewrite Int64.unsigned_repr_eq.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      reflexivity.
  - apply deref_loc_value with (chunk := int_chunk).
    + unfold val, LambdaANF_to_Clight.val, int_chunk, LambdaANF_to_Clight.int_chunk.
      simpl.
      reflexivity.
    + assert (Hofs_eq :
        Ptrofs.mul (Ptrofs.repr (if Archi.ptr64 then 8%Z else 4%Z))
          (Ptrofs.of_int64 (Int64.repr (Z.of_N n))) =
        Ptrofs.mul (Ptrofs.repr (Z.of_N n)) (Ptrofs.repr int_size)).
      {
        rewrite Harchi.
        unfold int_size, int_chunk, LambdaANF_to_Clight.int_chunk.
        simpl.
        unfold Ptrofs.of_int64.
        rewrite ptrofs_of_int64.
        rewrite Ptrofs.mul_commut.
        reflexivity.
      }
      rewrite Hofs_eq.
      exact Hload.
Qed.

Lemma eproj_prefix_step_m_tstep2 :
  forall fenv finfo_env p rep_env rho m lenv x t n y e stm fu k vs v,
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    M.get y rho = Some (Vconstr t vs) ->
    nthN vs n = Some v ->
    exists s v7 L,
      protected_not_in_L_id p lenv L /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      stm =
        Ssequence
          (Sset x
             (Ederef
                (add (Ecast (Etempvar y val) valPtr)
                     (c_int (Z.of_N n) LambdaANF_to_Clight.uval))
                val)) s /\
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu s k empty_env (M.set x v7 lenv) m) /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x t n y e stm fu k vs v
    Hrepr Hrel Hy Hnth.
  inversion Hrepr; subst; clear Hrepr.
  destruct (rel_mem_eproj_get_local_repr
              fenv finfo_env p rep_env rho m lenv x t n y e vs Hrel Hy)
    as [L0 [vy [Hprot0 [Hsym_none [Hylenv0 Hrepr_constr]]]]].
  destruct (rel_mem_eproj_nth_load_repr
              fenv finfo_env p rep_env rho m lenv x t n y e vs v Hrel Hy Hnth)
    as [L [b [i [v7 [Hprot [Hgvof [Hload Hrepr_v]]]]]]].
  assert (Hylenv_ptr : M.get y lenv = Some (Vptr b i)).
  {
    eapply get_var_or_funvar_local_ptr_from_none; eauto.
  }
  assert (Heval_rhs :
    eval_expr (globalenv p) empty_env lenv m
      (Ederef
         (add (Ecast (Etempvar y val) valPtr)
              (c_int (Z.of_N n) LambdaANF_to_Clight.uval))
         val) v7).
  { eapply eval_eproj_field_from_load; eauto. }
  eexists.
  exists v7.
  exists L.
  split; [exact Hprot|].
  split; [eassumption|].
  split.
  - reflexivity.
  - split.
    + eapply m_tstep2_seq_set.
      exact Heval_rhs.
    + exact Hrepr_v.
Qed.

Lemma halt_rel_repr_extract :
  forall fenv finfo_env p rep_env rho m lenv x v stm,
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    exists L v7 e,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv x v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 /\
      var_or_funvar threadInfIdent nParam fenv finfo_env p x e.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v stm Hrel Hget Hrepr.
  destruct (rel_mem_halt_get_var_or_funvar _ _ _ _ _ _ _ _ _ Hrel Hget)
    as [L [v7 [Hprot [Hgvof Hreprv]]]].
  destruct (repr_expr_ehalt_inv _ _ _ _ _ _ Hrepr) as [e Hvof].
  exists L, v7, e.
  repeat split; assumption.
Qed.

Lemma halt_rel_repr_eval_cast :
  forall fenv finfo_env p rep_env rho m lenv x v stm,
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    exists L v7 e,
      protected_not_in_L_id p lenv L /\
      get_var_or_funvar p lenv x v7 /\
      repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 /\
      var_or_funvar threadInfIdent nParam fenv finfo_env p x e /\
      eval_expr (globalenv p) empty_env lenv m e v7 /\
      sem_cast v7 (typeof e) val m = Some v7.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v stm Hsym Hfinfo Hrel Hget Hrepr.
  destruct (halt_rel_repr_extract _ _ _ _ _ _ _ _ _ _ Hrel Hget Hrepr)
    as [L [v7 [e [Hprot [Hgvof [Hreprv Hvof]]]]]].
  pose proof (proj1 (var_or_funvar_of_f threadInfIdent nParam fenv finfo_env p x e) Hvof)
    as Heq.
  exists L, v7, e.
  repeat split; try assumption.
  - rewrite <- Heq.
    eapply get_var_or_funvar_eval; eauto.
  - rewrite <- Heq.
    eapply get_var_or_funvar_semcast; eauto.
Qed.

Lemma protected_not_in_L_args1_store_unchanged :
  forall p lenv L m m' args_b args_ofs v7,
    protected_not_in_L_id p lenv L ->
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    Mem.store int_chunk m args_b
      (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m' ->
    Mem.unchanged_on L m m'.
Proof.
  intros p lenv L m m' args_b args_ofs v7 Hprot Hargs Hstore.
  destruct Hprot as [alloc_b [alloc_ofs [limit_ofs [args_b' [args_ofs' [tinf_b [tinf_ofs
    [Halloc [HallocL [Hlimit [Hargs' [HargsL [Htinf [HtinfL Hglob]]]]]]]]]]]]]].
  rewrite Hargs' in Hargs.
  inversion Hargs; subst.
  eapply Mem.store_unchanged_on; eauto.
  intros i Hi.
  assert (Hone : (0 <= 1 < max_args)%Z) by (unfold max_args; lia).
  replace (Ptrofs.repr int_size) with (Ptrofs.repr (int_size * 1)) in Hi
    by (f_equal; lia).
  eapply HargsL; eauto.
Qed.

Lemma halt_args1_store_arg_val :
  forall fenv finfo_env p rep_env v lenv m m' L args_b args_ofs v7,
    protected_not_in_L_id p lenv L ->
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    Mem.store int_chunk m args_b
      (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m' ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 ->
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv.
Proof.
  intros fenv finfo_env p rep_env v lenv m m' L args_b args_ofs v7 Hprot Hargs Hstore Hrepr.
  eapply arg_val_after_args_store; eauto.
  eapply protected_not_in_L_args1_store_unchanged; eauto.
Qed.

Lemma protected_not_in_L_tinfo_store_unchanged :
  forall p lenv L m m' tinf_b tinf_ofs ofs v,
    protected_not_in_L_id p lenv L ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    Mem.store int_chunk m tinf_b ofs v = Some m' ->
    Mem.unchanged_on L m m'.
Proof.
  intros p lenv L m m' tinf_b tinf_ofs ofs v Hprot Htinf Hstore.
  destruct Hprot as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b' [tinf_ofs'
    [Halloc [HallocL [Hlimit [Hargs [HargsL [Htinf' [HtinfL Hglob]]]]]]]]]]]]]].
  rewrite Htinf' in Htinf.
  inversion Htinf; subst.
  eapply Mem.store_unchanged_on.
  - exact Hstore.
  - intros i _.
    eapply HtinfL.
Qed.

Lemma protected_not_in_L_tinfo_two_stores_unchanged :
  forall p lenv L m m1 m2 tinf_b tinf_ofs ofs0 v0 v1,
    protected_not_in_L_id p lenv L ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    Mem.store int_chunk m tinf_b ofs0 v0 = Some m1 ->
    Mem.store int_chunk m1 tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size))) v1 = Some m2 ->
    Mem.unchanged_on L m m2.
Proof.
  intros p lenv L m m1 m2 tinf_b tinf_ofs ofs0 v0 v1 Hprot Htinf Hs0 Hs1.
  eapply Mem.unchanged_on_trans.
  - eapply protected_not_in_L_tinfo_store_unchanged; eauto.
  - eapply protected_not_in_L_tinfo_store_unchanged; eauto.
Qed.

Lemma repr_val_after_tinfo_two_stores :
  forall fenv finfo_env p rep_env v m m1 m2 L v7 lenv tinf_b tinf_ofs ofs0 v0 v1,
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 ->
    protected_not_in_L_id p lenv L ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    Mem.store int_chunk m tinf_b ofs0 v0 = Some m1 ->
    Mem.store int_chunk m1 tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size))) v1 = Some m2 ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m2 L v7.
Proof.
  intros fenv finfo_env p rep_env v m m1 m2 L v7 lenv tinf_b tinf_ofs ofs0 v0 v1
    Hrepr Hprot Htinf Hs0 Hs1.
  eapply repr_val_L_unchanged; eauto.
  eapply protected_not_in_L_tinfo_two_stores_unchanged; eauto.
Qed.

Lemma correct_tinfo_store_alloc_exists :
  forall p z lenv m,
    correct_tinfo p z lenv m ->
    exists alloc_b alloc_ofs tinf_b tinf_ofs m1,
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      Mem.store int_chunk m tinf_b
        (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
        (Vptr alloc_b alloc_ofs) = Some m1.
Proof.
  intros p z lenv m Hct.
  destruct Hct as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs
    [Halloc [Halign [Hrange [Hlimit [Hbound [Hargs [Hdj [HargsRange [HargsVA [Htinf
    [HtinfNe1 [HtinfNe2 [HtinfVA [Hderef Hglob]]]]]]]]]]]]]]]]]]]]].
  assert (Hva0 : Mem.valid_access m int_chunk tinf_b
    (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0)))) Writable).
  { eapply HtinfVA. lia. }
  destruct (Mem.valid_access_store m int_chunk tinf_b
    (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
    (Vptr alloc_b alloc_ofs) Hva0) as [m1 Hstore].
  exists alloc_b, alloc_ofs, tinf_b, tinf_ofs, m1.
  repeat split; eauto.
Qed.

Lemma correct_tinfo_store_limit_exists_after_alloc :
  forall p z lenv m m1 alloc_b alloc_ofs limit_ofs tinf_b tinf_ofs,
    correct_tinfo p z lenv m ->
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) ->
    M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) ->
    Mem.store int_chunk m tinf_b
      (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
      (Vptr alloc_b alloc_ofs) = Some m1 ->
    exists m2,
      Mem.store int_chunk m1 tinf_b
        (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)))
        (Vptr alloc_b limit_ofs) = Some m2.
Proof.
  intros p z lenv m m1 alloc_b alloc_ofs limit_ofs tinf_b tinf_ofs
    Hct Halloc Hlimit Htinf Hs0.
  destruct Hct as [alloc_b' [alloc_ofs' [limit_ofs' [args_b [args_ofs [tinf_b' [tinf_ofs'
    [Halloc' [Halign [Hrange [Hlimit' [Hbound [Hargs [Hdj [HargsRange [HargsVA [Htinf'
    [HtinfNe1 [HtinfNe2 [HtinfVA [Hderef Hglob]]]]]]]]]]]]]]]]]]]]].
  rewrite Halloc' in Halloc. inversion Halloc; subst.
  rewrite Hlimit' in Hlimit. inversion Hlimit; subst.
  rewrite Htinf' in Htinf. inversion Htinf; subst.
  assert (Hva1 : Mem.valid_access m int_chunk tinf_b
    (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1)))) Writable).
  { eapply HtinfVA. lia. }
  assert (Hva1' : Mem.valid_access m1 int_chunk tinf_b
    (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1)))) Writable).
  { eapply Mem.store_valid_access_1; eauto. }
  replace (Ptrofs.repr int_size) with (Ptrofs.repr (int_size * 1)) by (f_equal; lia).
  destruct (Mem.valid_access_store m1 int_chunk tinf_b
    (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 1))))
    (Vptr alloc_b limit_ofs) Hva1') as [m2 Hs1].
  exists m2.
  exact Hs1.
Qed.

Lemma ptrofs_repr_one :
  Ptrofs.repr 1%Z = Ptrofs.one.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma correct_tinfo_store_args1_exists :
  forall p z lenv m args_b args_ofs v7,
    correct_tinfo p z lenv m ->
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
    exists m',
      Mem.store int_chunk m args_b
        (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m'.
Proof.
  intros p z lenv m args_b args_ofs v7 Hct Hargs.
  destruct Hct as [alloc_b [alloc_ofs [limit_ofs [args_b' [args_ofs' [tinf_b [tinf_ofs
    [Halloc [Halign [Hrange [Hlimit [Hbound [Hargs' [Hdj [HargsRange [HargsVA [Htinf
    [HtinfNe1 [HtinfNe2 [HtinfVA [Hderef Hglob]]]]]]]]]]]]]]]]]]]]].
  rewrite Hargs' in Hargs.
  inversion Hargs; subst.
  assert (Hva1 : Mem.valid_access m int_chunk args_b
    (Ptrofs.unsigned
      (Ptrofs.add args_ofs
        (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr 1)))) Writable).
  { eapply HargsVA. unfold max_args. lia. }
  replace (Ptrofs.repr 1) with Ptrofs.one in Hva1 by apply ptrofs_repr_one.
  rewrite Ptrofs.mul_one in Hva1.
  destruct (Mem.valid_access_store m int_chunk args_b
    (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size)))
    v7 Hva1) as [m' Hstore].
  exists m'.
  exact Hstore.
Qed.

Lemma halt_store_chain_exists :
  forall fenv finfo_env p rep_env v lenv m L max_alloc v7,
    correct_tinfo p max_alloc lenv m ->
    protected_not_in_L_id p lenv L ->
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L v7 ->
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs tinf_b tinf_ofs m1 m2 m3,
      M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
      M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
      M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      Mem.store int_chunk m tinf_b
        (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr (int_size * 0))))
        (Vptr alloc_b alloc_ofs) = Some m1 /\
      Mem.store int_chunk m1 tinf_b
        (Ptrofs.unsigned (Ptrofs.add tinf_ofs (Ptrofs.repr int_size)))
        (Vptr alloc_b limit_ofs) = Some m2 /\
      Mem.store int_chunk m2 args_b
        (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) v7 = Some m3 /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m3 lenv.
Proof.
  intros fenv finfo_env p rep_env v lenv m L max_alloc v7 Hct Hprot Hrepr.
  pose proof Hct as Hct0.
  destruct Hct0 as [alloc_b0 [alloc_ofs0 [limit_ofs0 [args_b0 [args_ofs0 [tinf_b0 [tinf_ofs0
    [Halloc0 [Halign0 [Hrange0 [Hlimit0 [Hbound0 [Hargs0 [Hdj0 [HargsRange0 [HargsVA0 [Htinf0
    [HtinfNe10 [HtinfNe20 [HtinfVA0 [Hderef0 Hglob0]]]]]]]]]]]]]]]]]]]]].

  destruct (correct_tinfo_store_alloc_exists _ _ _ _ Hct)
    as [alloc_b [alloc_ofs [tinf_b [tinf_ofs [m1 [Halloc [Htinf Hs0]]]]]]].

  assert (Heq_alloc : alloc_b = alloc_b0 /\ alloc_ofs = alloc_ofs0).
  {
    rewrite Halloc0 in Halloc.
    inversion Halloc; subst.
    auto.
  }
  destruct Heq_alloc as [-> ->].
  assert (Heq_tinf : tinf_b = tinf_b0 /\ tinf_ofs = tinf_ofs0).
  {
    rewrite Htinf0 in Htinf.
    inversion Htinf; subst.
    auto.
  }
  destruct Heq_tinf as [-> ->].

  destruct (correct_tinfo_store_limit_exists_after_alloc _ _ _ _ _ _ _ _ _ _ Hct Halloc0 Hlimit0 Htinf0 Hs0)
    as [m2 Hs1].

  pose proof (correct_tinfo_after_store _ _ _ _ Hct _ _ _ _ _ Hs0) as Hct1.
  pose proof (correct_tinfo_after_store _ _ _ _ Hct1 _ _ _ _ _ Hs1) as Hct2.

  destruct (correct_tinfo_store_args1_exists _ _ _ _ _ _ v7 Hct2 Hargs0)
    as [m3 Hs2].

  assert (Hrepr2 :
    repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m2 L v7).
  {
    eapply repr_val_after_tinfo_two_stores
      with (lenv := lenv) (tinf_b := tinf_b0) (tinf_ofs := tinf_ofs0)
           (ofs0 := Ptrofs.unsigned (Ptrofs.add tinf_ofs0 (Ptrofs.repr (int_size * 0))))
           (v0 := Vptr alloc_b0 alloc_ofs0) (v1 := Vptr alloc_b0 limit_ofs0); eauto.
  }

  assert (Harg :
    arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m3 lenv).
  {
    eapply halt_args1_store_arg_val; eauto.
  }

  exists alloc_b0, alloc_ofs0, limit_ofs0, args_b0, args_ofs0, tinf_b0, tinf_ofs0, m1, m2, m3.
  repeat split; eauto.
Qed.

Lemma halt_eval_cast_arg_val_exists :
  forall fenv finfo_env p rep_env rho m lenv x v stm max_alloc,
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    correct_tinfo p max_alloc lenv m ->
    exists L v7 e m3,
      protected_not_in_L_id p lenv L /\
      eval_expr (globalenv p) empty_env lenv m e v7 /\
      sem_cast v7 (typeof e) val m = Some v7 /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m3 lenv.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v stm max_alloc
    Hsym Hfinfo Hrel Hget Hrepr Hct.
  destruct (halt_rel_repr_eval_cast _ _ _ _ _ _ _ _ _ _ Hsym Hfinfo Hrel Hget Hrepr)
    as [L [v7 [e [Hprot [_ [Hreprv [_ [Heval Hcast]]]]]]]].
  destruct (halt_store_chain_exists
              fenv finfo_env p rep_env v lenv m L max_alloc v7 Hct Hprot Hreprv)
    as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [m1 [m2 [m3 Hchain]]]]]]]]]].
  destruct Hchain as [_ [_ [_ [_ [_ [_ [_ Harg]]]]]]].
  exists L, v7, e, m3.
  repeat split; eauto.
Qed.

Lemma halt_same_args_ptr_arg_val_exists :
  forall fenv finfo_env p rep_env rho m lenv x v stm max_alloc,
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    correct_tinfo p max_alloc lenv m ->
    exists m' lenv',
      same_args_ptr lenv lenv' /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v stm max_alloc
    Hsym Hfinfo Hrel Hget Hrepr Hct.
  destruct (halt_eval_cast_arg_val_exists
              fenv finfo_env p rep_env rho m lenv x v stm max_alloc
              Hsym Hfinfo Hrel Hget Hrepr Hct)
    as [L [v7 [e [m3 [_ [_ [_ Harg]]]]]]].
  exists m3, lenv.
  split.
  - apply same_args_ptr_refl.
  - exact Harg.
Qed.

Lemma ehalt_m_tstep2_arg_val :
  forall fenv finfo_env p rep_env rho m lenv x v stm fu k max_alloc,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    M.get x rho = Some v ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    correct_tinfo p max_alloc lenv m ->
    exists m',
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu Sskip k empty_env lenv m') /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv.
Proof.
  intros fenv finfo_env p rep_env rho m lenv x v stm fu k max_alloc
    Hpinv Hsym Hfinfo Hrel Hget Hrepr Hct.
  destruct Hpinv as [_ [Hpti _]].
  inversion Hrepr; subst; clear Hrepr.
  destruct (rel_mem_halt_get_var_or_funvar _ _ _ _ _ _ _ _ _ Hrel Hget)
    as [L [v7 [Hprot [Hgvof Hreprv]]]].
  destruct (halt_store_chain_exists
              fenv finfo_env p rep_env v lenv m L max_alloc v7 Hct Hprot Hreprv)
    as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [m1 [m2 [m3 Hchain]]]]]]]]]].
  destruct Hchain as [Halloc [Hlimit [Hargs [Htinf [Hs0 [Hs1 [Hs2 Harg]]]]]]].
  pose proof (proj1 (var_or_funvar_of_f threadInfIdent nParam fenv finfo_env p x e) H0)
    as Heq_vof.
  assert (Heval2 : eval_expr (globalenv p) empty_env lenv m2 e v7).
  { rewrite <- Heq_vof.
    eapply get_var_or_funvar_eval; eauto. }
  assert (Hcast2 : sem_cast v7 (typeof e) val m2 = Some v7).
  { rewrite <- Heq_vof.
    eapply get_var_or_funvar_semcast; eauto. }
  exists m3.
  split.
  - eapply m_tstep2_transitive.
    + apply m_tstep2_step. constructor.
    + eapply m_tstep2_transitive.
      * eapply m_tstep2_tinfo_assigns; eauto.
      * eapply m_tstep2_transitive.
        { apply m_tstep2_step. constructor. }
        { apply m_tstep2_step.
          eapply step_assign_args1; eauto. }
  - exact Harg.
Qed.

Lemma repr_bs_ehalt_case :
  forall p rep_env cenv fenv finfo_env rho v x n stm lenv m k max_alloc fu,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Ehalt x) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
    correct_tinfo p max_alloc lenv m ->
    exists m' lenv',
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu Sskip k empty_env lenv' m') /\
      same_args_ptr lenv lenv' /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv fenv finfo_env rho v x n stm lenv m k max_alloc fu
    Hpinv Hsym Hfinfo Hbs Hrepr Hrel Hct.
  destruct (bstep_e_halt_inv _ _ _ _ _ _ Hbs) as [_ Hget].
  destruct (ehalt_m_tstep2_arg_val
              fenv finfo_env p rep_env rho m lenv x v stm fu k max_alloc
              Hpinv Hsym Hfinfo Hrel Hget Hrepr Hct)
    as [m' [Hstep Harg]].
  exists m', lenv.
  split.
  - exact Hstep.
  - split.
    + apply same_args_ptr_refl.
    + exact Harg.
Qed.

Lemma repr_bs_halt_step_lift :
  forall p rep_env cenv ienv fenv finfo_env rho v x n,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Ehalt x) v n ->
    correct_envs cenv ienv rep_env rho (Ehalt x) ->
    protected_id_not_bound_id rho (Ehalt x) ->
    unique_bindings_env rho (Ehalt x) ->
    functions_not_bound p rho (Ehalt x) ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ehalt x) rho m lenv ->
      correct_alloc (Ehalt x) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho v x n
    Hpinv Hsym Hfinfo Hbs _ _ _ _
    stm lenv m k max_alloc fu Hrepr Hrel _ Hct.
  eapply repr_bs_ehalt_case; eauto.
Qed.

Lemma repr_bs_efun_step_lift :
  forall p rep_env cenv ienv fenv finfo_env rho v fds e n,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Efun fds e) v n ->
    correct_envs cenv ienv rep_env rho (Efun fds e) ->
    protected_id_not_bound_id rho (Efun fds e) ->
    unique_bindings_env rho (Efun fds e) ->
    functions_not_bound p rho (Efun fds e) ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Efun fds e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Efun fds e) rho m lenv ->
      correct_alloc (Efun fds e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho v fds e n
    _ _ _ _ _ _ _ _
    stm lenv m k max_alloc fu Hrepr _ _ _.
  exfalso.
  eapply repr_expr_efun_false; eauto.
Qed.

Lemma repr_bs_eprim_val_step_lift :
  forall p rep_env cenv ienv fenv finfo_env rho v x p0 e n,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Eprim_val x p0 e) v n ->
    correct_envs cenv ienv rep_env rho (Eprim_val x p0 e) ->
    protected_id_not_bound_id rho (Eprim_val x p0 e) ->
    unique_bindings_env rho (Eprim_val x p0 e) ->
    functions_not_bound p rho (Eprim_val x p0 e) ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim_val x p0 e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim_val x p0 e) rho m lenv ->
      correct_alloc (Eprim_val x p0 e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho v x p0 e n
    _ _ _ _ _ _ _ _
    stm lenv m k max_alloc fu Hrepr _ _ _.
  exfalso.
  eapply repr_expr_eprim_val_false; eauto.
Qed.

Lemma repr_bs_eprim_step_lift :
  forall p rep_env cenv ienv fenv finfo_env rho v x p0 ys e n,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Eprim x p0 ys e) v n ->
    correct_envs cenv ienv rep_env rho (Eprim x p0 ys e) ->
    protected_id_not_bound_id rho (Eprim x p0 ys e) ->
    unique_bindings_env rho (Eprim x p0 ys e) ->
    functions_not_bound p rho (Eprim x p0 ys e) ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim x p0 ys e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eprim x p0 ys e) rho m lenv ->
      correct_alloc (Eprim x p0 ys e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho v x p0 ys e n
    _ _ _ _ _ _ _ _
    stm lenv m k max_alloc fu Hrepr _ _ _.
  exfalso.
  eapply repr_expr_eprim_false; eauto.
Qed.

Definition repr_bs_currently_covered (e : exp) : Prop :=
  match e with
  | Ehalt _ => True
  | Efun _ _ => True
  | Eprim_val _ _ _ => True
  | Eprim _ _ _ _ => True
  | _ => False
  end.

Lemma repr_bs_currently_covered_step :
  forall p rep_env cenv ienv fenv finfo_env rho v e n,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho e v n ->
    correct_envs cenv ienv rep_env rho e ->
    protected_id_not_bound_id rho e ->
    unique_bindings_env rho e ->
    functions_not_bound p rho e ->
    repr_bs_currently_covered e ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
      correct_alloc e max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho v e n
    Hpinv Hsym Hfinfo Hbs Hcenvs Hprot Hub Hfnb Hcov
    stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
  destruct e; simpl in Hcov; try contradiction;
    eauto using repr_bs_halt_step_lift,
      repr_bs_efun_step_lift,
      repr_bs_eprim_val_step_lift,
      repr_bs_eprim_step_lift.
Qed.

Lemma repr_bs_main_currently_covered :
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env),
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat),
      bstep_e (M.empty _) cenv rho e v n ->
      correct_envs cenv ienv rep_env rho e ->
      protected_id_not_bound_id rho e ->
      unique_bindings_env rho e ->
      functions_not_bound p rho e ->
      repr_bs_currently_covered e ->
      forall (stm : statement) (lenv : temp_env) (m : mem) (k : cont) (max_alloc : Z) (fu : function),
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
        correct_alloc e max_alloc ->
        correct_tinfo p max_alloc lenv m ->
        exists (m' : mem) (lenv' : temp_env),
          m_tstep2 (globalenv p) (State fu stm k empty_env lenv m) (State fu Sskip k empty_env lenv' m') /\
          same_args_ptr lenv lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv fenv finfo_env ienv
    Hpinv Hsym Hfinfo rho v e n
    Hbs Hcenvs Hprot Hub Hfnb Hcov
    stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
  eapply repr_bs_currently_covered_step; eauto.
Qed.

Lemma econstr_body_step_and_invariants :
  forall p rep_env cenv ienv rho x t ys e v n,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    exists vs,
      get_list ys rho = Some vs /\
      bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n /\
      correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e /\
      protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e /\
      unique_bindings_env (M.set x (Vconstr t vs) rho) e /\
      functions_not_bound p (M.set x (Vconstr t vs) rho) e.
Proof.
  intros p rep_env cenv ienv rho x t ys e v n
    Hbs Hcenvs Hprot Hub Hfnb.
  destruct (bstep_e_econstr_inv _ _ _ _ _ _ _ _ _ Hbs)
    as [rho' [vs [Hgl [Hrho' Hbs_body]]]].
  subst rho'.
  assert (Hfnb_e : functions_not_bound p rho e).
  { eapply functions_not_bound_subterm; eauto.
    constructor. constructor. }
  exists vs.
  split; [exact Hgl|].
  split; [exact Hbs_body|].
  split.
  - eapply correct_envs_econstr_body_set; eauto.
  - split.
    + eapply protected_id_not_bound_econstr_body_set; eauto.
    + split.
      * eapply unique_bindings_env_econstr_body_set; eauto.
      * eapply functions_not_bound_set_constr; eauto.
Qed.

Lemma eproj_body_step_and_invariants :
  forall p rep_env cenv ienv rho x t n y e ov c,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    exists vs v,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e.
Proof.
  intros p rep_env cenv ienv rho x t n y e ov c
    Hbs Hcenvs Hprot Hub Hfnb.
  destruct (bstep_e_eproj_inv _ _ _ _ _ _ _ _ _ _ Hbs)
    as [vs [v [Hy [Hnth Hbs_body]]]].
  assert (Hfnb_e : functions_not_bound p rho e).
  { eapply functions_not_bound_subterm; eauto.
    constructor. constructor. }
  exists vs, v.
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_body|].
  split.
  - eapply correct_envs_eproj_body_set; eauto.
  - split.
    + eapply protected_id_not_bound_eproj_body_set; eauto.
    + split.
      * eapply unique_bindings_env_eproj_body_set; eauto.
      * eapply functions_not_bound_set_proj; eauto.
Qed.

Lemma ecase_body_step_and_invariants :
  forall p rep_env cenv ienv rho y cl v n,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    exists t vl e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e.
Proof.
  intros p rep_env cenv ienv rho y cl v n
    Hbs Hcenvs Hprot Hub Hfnb.
  destruct (bstep_e_ecase_inv _ _ _ _ _ _ _ Hbs)
    as [t [vl [e [Hy [Hcc [Hfind Hbs_e]]]]]].
  assert (Hin : List.In (t, e) cl).
  { eapply findtag_In; eauto. }
  assert (Hsub : subterm_e e (Ecase y cl)).
  { constructor. econstructor. exact Hin. }
  assert (Hhub_e : unique_bindings_env rho e).
  {
    destruct Hub as [Hub_uniq Hub_env].
    split.
    - eapply unique_bindings_Ecase_In; eauto.
    - intros x vx Hget.
      specialize (Hub_env x vx Hget) as [Hnbe Huv].
      split.
      + intro Hbve.
        eapply Hnbe.
        eapply Bound_Ecase; eauto.
      + exact Huv.
  }
  exists t, vl, e.
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split.
  - eapply correct_envs_subterm; eauto.
  - split.
    + eapply protected_id_not_bound_subterm; eauto.
    + split.
      * exact Hhub_e.
      * eapply functions_not_bound_subterm; eauto.
Qed.

Lemma ecase_step_invariants_and_repr :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n stm,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    exists t vl e ls ls',
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n stm
    Hbs Hcenvs Hprot Hub Hfnb Hrepr.
  destruct (ecase_body_step_and_invariants
              p rep_env cenv ienv rho y cl v n
              Hbs Hcenvs Hprot Hub Hfnb)
    as [t [vl [e [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e Hfnb_e]]]]]]]]]].
  destruct (repr_expr_ecase_inv _ _ _ _ _ _ _ Hrepr)
    as [ls [ls' [Hbr Hsw]]].
  exists t, vl, e, ls, ls'.
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hbr|].
  exact Hsw.
Qed.

Lemma ecase_selected_branch_stmt :
  forall p rep_env cenv ienv fenv finfo_env rho y cl t vl e ls ls' m lenv,
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
    M.get y rho = Some (Vconstr t vl) ->
    caseConsistent cenv cl t ->
    findtag cl t = Some e ->
    repr_branches_LambdaANF_Codegen
      argsIdent allocIdent limitIdent threadInfIdent tinfIdent
      isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
    exists s s',
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      ((exists arr n0,
          M.get t rep_env = Some (enum arr) /\
          repr_unboxed_Codegen arr n0 /\
          seq_of_labeled_statement (select_switch (Z.shiftr n0 1) ls') =
            Ssequence (Ssequence s Sbreak) s')
       \/
       (exists n a h,
          M.get t rep_env = Some (boxed n a) /\
          boxed_header n a h /\
          seq_of_labeled_statement (select_switch (Z.land h 255) ls) =
            Ssequence (Ssequence s Sbreak) s')).
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl t vl e ls ls' m lenv
    Hcenvs Hrel Hy Hcc Hfind Hbr.
  destruct Hcenvs as [Hienv [_ [_ Hcrep]]].
  destruct (rel_mem_ecase_get_var_or_funvar
              fenv finfo_env p rep_env rho m lenv y cl t vl Hrel Hy)
    as [L [v7 [_ [_ Hrepr_v]]]].
  destruct (repr_val_constr_cases
              fenv finfo_env p rep_env t vl m L v7 Hrepr_v)
    as [[arr [n0 [Hget_enum [Hvl [Hunboxed _]]]]]
       | [n [a [b [i [h [Hget_boxed [Hboxed _]]]]]]]].
  - subst vl.
    destruct (case_of_labeled_stm_unboxed
                rep_env arr t n0 e p fenv finfo_env ienv cenv
                Hienv Hget_enum Hcrep Hunboxed cl ls ls' Hcc Hfind Hbr)
      as [s [s' [Hsel Hrepr_e]]].
    exists s, s'.
    split; [exact Hrepr_e|].
    left.
    exists arr, n0.
    split; [exact Hget_enum|].
    split; [exact Hunboxed|].
    exact Hsel.
  - destruct (case_of_labeled_stm_boxed
                rep_env n a t h e p fenv finfo_env ienv cenv
                Hienv Hget_boxed Hcrep Hboxed cl ls ls' Hcc Hfind Hbr)
      as [s [s' [Hsel Hrepr_e]]].
    exists s, s'.
    split; [exact Hrepr_e|].
    right.
    exists n, a, h.
    split; [exact Hget_boxed|].
    split; [exact Hboxed|].
    exact Hsel.
Qed.

Lemma econstr_step_invariants_and_repr :
  forall p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
    exists vs s s',
      get_list ys rho = Some vs /\
      bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n /\
      correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e /\
      protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e /\
      unique_bindings_env (M.set x (Vconstr t vs) rho) e /\
      functions_not_bound p (M.set x (Vconstr t vs) rho) e /\
      repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env
        x t ys s /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s s'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm
    Hbs Hcenvs Hprot Hub Hfnb Hrepr.
  destruct (econstr_body_step_and_invariants
              p rep_env cenv ienv rho x t ys e v n
              Hbs Hcenvs Hprot Hub Hfnb)
    as [vs [Hgl [Hbs_e [Hcenvs_e [Hprot_e [Hub_e Hfnb_e]]]]]].
  destruct (repr_expr_econstr_inv _ _ _ _ _ _ _ _ _ Hrepr)
    as [s [s' [Hasgn [Hrepr_e Hstm]]]].
  exists vs, s, s'.
  split; [exact Hgl|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hasgn|].
  split; [exact Hrepr_e|].
  exact Hstm.
Qed.

Lemma eproj_step_invariants_and_repr :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    exists vs v s,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm
    Hbs Hcenvs Hprot Hub Hfnb Hrepr.
  destruct (eproj_body_step_and_invariants
              p rep_env cenv ienv rho x t n y e ov c
              Hbs Hcenvs Hprot Hub Hfnb)
    as [vs [v [Hy [Hnth [Hbs_e [Hcenvs_e [Hprot_e [Hub_e Hfnb_e]]]]]]]].
  destruct (repr_expr_eproj_inv _ _ _ _ _ _ _ _ _ _ Hrepr) as [s Hrepr_e].
  exists vs, v, s.
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  exact Hrepr_e.
Qed.

Lemma econstr_step_inv_repr_alloc :
  forall p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm max_alloc,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
    correct_alloc (Econstr x t ys e) max_alloc ->
    exists vs s s' max_alloc_e,
      get_list ys rho = Some vs /\
      bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n /\
      correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e /\
      protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e /\
      unique_bindings_env (M.set x (Vconstr t vs) rho) e /\
      functions_not_bound p (M.set x (Vconstr t vs) rho) e /\
      repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env x t ys s /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s s' /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc.
  destruct (econstr_step_invariants_and_repr
              p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm
              Hbs Hcenvs Hprot Hub Hfnb Hrepr)
    as [vs [s [s' [Hgl [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hasgn [Hrepr_e Hstm]]]]]]]]]]].
  destruct (correct_alloc_econstr_body x t ys e max_alloc Halloc)
    as [Halloc_bound Halloc_e].
  exists vs, s, s', (Z.of_nat (max_allocs e)).
  split; [exact Hgl|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hasgn|].
  split; [exact Hrepr_e|].
  split; [exact Hstm|].
  split; [reflexivity|].
  split; [exact Halloc_bound|].
  exact Halloc_e.
Qed.

Lemma eproj_step_inv_repr_alloc :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm max_alloc,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    exists vs v s max_alloc_e,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc.
  destruct (eproj_step_invariants_and_repr
              p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm
              Hbs Hcenvs Hprot Hub Hfnb Hrepr)
    as [vs [v [s [Hy [Hnth [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e Hrepr_e]]]]]]]]]].
  destruct (correct_alloc_eproj_body x t n y e max_alloc Halloc)
    as [Halloc_bound Halloc_e].
  exists vs, v, s, (Z.of_nat (max_allocs e)).
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [reflexivity|].
  split; [exact Halloc_bound|].
  exact Halloc_e.
Qed.

Lemma ecase_step_inv_repr_alloc :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n stm max_alloc,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    correct_alloc (Ecase y cl) max_alloc ->
    exists t vl e ls ls' max_alloc_e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n stm max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc.
  destruct (ecase_step_invariants_and_repr
              p rep_env cenv ienv fenv finfo_env rho y cl v n stm
              Hbs Hcenvs Hprot Hub Hfnb Hrepr)
    as [t [vl [e [ls [ls' [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hbr Hsw]]]]]]]]]]]]]].
  assert (Hin : List.In (t, e) cl).
  { eapply findtag_In; eauto. }
  destruct (correct_alloc_ecase_branch y cl t e max_alloc Hin Halloc)
    as [Halloc_bound Halloc_e].
  exists t, vl, e, ls, ls', (Z.of_nat (max_allocs e)).
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hbr|].
  split; [exact Hsw|].
  split; [reflexivity|].
  split; [exact Halloc_bound|].
  exact Halloc_e.
Qed.

Lemma econstr_step_inv_repr_alloc_tinfo :
  forall p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
    correct_alloc (Econstr x t ys e) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists vs s s' max_alloc_e,
      get_list ys rho = Some vs /\
      bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n /\
      correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e /\
      protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e /\
      unique_bindings_env (M.set x (Vconstr t vs) rho) e /\
      functions_not_bound p (M.set x (Vconstr t vs) rho) e /\
      repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env x t ys s /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s s' /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct.
  destruct (econstr_step_inv_repr_alloc
              p rep_env cenv ienv fenv finfo_env rho x t ys e v n stm max_alloc
              Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc)
    as [vs [s [s' [max_alloc_e
         [Hgl [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hasgn [Hrepr_e
         [Hstm [Hmaxeq [Hbound Halloc_e]]]]]]]]]]]]]]].
  subst max_alloc_e.
  exists vs, s, s', (Z.of_nat (max_allocs e)).
  split; [exact Hgl|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hasgn|].
  split; [exact Hrepr_e|].
  split; [exact Hstm|].
  split; [reflexivity|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  eapply correct_tinfo_econstr_body; eauto.
Qed.

Lemma eproj_step_inv_repr_alloc_tinfo :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists vs v s max_alloc_e,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct.
  destruct (eproj_step_inv_repr_alloc
              p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm max_alloc
              Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc)
    as [vs [v [s [max_alloc_e
         [Hy [Hnth [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hrepr_e
         [Hmaxeq [Hbound Halloc_e]]]]]]]]]]]]]].
  subst max_alloc_e.
  exists vs, v, s, (Z.of_nat (max_allocs e)).
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [reflexivity|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  eapply correct_tinfo_eproj_body; eauto.
Qed.

Lemma eproj_step_inv_repr_rel_alloc_tinfo :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists vs v s v7 max_alloc_e,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (M.set x v rho) m (M.set x v7 lenv) /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct.
  pose proof (eproj_step_inv_repr_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound Hinv].
  destruct Hinv as [Halloc_e Hct_e].
  destruct (rel_mem_eproj_body_set
              fenv finfo_env p rep_env rho m lenv x t n y e vs v
              Hrel Hprot Hfnb Hy Hnth)
    as [v7 Hrel_e].
  exists vs, v, s, v7, max_alloc_e.
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [exact Hrel_e|].
  split; [exact Hmaxeq|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  exact Hct_e.
Qed.

Lemma eproj_step_inv_repr_rel_alloc_tinfo_set :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists vs v s v7 max_alloc_e,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (M.set x v rho) m (M.set x v7 lenv) /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e (M.set x v7 lenv) m /\
      same_args_ptr lenv (M.set x v7 lenv).
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct.
  pose proof (eproj_step_inv_repr_rel_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [v7 Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hrel_e Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound Hinv].
  destruct Hinv as [Halloc_e Hct_e].
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxt.
    subst x.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  assert (Hx_neq_args : x <> argsIdent).
  {
    intro Hxa.
    subst x.
    apply Hx_not_tinfo.
    right. right. reflexivity.
  }
  assert (Hct_set : correct_tinfo p max_alloc_e (M.set x v7 lenv) m).
  { eapply correct_tinfo_not_protected; eauto. }
  assert (Hsame : same_args_ptr lenv (M.set x v7 lenv)).
  {
    eapply same_args_ptr_set_right_other; eauto.
    apply same_args_ptr_refl.
  }
  exists vs, v, s, v7, max_alloc_e.
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [exact Hrel_e|].
  split; [exact Hmaxeq|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  split; [exact Hct_set|].
  exact Hsame.
Qed.

Lemma eproj_step_inv_prefix_alloc_tinfo_set :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m k fu max_alloc,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
    correct_alloc (Eproj x t n y e) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists vs v s v7 max_alloc_e,
      M.get y rho = Some (Vconstr t vs) /\
      nthN vs n = Some v /\
      bstep_e (M.empty _) cenv (M.set x v rho) e ov c /\
      correct_envs cenv ienv rep_env (M.set x v rho) e /\
      protected_id_not_bound_id (M.set x v rho) e /\
      unique_bindings_env (M.set x v rho) e /\
      functions_not_bound p (M.set x v rho) e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu s k empty_env (M.set x v7 lenv) m) /\
      correct_tinfo p max_alloc_e (M.set x v7 lenv) m /\
      same_args_ptr lenv (M.set x v7 lenv).
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m k fu max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct.
  pose proof (eproj_step_inv_repr_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s_body Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_body Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound Hinv].
  destruct Hinv as [Halloc_e Hct_e].
  destruct (eproj_prefix_step_m_tstep2
              fenv finfo_env p rep_env rho m lenv x t n y e stm fu k vs v
              Hrepr Hrel Hy Hnth)
    as [s [v7 [L [HprotL [Hrepr_e [Hstm [Hpref Hrepr_v]]]]]]].
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxt.
    subst x.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  assert (Hx_neq_args : x <> argsIdent).
  {
    intro Hxa.
    subst x.
    apply Hx_not_tinfo.
    right. right. reflexivity.
  }
  assert (Hct_set : correct_tinfo p max_alloc_e (M.set x v7 lenv) m).
  { eapply correct_tinfo_not_protected; eauto. }
  assert (Hsame : same_args_ptr lenv (M.set x v7 lenv)).
  {
    eapply same_args_ptr_set_right_other; eauto.
    apply same_args_ptr_refl.
  }
  exists vs, v, s, v7, max_alloc_e.
  split; [exact Hy|].
  split; [exact Hnth|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [exact Hmaxeq|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  split; [exact Hpref|].
  split; [exact Hct_set|].
  exact Hsame.
Qed.

Lemma repr_bs_eproj_step_lift_from_body :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
      correct_alloc (Eproj x t n y e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall vs v s v7 max_alloc_e,
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_e (M.empty _) cenv (M.set x v rho) e ov c ->
        correct_envs cenv ienv rep_env (M.set x v rho) e ->
        protected_id_not_bound_id (M.set x v rho) e ->
        unique_bindings_env (M.set x v rho) e ->
        functions_not_bound p (M.set x v rho) e ->
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu s k empty_env (M.set x v7 lenv) m) ->
        correct_tinfo p max_alloc_e (M.set x v7 lenv) m ->
        same_args_ptr lenv (M.set x v7 lenv) ->
        exists m' lenv',
          m_tstep2 (globalenv p)
            (State fu s k empty_env (M.set x v7 lenv) m)
            (State fu Sskip k empty_env lenv' m') /\
          same_args_ptr (M.set x v7 lenv) lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov m' lenv') ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct Hbody.
  pose proof (eproj_step_inv_prefix_alloc_tinfo_set
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
                stm lenv m k fu max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [v7 Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound Hinv].
  destruct Hinv as [Halloc_e Hinv].
  destruct Hinv as [Hpref Hinv].
  destruct Hinv as [Hct_set Hsame_pref].
  pose proof (Hbody vs v s v7 max_alloc_e
               Hy Hnth Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e Hrepr_e
               Hmaxeq Hbound Halloc_e Hpref Hct_set Hsame_pref) as Hbody_post.
  eapply compose_prefix_body_result; eauto.
Qed.

Lemma repr_bs_eproj_step_lift :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c,
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    (forall rho' ov' e' c',
      bstep_e (M.empty _) cenv rho' e' ov' c' ->
      correct_envs cenv ienv rep_env rho' e' ->
      protected_id_not_bound_id rho' e' ->
      unique_bindings_env rho' e' ->
      functions_not_bound p rho' e' ->
      forall stm lenv m k max_alloc fu,
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e' stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e' rho' m lenv ->
        correct_alloc e' max_alloc ->
        correct_tinfo p max_alloc lenv m ->
        exists m' lenv',
          m_tstep2 (globalenv p)
            (State fu stm k empty_env lenv m)
            (State fu Sskip k empty_env lenv' m') /\
          same_args_ptr lenv lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov' m' lenv') ->
    forall stm lenv m k max_alloc fu,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
      correct_alloc (Eproj x t n y e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
    _ _ _ Hbs Hcenvs Hprot Hub Hfnb IH
    stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
  pose proof (eproj_step_inv_repr_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
                stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound [Halloc_e Hct_e]].
  destruct (eproj_prefix_step_m_tstep2
              fenv finfo_env p rep_env rho m lenv x t n y e stm fu k vs v
              Hrepr Hrel Hy Hnth)
    as [s_pref [v7 [L [HprotL [Hrepr_e_pref [Hstm [Hpref Hrepr_v]]]]]]].
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxt.
    subst x.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  assert (Hx_neq_args : x <> argsIdent).
  {
    intro Hxa.
    subst x.
    apply Hx_not_tinfo.
    right. right. reflexivity.
  }
  assert (Hct_set : correct_tinfo p max_alloc_e (M.set x v7 lenv) m).
  { eapply correct_tinfo_not_protected; eauto. }
  assert (Hsame_pref : same_args_ptr lenv (M.set x v7 lenv)).
  {
    eapply same_args_ptr_set_right_other; eauto.
    apply same_args_ptr_refl.
  }
  assert (Hrel_e :
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
      e (M.set x v rho) m (M.set x v7 lenv)).
  {
    eapply rel_mem_eproj_body_set_with_repr; eauto.
  }
  pose proof (IH (M.set x v rho) ov e c
                Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
                s_pref (M.set x v7 lenv) m k max_alloc_e fu
                Hrepr_e_pref Hrel_e Halloc_e Hct_set) as Hbody.
  eapply compose_prefix_body_result; eauto.
Qed.

Lemma repr_bs_eproj_step_lift_from_body_rel :
  forall p rep_env cenv ienv fenv finfo_env rho x t n y e ov c,
    bstep_e (M.empty _) cenv rho (Eproj x t n y e) ov c ->
    correct_envs cenv ienv rep_env rho (Eproj x t n y e) ->
    protected_id_not_bound_id rho (Eproj x t n y e) ->
    unique_bindings_env rho (Eproj x t n y e) ->
    functions_not_bound p rho (Eproj x t n y e) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eproj x t n y e) rho m lenv ->
      correct_alloc (Eproj x t n y e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall vs v s v7 max_alloc_e,
        M.get y rho = Some (Vconstr t vs) ->
        nthN vs n = Some v ->
        bstep_e (M.empty _) cenv (M.set x v rho) e ov c ->
        correct_envs cenv ienv rep_env (M.set x v rho) e ->
        protected_id_not_bound_id (M.set x v rho) e ->
        unique_bindings_env (M.set x v rho) e ->
        functions_not_bound p (M.set x v rho) e ->
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (M.set x v rho) m (M.set x v7 lenv) ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu s k empty_env (M.set x v7 lenv) m) ->
        correct_tinfo p max_alloc_e (M.set x v7 lenv) m ->
        same_args_ptr lenv (M.set x v7 lenv) ->
        exists m' lenv',
          m_tstep2 (globalenv p)
            (State fu s k empty_env (M.set x v7 lenv) m)
            (State fu Sskip k empty_env lenv' m') /\
          same_args_ptr (M.set x v7 lenv) lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov m' lenv') ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env ov m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct Hbody.
  pose proof (eproj_step_inv_repr_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t n y e ov c
                stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [v Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hy Hinv].
  destruct Hinv as [Hnth Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound [Halloc_e Hct_e]].
  destruct (eproj_prefix_step_m_tstep2
              fenv finfo_env p rep_env rho m lenv x t n y e stm fu k vs v
              Hrepr Hrel Hy Hnth)
    as [s_pref [v7 [L [HprotL [Hrepr_e_pref [Hstm [Hpref Hrepr_v]]]]]]].
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eproj_head; eauto. }
  assert (Hx_not_tinfo : ~ is_protected_tinfo_id_thm x).
  {
    intro Hxt.
    apply Hx_not_prot.
    eapply is_protected_tinfo_weak; eauto.
  }
  assert (Hx_neq_tinf : x <> tinfIdent).
  {
    intro Hxt.
    subst x.
    apply Hx_not_prot.
    unfold is_protected_id_thm, is_protected_id, protectedIdent_thm, protectedIdent.
    inList.
  }
  assert (Hx_neq_args : x <> argsIdent).
  {
    intro Hxa.
    subst x.
    apply Hx_not_tinfo.
    right. right. reflexivity.
  }
  assert (Hct_set : correct_tinfo p max_alloc_e (M.set x v7 lenv) m).
  { eapply correct_tinfo_not_protected; eauto. }
  assert (Hsame_pref : same_args_ptr lenv (M.set x v7 lenv)).
  {
    eapply same_args_ptr_set_right_other; eauto.
    apply same_args_ptr_refl.
  }
  assert (Hrel_e :
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
      e (M.set x v rho) m (M.set x v7 lenv)).
  {
    eapply rel_mem_eproj_body_set_with_repr; eauto.
  }
  pose proof (Hbody vs v s_pref v7 max_alloc_e
                Hy Hnth Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
                Hrepr_e_pref Hrel_e Hmaxeq Hbound Halloc_e
                Hpref Hct_set Hsame_pref) as Hbody_post.
  eapply compose_prefix_body_result; eauto.
Qed.

Lemma repr_bs_econstr_step_lift_from_body_rel :
  forall p rep_env cenv ienv fenv finfo_env rho x t ys e v n,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) rho m lenv ->
      correct_alloc (Econstr x t ys e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall vs s s' max_alloc_e,
        get_list ys rho = Some vs ->
        bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n ->
        correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e ->
        protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e ->
        unique_bindings_env (M.set x (Vconstr t vs) rho) e ->
        functions_not_bound p (M.set x (Vconstr t vs) rho) e ->
        repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env x t ys s ->
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' ->
        stm = Ssequence s s' ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        correct_tinfo p max_alloc_e lenv m ->
        exists m_mid lenv_mid,
          m_tstep2 (globalenv p)
            (State fu stm k empty_env lenv m)
            (State fu s' k empty_env lenv_mid m_mid) /\
          same_args_ptr lenv lenv_mid /\
          rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
            e (M.set x (Vconstr t vs) rho) m_mid lenv_mid /\
          exists m' lenv',
            m_tstep2 (globalenv p)
              (State fu s' k empty_env lenv_mid m_mid)
              (State fu Sskip k empty_env lenv' m') /\
            same_args_ptr lenv_mid lenv' /\
            arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv') ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t ys e v n
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct Hbody.
  pose proof (econstr_step_inv_repr_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho x t ys e v n
                stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct) as Hinv.
  destruct Hinv as [vs Hinv].
  destruct Hinv as [s Hinv].
  destruct Hinv as [s' Hinv].
  destruct Hinv as [max_alloc_e Hinv].
  destruct Hinv as [Hgl Hinv].
  destruct Hinv as [Hbs_e Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hasgn Hinv].
  destruct Hinv as [Hrepr_e Hinv].
  destruct Hinv as [Hstm Hinv].
  destruct Hinv as [Hmaxeq Hinv].
  destruct Hinv as [Hbound [Halloc_e Hct_e]].
  destruct (Hbody vs s s' max_alloc_e
              Hgl Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
              Hasgn Hrepr_e Hstm Hmaxeq Hbound Halloc_e Hct_e)
    as [m_mid [lenv_mid [Hpref [Hsame [_ Hbody_post]]]]].
  eapply (compose_prefix_body_result_gen
            fenv finfo_env p rep_env v fu stm s' k lenv lenv_mid m m_mid); eauto.
Qed.

Lemma ecase_step_inv_repr_alloc_tinfo :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    correct_alloc (Ecase y cl) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists t vl e ls ls' max_alloc_e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct.
  destruct (ecase_step_inv_repr_alloc
              p rep_env cenv ienv fenv finfo_env rho y cl v n stm max_alloc
              Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc)
    as [t [vl [e [ls [ls' [max_alloc_e
         [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hbr [Hsw
         [Hmaxeq [Hbound Halloc_e]]]]]]]]]]]]]]]]]].
  subst max_alloc_e.
  exists t, vl, e, ls, ls', (Z.of_nat (max_allocs e)).
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hbr|].
  split; [exact Hsw|].
  split; [reflexivity|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  eapply correct_tinfo_ecase_branch; eauto.
  eapply findtag_In; eauto.
Qed.

Lemma ecase_step_inv_repr_rel_alloc_tinfo :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
    correct_alloc (Ecase y cl) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists t vl e ls ls' max_alloc_e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm /\
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct.
  destruct (ecase_step_inv_repr_alloc_tinfo
              p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc
              Hbs Hcenvs Hprot Hub Hfnb Hrepr Halloc Hct)
    as [t [vl [e [ls [ls' [max_alloc_e
         [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hbr [Hsw
         [Hmaxeq [Hbound [Halloc_e Hct_e]]]]]]]]]]]]]]]]]]].
  assert (Hrel_e :
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv).
  { eapply rel_mem_ecase_branch; eauto. }
  exists t, vl, e, ls, ls', max_alloc_e.
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hbr|].
  split; [exact Hsw|].
  split; [exact Hrel_e|].
  split; [exact Hmaxeq|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  exact Hct_e.
Qed.

Lemma repr_bs_ecase_step_lift_from_branch_rel :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
      correct_alloc (Ecase y cl) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall t vl e ls ls' max_alloc_e,
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        findtag cl t = Some e ->
        bstep_e (M.empty _) cenv rho e v n ->
        correct_envs cenv ienv rep_env rho e ->
        protected_id_not_bound_id rho e ->
        unique_bindings_env rho e ->
        functions_not_bound p rho e ->
        repr_branches_LambdaANF_Codegen
          argsIdent allocIdent limitIdent threadInfIdent tinfIdent
          isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
        repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        correct_tinfo p max_alloc_e lenv m ->
        exists s,
          repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
          m_tstep2 (globalenv p)
            (State fu stm k empty_env lenv m)
            (State fu s k empty_env lenv m) /\
          exists m' lenv',
            m_tstep2 (globalenv p)
              (State fu s k empty_env lenv m)
              (State fu Sskip k empty_env lenv' m') /\
            same_args_ptr lenv lenv' /\
            arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv') ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct Hbody.
  pose proof (ecase_step_inv_repr_rel_alloc_tinfo
                p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc
                Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct) as Hinv.
  destruct Hinv as [t [vl [e [ls [ls' [max_alloc_e
    [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hbr [Hsw [Hrel_e
    [Hmaxeq [Hbound [Halloc_e Hct_e]]]]]]]]]]]]]]]]]]]].
  destruct (Hbody t vl e ls ls' max_alloc_e
              Hy Hcc Hfind Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
              Hbr Hsw Hrel_e Hmaxeq Hbound Halloc_e Hct_e)
    as [s [Hrepr_s [Hpref Hpost]]].
  destruct Hpost as [m' [lenv' [Hstep_body [Hsame Harg]]]].
  exists m', lenv'.
  split.
  - eapply m_tstep2_transitive; eauto.
  - split; [exact Hsame|exact Harg].
Qed.

Lemma ecase_step_inv_repr_rel_alloc_tinfo_set_temp :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc tmp vtmp,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
    correct_alloc (Ecase y cl) max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    is_protected_id_thm tmp ->
    ~ is_protected_tinfo_id_thm tmp ->
    tmp <> tinfIdent ->
    exists t vl e ls ls' max_alloc_e,
      M.get y rho = Some (Vconstr t vl) /\
      caseConsistent cenv cl t /\
      findtag cl t = Some e /\
      bstep_e (M.empty _) cenv rho e v n /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_branches_LambdaANF_Codegen
        argsIdent allocIdent limitIdent threadInfIdent tinfIdent
        isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' /\
      repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm /\
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m (M.set tmp vtmp lenv) /\
      max_alloc_e = Z.of_nat (max_allocs e) /\
      (0 <= max_alloc_e <= max_alloc)%Z /\
      correct_alloc e max_alloc_e /\
      correct_tinfo p max_alloc_e lenv m.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc tmp vtmp
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct Htmp Htmp_tinfo Htmp_neq_tinf.
  destruct (ecase_step_inv_repr_rel_alloc_tinfo
              p rep_env cenv ienv fenv finfo_env rho y cl v n stm lenv m max_alloc
              Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel Halloc Hct)
    as [t [vl [e [ls [ls' [max_alloc_e
         [Hy [Hcc [Hfind [Hbs_e [Hcenvs_e [Hprot_e [Hub_e [Hfnb_e [Hbr [Hsw
         [Hrel_e [Hmaxeq [Hbound [Halloc_e Hct_e]]]]]]]]]]]]]]]]]]]].
  assert (Hrel_set :
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m
      (M.set tmp vtmp lenv)).
  { eapply rel_mem_set_protected_id; eauto. }
  exists t, vl, e, ls, ls', max_alloc_e.
  split; [exact Hy|].
  split; [exact Hcc|].
  split; [exact Hfind|].
  split; [exact Hbs_e|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hbr|].
  split; [exact Hsw|].
  split; [exact Hrel_set|].
  split; [exact Hmaxeq|].
  split; [exact Hbound|].
  split; [exact Halloc_e|].
  exact Hct_e.
Qed.

Lemma eletapp_cont_subterm_invariants :
  forall p rep_env cenv ienv rho x f t ys e,
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    unique_bindings_env rho (Eletapp x f t ys e) ->
    functions_not_bound p rho (Eletapp x f t ys e) ->
    correct_envs cenv ienv rep_env rho e /\
    protected_id_not_bound_id rho e /\
    unique_bindings_env rho e /\
    functions_not_bound p rho e.
Proof.
  intros p rep_env cenv ienv rho x f t ys e
    Hcenvs Hprot Hub Hfnb.
  assert (Hsub : subterm_e e (Eletapp x f t ys e)).
  { apply t_step. apply dsubterm_letapp. }
  assert (Hub_e : unique_bindings_env rho e).
  {
    destruct Hub as [Hub_exp Hub_env].
    split.
    - inversion Hub_exp; subst; assumption.
    - intros z vz Hget.
      specialize (Hub_env z vz Hget) as [Hnb Huv].
      split.
      + intro Hbve.
        eapply Hnb.
        eapply Bound_Eletapp2; eauto.
      + exact Huv.
  }
  split.
  - eapply correct_envs_subterm; eauto.
  - split.
    + eapply protected_id_not_bound_subterm; eauto.
    + split.
      * exact Hub_e.
      * eapply functions_not_bound_subterm; eauto.
Qed.

Lemma eletapp_cont_correct_envs_set :
  forall cenv ienv rep_env rho x f t ys e v_body,
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    correct_cenv_of_val cenv v_body ->
    correct_envs cenv ienv rep_env (M.set x v_body rho) e.
Proof.
  intros cenv ienv rep_env rho x f t ys e v_body Hcenvs Hcv.
  assert (Hsub : subterm_e e (Eletapp x f t ys e)).
  { apply t_step. apply dsubterm_letapp. }
  assert (Hcenvs_e : correct_envs cenv ienv rep_env rho e).
  { eapply correct_envs_subterm; [exact Hcenvs | exact Hsub]. }
  eapply correct_envs_set; eauto.
Qed.

Lemma eletapp_cont_protected_set :
  forall rho x f t ys e v_body,
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    (forall y, is_protected_id_thm y -> ~ bound_var_val v_body y) ->
    protected_id_not_bound_id (M.set x v_body rho) e.
Proof.
  intros rho x f t ys e v_body Hprot Hvb.
  assert (Hsub : subterm_e e (Eletapp x f t ys e)).
  { apply t_step. apply dsubterm_letapp. }
  assert (Hprot_e : protected_id_not_bound_id rho e).
  { eapply protected_id_not_bound_subterm; [exact Hprot | exact Hsub]. }
  assert (Hx_not_prot : ~ is_protected_id_thm x).
  { eapply protected_id_not_bound_eletapp_head; eauto. }
  eapply protected_id_not_bound_set; eauto.
Qed.

Lemma eletapp_cont_functions_not_bound_set :
  forall p rho x f t ys e v_body,
    functions_not_bound p rho (Eletapp x f t ys e) ->
    (forall z, bound_notfun_val v_body z ->
               Genv.find_symbol (globalenv p) z = None) ->
    functions_not_bound p (M.set x v_body rho) e.
Proof.
  intros p rho x f t ys e v_body Hfnb Hv.
  assert (Hsub : subterm_e e (Eletapp x f t ys e)).
  { apply t_step. apply dsubterm_letapp. }
  assert (Hfnb_e : functions_not_bound p rho e).
  { eapply functions_not_bound_subterm; [exact Hfnb | exact Hsub]. }
  eapply functions_not_bound_set; eauto.
Qed.

Lemma eletapp_cont_unique_bindings_set :
  forall rho x f t ys e v_body,
    unique_bindings_env rho (Eletapp x f t ys e) ->
    unique_bindings_val v_body ->
    unique_bindings_env (M.set x v_body rho) e.
Proof.
  intros rho x f t ys e v_body Hub Huv_body.
  destruct Hub as [Hub_exp Hub_env].
  inversion Hub_exp; subst.
  assert (Hub_e : unique_bindings_env rho e).
  {
    split.
    - assumption.
    - intros z vz Hget.
      specialize (Hub_env z vz Hget) as [Hnb_whole Huv].
      split.
      + intro Hbve.
        eapply Hnb_whole.
        eapply Bound_Eletapp2; eauto.
      + exact Huv.
  }
  match goal with
  | Hx_not_bound : ~ bound_var e x |- _ =>
      eapply unique_bindings_env_set; [exact Hub_e | exact Hx_not_bound | exact Huv_body]
  end.
Qed.

Lemma eletapp_cont_all_invariants_set :
  forall p rep_env cenv ienv rho x f t ys e v_body,
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    unique_bindings_env rho (Eletapp x f t ys e) ->
    functions_not_bound p rho (Eletapp x f t ys e) ->
    correct_cenv_of_val cenv v_body ->
    (forall y, is_protected_id_thm y -> ~ bound_var_val v_body y) ->
    unique_bindings_val v_body ->
    (forall z, bound_notfun_val v_body z ->
               Genv.find_symbol (globalenv p) z = None) ->
    correct_envs cenv ienv rep_env (M.set x v_body rho) e /\
    protected_id_not_bound_id (M.set x v_body rho) e /\
    unique_bindings_env (M.set x v_body rho) e /\
    functions_not_bound p (M.set x v_body rho) e.
Proof.
  intros p rep_env cenv ienv rho x f t ys e v_body
    Hcenvs Hprot Hub Hfnb Hcv Hvb Huv Hvf.
  split.
  - eapply eletapp_cont_correct_envs_set; eauto.
  - split.
    + eapply eletapp_cont_protected_set; eauto.
    + split.
      * eapply eletapp_cont_unique_bindings_set; eauto.
      * eapply eletapp_cont_functions_not_bound_set; eauto.
Qed.

Lemma eapp_step_and_repr_inv :
  forall p rep_env cenv fenv finfo_env rho f t ys v n stm,
    bstep_e (M.empty _) cenv rho (Eapp f t ys) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) stm ->
    exists rho_clo fl f' vs xs e rho_call c s_pref s_tail,
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e v c /\
      n = c + 1 /\
      stm = Ssequence s_pref s_tail.
Proof.
  intros p rep_env cenv fenv finfo_env rho f t ys v n stm Hbs Hrepr.
  pose proof (bstep_e_eapp_inv _ _ _ _ _ _ _ _ Hbs) as Hbs_inv.
  destruct Hbs_inv as [rho_clo Hbs_inv].
  destruct Hbs_inv as [fl Hbs_inv].
  destruct Hbs_inv as [f' Hbs_inv].
  destruct Hbs_inv as [vs Hbs_inv].
  destruct Hbs_inv as [xs Hbs_inv].
  destruct Hbs_inv as [e Hbs_inv].
  destruct Hbs_inv as [rho_call Hbs_inv].
  destruct Hbs_inv as [c [Hgetf [Hgetys [Hfind [Hset [Hbs_e Hn]]]]]].
  destruct (repr_expr_eapp_inv _ _ _ _ _ _ _ _ Hrepr) as [s_pref [s_tail Hstm]].
  exists rho_clo, fl, f', vs, xs, e, rho_call, c, s_pref, s_tail.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_e|].
  split; [exact Hn|].
  exact Hstm.
Qed.

Lemma eapp_step_and_repr_with_body_cenv :
  forall p rep_env cenv ienv fenv finfo_env rho f t ys v n stm,
    bstep_e (M.empty _) cenv rho (Eapp f t ys) v n ->
    correct_envs cenv ienv rep_env rho (Eapp f t ys) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) stm ->
    exists rho_clo fl f' vs xs e_body rho_call c s_pref s_tail,
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v c /\
      n = c + 1 /\
      correct_cenv_of_exp cenv e_body /\
      stm = Ssequence s_pref s_tail.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho f t ys v n stm
    Hbs Hcenvs Hrepr.
  destruct (eapp_step_and_repr_inv
              p rep_env cenv fenv finfo_env rho f t ys v n stm Hbs Hrepr)
    as [rho_clo [fl [f' [vs [xs [e_body [rho_call [c [s_pref [s_tail
         [Hgetf [Hgetys [Hfind [Hset [Hbs_body [Hn Hstm]]]]]]]]]]]]]]]].
  destruct Hcenvs as [_ [Hcenv_rho _]].
  assert (Hcenv_e : correct_cenv_of_exp cenv e_body).
  { eapply correct_cenv_of_exp_find_def_from_env; eauto. }
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, c, s_pref, s_tail.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hn|].
  split; [exact Hcenv_e|].
  exact Hstm.
Qed.

Lemma eapp_step_and_repr_rel_fun_inv :
  forall p rep_env cenv ienv fenv finfo_env rho f t ys v n stm m lenv,
    bstep_e (M.empty _) cenv rho (Eapp f t ys) v n ->
    correct_envs cenv ienv rep_env rho (Eapp f t ys) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eapp f t ys) rho m lenv ->
    exists rho_clo fl f' vs xs e_body rho_call c s_pref s_tail L,
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v c /\
      n = c + 1 /\
      correct_cenv_of_exp cenv e_body /\
      stm = Ssequence s_pref s_tail /\
      protected_not_in_L_id p lenv L /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env
        (Vfun rho_clo fl f') m L lenv f' /\
      closed_val (Vfun rho_clo fl f') /\
      correct_fundef_id_info fenv finfo_env p m fl f'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho f t ys v n stm m lenv
    Hbs Hcenvs Hrepr Hrel.
  pose proof (eapp_step_and_repr_with_body_cenv
                p rep_env cenv ienv fenv finfo_env rho f t ys v n stm
                Hbs Hcenvs Hrepr) as Hinv.
  destruct Hinv as [rho_clo Hinv].
  destruct Hinv as [fl Hinv].
  destruct Hinv as [f' Hinv].
  destruct Hinv as [vs Hinv].
  destruct Hinv as [xs Hinv].
  destruct Hinv as [e_body Hinv].
  destruct Hinv as [rho_call Hinv].
  destruct Hinv as [c Hinv].
  destruct Hinv as [s_pref Hinv].
  destruct Hinv as [s_tail Hinv].
  destruct Hinv as [Hgetf Hinv].
  destruct Hinv as [Hgetys Hinv].
  destruct Hinv as [Hfind Hinv].
  destruct Hinv as [Hset Hinv].
  destruct Hinv as [Hbs_body Hinv].
  destruct Hinv as [Hn Hinv].
  destruct Hinv as [Hcenv_body Hstm].
  destruct (rel_mem_fun_get_info
              fenv finfo_env p rep_env (Eapp f t ys) rho m lenv
              f rho_clo fl f' Hrel Hgetf)
    as [L [HprotL [Hrepr_fun [Hclosed_fun Hfundef_info]]]].
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, c, s_pref, s_tail, L.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hn|].
  split; [exact Hcenv_body|].
  split; [exact Hstm|].
  split; [exact HprotL|].
  split; [exact Hrepr_fun|].
  split; [exact Hclosed_fun|].
  exact Hfundef_info.
Qed.

Lemma eletapp_step_and_repr_inv :
  forall p rep_env cenv fenv finfo_env rho x f t ys e v n stm,
    bstep_e (M.empty _) cenv rho (Eletapp x f t ys e) v n ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    exists rho_clo fl f' vs xs e_body rho_call v_body c c' s_pref s',
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v_body c /\
      bstep_e (M.empty _) cenv (M.set x v_body rho) e v c' /\
      n = c + c' + 1 /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s_pref s'.
Proof.
  intros p rep_env cenv fenv finfo_env rho x f t ys e v n stm Hbs Hrepr.
  pose proof (bstep_e_eletapp_inv _ _ _ _ _ _ _ _ _ _ Hbs) as Hbs_inv.
  destruct Hbs_inv as [rho_clo Hbs_inv].
  destruct Hbs_inv as [fl Hbs_inv].
  destruct Hbs_inv as [f' Hbs_inv].
  destruct Hbs_inv as [vs Hbs_inv].
  destruct Hbs_inv as [xs Hbs_inv].
  destruct Hbs_inv as [e_body Hbs_inv].
  destruct Hbs_inv as [rho_call Hbs_inv].
  destruct Hbs_inv as [v_body Hbs_inv].
  destruct Hbs_inv as [c Hbs_inv].
  destruct Hbs_inv as [c' [Hgetf [Hgetys [Hfind [Hset [Hbs_body [Hbs_cont Hn]]]]]]].
  destruct (repr_expr_eletapp_inv _ _ _ _ _ _ _ _ _ _ Hrepr)
    as [s' [s_pref [Hrepr_e Hstm]]].
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, v_body, c, c', s_pref, s'.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hbs_cont|].
  split; [exact Hn|].
  split; [exact Hrepr_e|].
  exact Hstm.
Qed.

Lemma eletapp_step_and_repr_with_body_cenv :
  forall p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm,
    bstep_e (M.empty _) cenv rho (Eletapp x f t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    exists rho_clo fl f' vs xs e_body rho_call v_body c c' s_pref s',
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v_body c /\
      bstep_e (M.empty _) cenv (M.set x v_body rho) e v c' /\
      n = c + c' + 1 /\
      correct_cenv_of_exp cenv e_body /\
      correct_cenv_of_exp cenv e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s_pref s'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm
    Hbs Hcenvs Hrepr.
  destruct (eletapp_step_and_repr_inv
              p rep_env cenv fenv finfo_env rho x f t ys e v n stm Hbs Hrepr)
    as [rho_clo [fl [f' [vs [xs [e_body [rho_call [v_body [c [c' [s_pref [s'
         [Hgetf [Hgetys [Hfind [Hset [Hbs_body [Hbs_cont [Hn [Hrepr_e Hstm]]]]]]]]]]]]]]]]]]]].
  assert (Hsub_e : subterm_e e (Eletapp x f t ys e)).
  { apply t_step. apply dsubterm_letapp. }
  assert (Hcenvs_e : correct_envs cenv ienv rep_env rho e).
  { eapply correct_envs_subterm; [exact Hcenvs | exact Hsub_e]. }
  destruct Hcenvs as [_ [Hcenv_rho _]].
  assert (Hcenv_body : correct_cenv_of_exp cenv e_body).
  { eapply correct_cenv_of_exp_find_def_from_env; eauto. }
  destruct Hcenvs_e as [_ [_ [Hcenv_e _]]].
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, v_body, c, c', s_pref, s'.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hbs_cont|].
  split; [exact Hn|].
  split; [exact Hcenv_body|].
  split; [exact Hcenv_e|].
  split; [exact Hrepr_e|].
  exact Hstm.
Qed.

Lemma eletapp_step_and_repr_cont_invariants :
  forall p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm,
    bstep_e (M.empty _) cenv rho (Eletapp x f t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    unique_bindings_env rho (Eletapp x f t ys e) ->
    functions_not_bound p rho (Eletapp x f t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    exists rho_clo fl f' vs xs e_body rho_call v_body c c' s_pref s',
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v_body c /\
      bstep_e (M.empty _) cenv (M.set x v_body rho) e v c' /\
      n = c + c' + 1 /\
      correct_cenv_of_exp cenv e_body /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s_pref s'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm
    Hbs Hcenvs Hprot Hub Hfnb Hrepr.
  pose proof (eletapp_step_and_repr_with_body_cenv
                p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm
                Hbs Hcenvs Hrepr) as Hinv.
  destruct Hinv as [rho_clo Hinv].
  destruct Hinv as [fl Hinv].
  destruct Hinv as [f' Hinv].
  destruct Hinv as [vs Hinv].
  destruct Hinv as [xs Hinv].
  destruct Hinv as [e_body Hinv].
  destruct Hinv as [rho_call Hinv].
  destruct Hinv as [v_body Hinv].
  destruct Hinv as [c Hinv].
  destruct Hinv as [c' Hinv].
  destruct Hinv as [s_pref Hinv].
  destruct Hinv as [s' Hinv].
  destruct Hinv as [Hgetf Hinv].
  destruct Hinv as [Hgetys Hinv].
  destruct Hinv as [Hfind Hinv].
  destruct Hinv as [Hset Hinv].
  destruct Hinv as [Hbs_body Hinv].
  destruct Hinv as [Hbs_cont Hinv].
  destruct Hinv as [Hn Hinv].
  destruct Hinv as [Hcenv_body Hinv].
  destruct Hinv as [Hcenv_e Hinv].
  destruct Hinv as [Hrepr_e Hstm].
  destruct (eletapp_cont_subterm_invariants
              p rep_env cenv ienv rho x f t ys e Hcenvs Hprot Hub Hfnb)
    as [Hcenvs_e [Hprot_e [Hub_e Hfnb_e]]].
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, v_body, c, c', s_pref, s'.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hbs_cont|].
  split; [exact Hn|].
  split; [exact Hcenv_body|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  exact Hstm.
Qed.

Lemma eletapp_step_and_repr_rel_fun_cont_inv :
  forall p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm m lenv,
    bstep_e (M.empty _) cenv rho (Eletapp x f t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Eletapp x f t ys e) ->
    protected_id_not_bound_id rho (Eletapp x f t ys e) ->
    unique_bindings_env rho (Eletapp x f t ys e) ->
    functions_not_bound p rho (Eletapp x f t ys e) ->
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Eletapp x f t ys e) rho m lenv ->
    exists rho_clo fl f' vs xs e_body rho_call v_body c c' s_pref s' L,
      M.get f rho = Some (Vfun rho_clo fl f') /\
      get_list ys rho = Some vs /\
      find_def f' fl = Some (t, xs, e_body) /\
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call /\
      bstep_e (M.empty _) cenv rho_call e_body v_body c /\
      bstep_e (M.empty _) cenv (M.set x v_body rho) e v c' /\
      n = c + c' + 1 /\
      correct_cenv_of_exp cenv e_body /\
      correct_envs cenv ienv rep_env rho e /\
      protected_id_not_bound_id rho e /\
      unique_bindings_env rho e /\
      functions_not_bound p rho e /\
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' /\
      stm = Ssequence s_pref s' /\
      protected_not_in_L_id p lenv L /\
      repr_val_id_L_LambdaANF_Codegen_id fenv finfo_env p rep_env
        (Vfun rho_clo fl f') m L lenv f' /\
      closed_val (Vfun rho_clo fl f') /\
      correct_fundef_id_info fenv finfo_env p m fl f'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm m lenv
    Hbs Hcenvs Hprot Hub Hfnb Hrepr Hrel.
  pose proof (eletapp_step_and_repr_cont_invariants
                p rep_env cenv ienv fenv finfo_env rho x f t ys e v n stm
                Hbs Hcenvs Hprot Hub Hfnb Hrepr) as Hinv.
  destruct Hinv as [rho_clo Hinv].
  destruct Hinv as [fl Hinv].
  destruct Hinv as [f' Hinv].
  destruct Hinv as [vs Hinv].
  destruct Hinv as [xs Hinv].
  destruct Hinv as [e_body Hinv].
  destruct Hinv as [rho_call Hinv].
  destruct Hinv as [v_body Hinv].
  destruct Hinv as [c Hinv].
  destruct Hinv as [c' Hinv].
  destruct Hinv as [s_pref Hinv].
  destruct Hinv as [s' Hinv].
  destruct Hinv as [Hgetf Hinv].
  destruct Hinv as [Hgetys Hinv].
  destruct Hinv as [Hfind Hinv].
  destruct Hinv as [Hset Hinv].
  destruct Hinv as [Hbs_body Hinv].
  destruct Hinv as [Hbs_cont Hinv].
  destruct Hinv as [Hn Hinv].
  destruct Hinv as [Hcenv_body Hinv].
  destruct Hinv as [Hcenvs_e Hinv].
  destruct Hinv as [Hprot_e Hinv].
  destruct Hinv as [Hub_e Hinv].
  destruct Hinv as [Hfnb_e Hinv].
  destruct Hinv as [Hrepr_e Hstm].
  destruct (rel_mem_fun_get_info
              fenv finfo_env p rep_env (Eletapp x f t ys e) rho m lenv
              f rho_clo fl f' Hrel Hgetf)
    as [L [HprotL [Hrepr_fun [Hclosed_fun Hfundef_info]]]].
  exists rho_clo, fl, f', vs, xs, e_body, rho_call, v_body, c, c', s_pref, s', L.
  split; [exact Hgetf|].
  split; [exact Hgetys|].
  split; [exact Hfind|].
  split; [exact Hset|].
  split; [exact Hbs_body|].
  split; [exact Hbs_cont|].
  split; [exact Hn|].
  split; [exact Hcenv_body|].
  split; [exact Hcenvs_e|].
  split; [exact Hprot_e|].
  split; [exact Hub_e|].
  split; [exact Hfnb_e|].
  split; [exact Hrepr_e|].
  split; [exact Hstm|].
  split; [exact HprotL|].
  split; [exact Hrepr_fun|].
  split; [exact Hclosed_fun|].
  exact Hfundef_info.
Qed.

Definition repr_bs_goal
  (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
  (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env)
  (rho : eval.env) (v : cps.val) (e : exp) (n : nat) : Prop :=
  correct_envs cenv ienv rep_env rho e ->
  protected_id_not_bound_id rho e ->
  unique_bindings_env rho e ->
  functions_not_bound p rho e ->
  forall (stm : statement) (lenv : temp_env) (m : mem) (k : cont) (max_alloc : Z) (fu : function),
    repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm ->
    rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
    correct_alloc e max_alloc ->
    correct_tinfo p max_alloc lenv m ->
    exists (m' : mem) (lenv' : temp_env),
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu Sskip k empty_env lenv' m') /\
      same_args_ptr lenv lenv' /\
      arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.

Lemma repr_bs_goal_after_prefix :
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env)
         (rho : eval.env) (v : cps.val) (e : exp) (n : nat),
    repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v e n ->
    correct_envs cenv ienv rep_env rho e ->
    protected_id_not_bound_id rho e ->
    unique_bindings_env rho e ->
    functions_not_bound p rho e ->
    forall (fu : function) (k : cont) (stm s : statement)
           (lenv lenv_mid : temp_env) (m m_mid : mem) (max_alloc : Z),
      m_tstep2 (globalenv p)
        (State fu stm k empty_env lenv m)
        (State fu s k empty_env lenv_mid m_mid) ->
      same_args_ptr lenv lenv_mid ->
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m_mid lenv_mid ->
      correct_alloc e max_alloc ->
      correct_tinfo p max_alloc lenv_mid m_mid ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv fenv finfo_env ienv rho v e n
    Hgoal Hcenvs Hprot Hub Hfnb
    fu k stm s lenv lenv_mid m m_mid max_alloc
    Hpref Hsame Hrepr Hrel Halloc Hct.
  pose proof (Hgoal Hcenvs Hprot Hub Hfnb
                s lenv_mid m_mid k max_alloc fu
                Hrepr Hrel Halloc Hct) as Hbody.
  eapply (compose_prefix_body_result_gen
            fenv finfo_env p rep_env v fu stm s k lenv lenv_mid m m_mid); eauto.
Qed.

Lemma repr_bs_econstr_step_lift_from_body_goal :
  forall p rep_env cenv ienv fenv finfo_env rho x t ys e v n,
    bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
    correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
    protected_id_not_bound_id rho (Econstr x t ys e) ->
    unique_bindings_env rho (Econstr x t ys e) ->
    functions_not_bound p rho (Econstr x t ys e) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) rho m lenv ->
      correct_alloc (Econstr x t ys e) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall vs s s' max_alloc_e,
        get_list ys rho = Some vs ->
        bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n ->
        correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e ->
        protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e ->
        unique_bindings_env (M.set x (Vconstr t vs) rho) e ->
        functions_not_bound p (M.set x (Vconstr t vs) rho) e ->
        repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env x t ys s ->
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' ->
        stm = Ssequence s s' ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        correct_tinfo p max_alloc_e lenv m ->
        exists m_mid lenv_mid,
          m_tstep2 (globalenv p)
            (State fu stm k empty_env lenv m)
            (State fu s' k empty_env lenv_mid m_mid) /\
          same_args_ptr lenv lenv_mid /\
          rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
            e (M.set x (Vconstr t vs) rho) m_mid lenv_mid /\
          correct_tinfo p max_alloc_e lenv_mid m_mid) ->
      (forall vs,
        get_list ys rho = Some vs ->
        repr_bs_goal p rep_env cenv fenv finfo_env ienv
          (M.set x (Vconstr t vs) rho) v e n) ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho x t ys e v n
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct
    Hprefix Hgoal_body.
  eapply repr_bs_econstr_step_lift_from_body_rel; eauto.
  intros vs s s' max_alloc_e
    Hgl Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
    Hasgn Hrepr_e Hstm Hmaxeq Hbound Halloc_e Hct_e.
  destruct (Hprefix vs s s' max_alloc_e
              Hgl Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
              Hasgn Hrepr_e Hstm Hmaxeq Hbound Halloc_e Hct_e)
    as [m_mid [lenv_mid [Hpref [Hsame [Hrel_e Hct_mid]]]]].
  pose proof (Hgoal_body vs Hgl) as Hgoal_vs.
  pose proof (Hgoal_vs Hcenvs_e Hprot_e Hub_e Hfnb_e
                s' lenv_mid m_mid k max_alloc_e fu
                Hrepr_e Hrel_e Halloc_e Hct_mid) as Hbody.
  exists m_mid, lenv_mid.
  split; [exact Hpref|].
  split; [exact Hsame|].
  split; [exact Hrel_e|].
  exact Hbody.
Qed.

Lemma repr_bs_ecase_step_lift_from_branch_goal :
  forall p rep_env cenv ienv fenv finfo_env rho y cl v n,
    bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
    correct_envs cenv ienv rep_env rho (Ecase y cl) ->
    protected_id_not_bound_id rho (Ecase y cl) ->
    unique_bindings_env rho (Ecase y cl) ->
    functions_not_bound p rho (Ecase y cl) ->
    forall stm lenv m k fu max_alloc,
      repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
      rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
      correct_alloc (Ecase y cl) max_alloc ->
      correct_tinfo p max_alloc lenv m ->
      (forall t vl e ls ls' max_alloc_e,
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        findtag cl t = Some e ->
        bstep_e (M.empty _) cenv rho e v n ->
        correct_envs cenv ienv rep_env rho e ->
        protected_id_not_bound_id rho e ->
        unique_bindings_env rho e ->
        functions_not_bound p rho e ->
        repr_branches_LambdaANF_Codegen
          argsIdent allocIdent limitIdent threadInfIdent tinfIdent
          isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
        repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
        max_alloc_e = Z.of_nat (max_allocs e) ->
        (0 <= max_alloc_e <= max_alloc)%Z ->
        correct_alloc e max_alloc_e ->
        correct_tinfo p max_alloc_e lenv m ->
        exists s,
          repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
          m_tstep2 (globalenv p)
            (State fu stm k empty_env lenv m)
            (State fu s k empty_env lenv m)) ->
      (forall t vl e,
        M.get y rho = Some (Vconstr t vl) ->
        caseConsistent cenv cl t ->
        findtag cl t = Some e ->
        repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v e n) ->
      exists m' lenv',
        m_tstep2 (globalenv p)
          (State fu stm k empty_env lenv m)
          (State fu Sskip k empty_env lenv' m') /\
        same_args_ptr lenv lenv' /\
        arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv ienv fenv finfo_env rho y cl v n
    Hbs Hcenvs Hprot Hub Hfnb
    stm lenv m k fu max_alloc Hrepr Hrel Halloc Hct
    Hprefix Hgoal_branch.
  eapply repr_bs_ecase_step_lift_from_branch_rel; eauto.
  intros t vl e ls ls' max_alloc_e
    Hy Hcc Hfind Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
    Hbr Hsw Hrel_e Hmaxeq Hbound Halloc_e Hct_e.
  destruct (Hprefix t vl e ls ls' max_alloc_e
              Hy Hcc Hfind Hbs_e Hcenvs_e Hprot_e Hub_e Hfnb_e
              Hbr Hsw Hrel_e Hmaxeq Hbound Halloc_e Hct_e)
    as [s [Hrepr_s Hpref]].
  pose proof (Hgoal_branch t vl e Hy Hcc Hfind) as Hgoal_e.
  pose proof (Hgoal_e Hcenvs_e Hprot_e Hub_e Hfnb_e
                s lenv m k max_alloc_e fu
                Hrepr_s Hrel_e Halloc_e Hct_e) as Hpost.
  exists s.
  split; [exact Hrepr_s|].
  split; [exact Hpref|].
  exact Hpost.
Qed.

Lemma repr_bs_main_reduction :
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env),
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    (forall rho x t ys e v n rho' vs,
      get_list ys rho = Some vs ->
      M.set x (Vconstr t vs) rho = rho' ->
      bstep_e (M.empty _) cenv rho' e v n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho' v e n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v (Econstr x t ys e) n) ->
    (forall rho y cl v n t vl e,
      M.get y rho = Some (Vconstr t vl) ->
      caseConsistent cenv cl t ->
      findtag cl t = Some e ->
      bstep_e (M.empty _) cenv rho e v n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v e n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v (Ecase y cl) n) ->
    (forall rho rho_clo fl f' vs xs e rho_call f t ys v c,
      M.get f rho = Some (Vfun rho_clo fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e) ->
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call ->
      bstep_e (M.empty _) cenv rho_call e v c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho_call v e c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v (Eapp f t ys) (c + 1)) ->
    (forall rho rho_clo fl f' vs xs e_body e rho_call x f t ys v v' c c',
      M.get f rho = Some (Vfun rho_clo fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call ->
      bstep_e (M.empty _) cenv rho_call e_body v c ->
      bstep_e (M.empty _) cenv (M.set x v rho) e v' c' ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho_call v e_body c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv (M.set x v rho) v' e c' ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v'
        (Eletapp x f t ys e) (c + c' + 1)) ->
    forall rho v e n,
      bstep_e (M.empty _) cenv rho e v n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v e n.
Proof.
  intros p rep_env cenv fenv finfo_env ienv
    Hpinv Hsym Hfinfo
    Heconstr Hecase Heapp Heletapp
    rho v e n Hbs.
  induction Hbs.
  - eapply Heconstr; eauto.
  - unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_eproj_step_lift_from_body_rel.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
    + intros vs0 v0 s v7 max_alloc_e
        Hy0 Hnth0 Hbs0 Hcenvs0 Hprot0 Hub0 Hfnb0
        Hrepr0 Hrel0 Hmaxeq0 Hbound0 Halloc0 Hpref0 Hct0 Hsame0.
      assert (Hv_eq : v0 = v).
      { rewrite H in Hy0. inversion Hy0; subst.
        rewrite H0 in Hnth0. inversion Hnth0; reflexivity. }
      subst v0.
      exact (IHHbs Hcenvs0 Hprot0 Hub0 Hfnb0
               s (M.set x v7 lenv) m k max_alloc_e fu
               Hrepr0 Hrel0 Halloc0 Hct0).
  - eapply Hecase; eauto.
  - eapply Heapp; eauto.
  - eapply Heletapp; eauto.
  - unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_efun_step_lift.
    + exact Hpinv.
    + exact Hsym.
    + exact Hfinfo.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
  - unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_eprim_val_step_lift.
    + exact Hpinv.
    + exact Hsym.
    + exact Hfinfo.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
  - unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_eprim_step_lift.
    + exact Hpinv.
    + exact Hsym.
    + exact Hfinfo.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
  - unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_halt_step_lift.
    + exact Hpinv.
    + exact Hsym.
    + exact Hfinfo.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
Qed.

Lemma repr_bs_main_reduction_with_prefix_handlers :
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env),
    program_inv p ->
    find_symbol_domain p finfo_env ->
    finfo_env_correct fenv finfo_env ->
    (forall rho x t ys e v n,
      bstep_e (M.empty _) cenv rho (Econstr x t ys e) v n ->
      correct_envs cenv ienv rep_env rho (Econstr x t ys e) ->
      protected_id_not_bound_id rho (Econstr x t ys e) ->
      unique_bindings_env rho (Econstr x t ys e) ->
      functions_not_bound p rho (Econstr x t ys e) ->
      forall stm lenv m k fu max_alloc,
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Econstr x t ys e) rho m lenv ->
        correct_alloc (Econstr x t ys e) max_alloc ->
        correct_tinfo p max_alloc lenv m ->
        forall vs s s' max_alloc_e,
          get_list ys rho = Some vs ->
          bstep_e (M.empty _) cenv (M.set x (Vconstr t vs) rho) e v n ->
          correct_envs cenv ienv rep_env (M.set x (Vconstr t vs) rho) e ->
          protected_id_not_bound_id (M.set x (Vconstr t vs) rho) e ->
          unique_bindings_env (M.set x (Vconstr t vs) rho) e ->
          functions_not_bound p (M.set x (Vconstr t vs) rho) e ->
          repr_asgn_constr allocIdent threadInfIdent nParam fenv finfo_env p rep_env x t ys s ->
          repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s' ->
          stm = Ssequence s s' ->
          max_alloc_e = Z.of_nat (max_allocs e) ->
          (0 <= max_alloc_e <= max_alloc)%Z ->
          correct_alloc e max_alloc_e ->
          correct_tinfo p max_alloc_e lenv m ->
          exists m_mid lenv_mid,
            m_tstep2 (globalenv p)
              (State fu stm k empty_env lenv m)
              (State fu s' k empty_env lenv_mid m_mid) /\
            same_args_ptr lenv lenv_mid /\
            rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env
              e (M.set x (Vconstr t vs) rho) m_mid lenv_mid /\
            correct_tinfo p max_alloc_e lenv_mid m_mid) ->
    (forall rho y cl v n,
      bstep_e (M.empty _) cenv rho (Ecase y cl) v n ->
      correct_envs cenv ienv rep_env rho (Ecase y cl) ->
      protected_id_not_bound_id rho (Ecase y cl) ->
      unique_bindings_env rho (Ecase y cl) ->
      functions_not_bound p rho (Ecase y cl) ->
      forall stm lenv m k fu max_alloc,
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) stm ->
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env (Ecase y cl) rho m lenv ->
        correct_alloc (Ecase y cl) max_alloc ->
        correct_tinfo p max_alloc lenv m ->
        forall t vl e ls ls' max_alloc_e,
          M.get y rho = Some (Vconstr t vl) ->
          caseConsistent cenv cl t ->
          findtag cl t = Some e ->
          bstep_e (M.empty _) cenv rho e v n ->
          correct_envs cenv ienv rep_env rho e ->
          protected_id_not_bound_id rho e ->
          unique_bindings_env rho e ->
          functions_not_bound p rho e ->
          repr_branches_LambdaANF_Codegen
            argsIdent allocIdent limitIdent threadInfIdent tinfIdent
            isptrIdent caseIdent nParam fenv finfo_env p rep_env cl ls ls' ->
          repr_switch_LambdaANF_Codegen isptrIdent caseIdent y ls ls' stm ->
          rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
          max_alloc_e = Z.of_nat (max_allocs e) ->
          (0 <= max_alloc_e <= max_alloc)%Z ->
          correct_alloc e max_alloc_e ->
          correct_tinfo p max_alloc_e lenv m ->
          exists s,
            repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e s /\
            m_tstep2 (globalenv p)
              (State fu stm k empty_env lenv m)
              (State fu s k empty_env lenv m)) ->
    (forall rho rho_clo fl f' vs xs e rho_call f t ys v c,
      M.get f rho = Some (Vfun rho_clo fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e) ->
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call ->
      bstep_e (M.empty _) cenv rho_call e v c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho_call v e c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v (Eapp f t ys) (c + 1)) ->
    (forall rho rho_clo fl f' vs xs e_body e rho_call x f t ys v v' c c',
      M.get f rho = Some (Vfun rho_clo fl f') ->
      get_list ys rho = Some vs ->
      find_def f' fl = Some (t, xs, e_body) ->
      set_lists xs vs (def_funs fl fl rho_clo rho_clo) = Some rho_call ->
      bstep_e (M.empty _) cenv rho_call e_body v c ->
      bstep_e (M.empty _) cenv (M.set x v rho) e v' c' ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho_call v e_body c ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv (M.set x v rho) v' e c' ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v'
        (Eletapp x f t ys e) (c + c' + 1)) ->
    forall rho v e n,
      bstep_e (M.empty _) cenv rho e v n ->
      repr_bs_goal p rep_env cenv fenv finfo_env ienv rho v e n.
Proof.
  intros p rep_env cenv fenv finfo_env ienv
    Hpinv Hsym Hfinfo
    Heconstr_prefix Hecase_prefix
    Heapp Heletapp
    rho v e n Hbs.
  eapply repr_bs_main_reduction; eauto.
  - intros rho0 x t ys e0 v0 n0 rho' vs Hgl Hset Hbs_e Hgoal_e.
    subst rho'.
    unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_econstr_step_lift_from_body_goal.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
    + intros vs0 s s' max_alloc_e
        Hgl0 Hbs_e0 Hcenvs_e Hprot_e Hub_e Hfnb_e
        Hasgn Hrepr_e Hstm Hmaxeq Hbound Halloc_e Hct_e.
      eapply Heconstr_prefix; eauto.
      econstructor; eauto.
    + intros vs0 Hgl0.
      rewrite Hgl in Hgl0.
      inversion Hgl0; subst.
      exact Hgoal_e.
  - intros rho0 y cl v0 n0 t vl e0
      Hy Hcc Hfind Hbs_e Hgoal_e.
    unfold repr_bs_goal.
    intros Hcenvs Hprot Hub Hfnb stm lenv m k max_alloc fu Hrepr Hrel Halloc Hct.
    eapply repr_bs_ecase_step_lift_from_branch_goal.
    + econstructor; eauto.
    + exact Hcenvs.
    + exact Hprot.
    + exact Hub.
    + exact Hfnb.
    + exact Hrepr.
    + exact Hrel.
    + exact Halloc.
    + exact Hct.
    + intros t0 vl0 e1 ls ls' max_alloc_e
        Hy0 Hcc0 Hfind0 Hbs_e0 Hcenvs_e Hprot_e Hub_e Hfnb_e
        Hbr Hsw Hrel_e Hmaxeq Hbound Halloc_e Hct_e.
      eapply Hecase_prefix; eauto.
      econstructor; eauto.
    + intros t0 vl0 e1 Hy0 Hcc0 Hfind0.
      rewrite Hy in Hy0.
      inversion Hy0; subst.
      rewrite Hfind in Hfind0.
      inversion Hfind0; subst.
      exact Hgoal_e.
Qed.

(* Main Theorem *)
Theorem repr_bs_LambdaANF_Codegen_related:
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (fenv : fun_env) (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env),
    program_inv p -> (* isPtr function is defined/correct /\ thread info is correct /\ gc invariant *)
    find_symbol_domain p finfo_env -> (* finfo_env [LambdaANF] contains precisely the same things as global env [Clight] *)
    finfo_env_correct fenv finfo_env -> (* everything in finfo_env is in the function environment *)
    forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
      bstep_e (M.empty _) cenv rho e v n ->  (* e n-steps to v *) (* for linking: environment won't be empty *)
      correct_envs cenv ienv rep_env rho e -> (* inductive type/constructor environments are correct/pertain to e*)
      protected_id_not_bound_id rho e ->
      unique_bindings_env rho e ->
      functions_not_bound p rho e -> (* function names in p/rho not bound in e *)
      forall (stm : statement) (lenv : temp_env) (m : mem) (k : cont) (max_alloc : Z) (fu : function),
        repr_expr_LambdaANF_Codegen_id fenv finfo_env p rep_env e stm -> (* translate_body e returns stm *)
        rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e rho m lenv ->
        (* " relates a LambdaANF evaluation environment [rho] to a Clight memory [m/lenv] up to the free variables in e " *)
        (* also says fundefs in e are correct in m *)
        (* NOTE: this is only place pertaining to outside of the body, and can likely incorporate free variables here *)
        correct_alloc e max_alloc ->  (* max_alloc correct *)
        correct_tinfo p max_alloc lenv m -> (* thread_info correct *)
        exists (m' : mem) (lenv' : temp_env),
          m_tstep2 (globalenv p) (State fu stm k empty_env lenv m) (State fu Sskip k empty_env lenv' m') /\
          (* memory m/lenv becomes m'/lenv' after executing stm *)
          same_args_ptr lenv lenv' /\
          arg_val_LambdaANF_Codegen fenv finfo_env p rep_env v m' lenv'. (* value v is related to memory m'/lenv' *)
Proof.
  (* NOTE [Rebuild From Scratch]:
     This theorem is being rebuilt constructively, lemma-by-lemma, from scratch.
     Historical proof scripts in git history are intentionally not used for this section.
     No admits, no Admitted, and no axioms are permitted here. *)
Abort.

End THEOREM.
