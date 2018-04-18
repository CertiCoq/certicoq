(* 
  Proof of correctness of the Clight code generation phase of CertiCoq 

  > Relates values to location in memory (syntactic)
  > Relates expression to statements (syntactic)
  > Relates L7 values (header, payload) to L7 values after GC (syntactic, up to non-function pointer location)
  > Relates L6 states to L7 states according to execution semantics

 *)

Require Import L6.cps L6.eval L6.cps_util L6.List_util L6.identifiers L6.tactics L6.shrink_cps_corresp.

Require Import L7.L6_to_Clight.



Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec Coq.Relations.Relations.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values
        compcert.common.Globalenvs
        compcert.common.Memory.

Require Import Libraries.maps_util.
 
 

Definition loc:Type := block * int.
Definition int_size := (size_chunk Mint32).
Definition max_args :=   1024%Z.

Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                        {| attr_volatile := false; attr_alignas := None |}).

Definition uint_range : Z -> Prop := 
  fun i => (0 <= i <=  Int.max_unsigned)%Z. 
Transparent uint_range.

Theorem uint_range_unsigned:
  forall i,
    uint_range (Int.unsigned i).
Proof.
  apply Int.unsigned_range_2.
Qed.
  
Ltac int_red := unfold int_size in *; simpl size_chunk in *.

Definition uint_range_l: list Z -> Prop :=
  fun l => Forall uint_range l.

Ltac solve_uint_range:=
  unfold Int.max_unsigned in *; unfold Int.modulus in *; simpl in *; (match goal with
          | [H:uint_range _ |- _] => unfold uint_range in H; solve_uint_range
          | [H:uint_range_l _ |- _] => unfold uint_range_l in H;  solve_uint_range                                                               
          | [H: Forall uint_range _ |- _] => inv H; solve_uint_range 
          | [|- uint_range _] => unfold uint_range; unfold Int.max_unsigned; unfold Int.modulus; simpl; try omega
          | [|- uint_range (Int.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range_l _] => unfold uint_range_l; solve_uint_range
          | [ |- Forall uint_range _] => constructor; solve_uint_range
          | _ => auto
          end).


Theorem int_z_mul :
  forall i y,
    uint_range_l [i; y] -> 
  Int.mul (Int.repr i) (Int.repr y) = Int.repr (i * y)%Z.
Proof.
  intros.
  unfold Int.mul.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr. reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.



Theorem int_z_add:
  forall i y,
    uint_range_l [i; y] -> 
    Int.add (Int.repr i) (Int.repr y) = Int.repr (i + y)%Z.
Proof.
  intros.
  unfold Int.add.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.  


Theorem pointer_ofs_no_overflow:
forall ofs z, 
  (0 <= z)%Z ->
  (Int.unsigned ofs + int_size * z <= Int.max_unsigned )%Z ->
                        
                        Int.unsigned (Int.add ofs (Int.repr (int_size * z))) =
        (Int.unsigned ofs + int_size * z)%Z.
Proof.
  intros.
  unfold int_size in *; simpl size_chunk in *.
  assert (0 <=  Int.unsigned ofs)%Z by apply Int.unsigned_range_2.
  unfold Int.add.
  rewrite Int.unsigned_repr with (z := (4 * z)%Z).
  rewrite Int.unsigned_repr. reflexivity.  
  omega.
  omega.
Qed.

  
 (* TODO: move to identifiers *)
Inductive bound_var_val: L6.cps.val -> Ensemble var :=
| Bound_Vconstr :
    forall c vs v x, 
    bound_var_val v x ->
    List.In v vs ->
    bound_var_val (Vconstr c vs) x
| Bound_Vfun:
    forall fds rho x f,
    bound_var_fundefs fds x ->
    bound_var_val (Vfun rho fds f) x.


(**** Representation relation for L6 values, expressions and functions ****)
Section RELATION.

  (* same as L6_to_Clight *)
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

  

    Variable cenv:L6.cps.cEnv.
  Variable fenv:L6.cps.fEnv.
  Variable finfo_env: M.t positive. (* map from a function name to its type info *)
  Variable p:program.
  
  
  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t cRep.

  
  Notation threadStructInf := (Tstruct threadInfIdent noattr).
Notation threadInf := (Tpointer threadStructInf noattr).

Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons (Tint I32 Unsigned noattr) Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := false;
                                 cc_unproto := false;
                                 cc_structret := false |}).






Notation val := uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Notation uval := uintTy.

Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).

Notation allocPtr := (Etempvar allocIdent valPtr).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).



(* changed tinf to be tempvar and have type Tstruct rather than Tptr Tstruct *)
Notation tinf := (Etempvar tinfIdent threadInf).
Notation tinfd := (Ederef tinf threadStructInf).

Notation heapInf := (Tstruct heapInfIdent noattr).

Definition add (a b : expr) := Ebinop Oadd a b valPtr.
Notation " a '+'' b " := (add a b) (at level 30).

Definition sub (a b: expr) := Ebinop Osub a b valPtr.
Notation " a '-'' b " := (sub a b) (at level 30).

Definition int_eq (a b : expr) := Ebinop Oeq a b type_bool.
Notation " a '='' b " := (int_eq a b) (at level 35).

Definition not (a : expr) := Eunop Onotbool a type_bool.
Notation "'!' a " := (not a) (at level 40).

Notation seq := Ssequence.

Notation " p ';' q " := (seq p q)
                         (at level 100, format " p ';' '//' q ").

Notation " a '::=' b " := (Sset a b) (at level 50).
Notation " a ':::=' b " := (Sassign a b) (at level 50).

Notation "'*' p " := (Ederef p val) (at level 40).

Notation "'&' p " := (Eaddrof p valPtr) (at level 40).

Definition c_int' n t := Econst_int (Int.repr n%Z) t.

Notation c_int := c_int'.

Notation "'while(' a ')' '{' b '}'" :=
  (Swhile a b) (at level 60).

Notation "'call' f " := (Scall None f (tinf :: nil)) (at level 35).

Notation "'[' t ']' e " := (Ecast e t) (at level 34).

Notation "'Field(' t ',' n ')'" :=
  ( *(add ([valPtr] t) (c_int n%Z intTy))) (at level 36). (* what is the type of int being added? *)

Notation "'args[' n ']'" :=
  ( *(add args (c_int n%Z val))) (at level 36).



  (* Any valid mem is disjoint  the global_env *)
  Axiom disjoint_mem: forall m:mem, ~ exists b i z T v v' , (Mem.load T m b z = Some v /\ Genv.find_funct (Genv.globalenv p) (Vptr b i) = Some v').

 Inductive header_of_rep: cRep -> Z -> Prop :=
 | header_enum: forall t, header_of_rep (enum t) (Z.of_N ((N.shiftl t 1) + 1))
 | header_boxed: forall t a, header_of_rep (boxed t a) (Z.of_N ((N.shiftl a 10) + t)).
  
 
Inductive repr_asgn_fun': list positive -> list N -> statement -> Prop :=
| repr_asgn_nil: repr_asgn_fun' nil nil (Efield tinfd allocIdent valPtr  :::= allocPtr)
| repr_asgn_cons: forall y ys i inf s, repr_asgn_fun' ys inf s ->
                 repr_asgn_fun' (y::ys) (i::inf) (args[ Z.of_N i ] :::= (var y); s).

Inductive repr_asgn_fun: list positive -> list N -> statement -> Prop :=
  |repr_asgn_wrap: forall ys inf s, repr_asgn_fun' ys inf s ->
                   repr_asgn_fun ys inf (argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr);s).



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
                var_or_funvar x (funVar x)
| V_VoF : forall x,
    Genv.find_symbol (Genv.globalenv p) x = None ->
       var_or_funvar x (var x).
    

Fixpoint Vint_or_Vptr (v:Values.val): bool :=
  match v with
  | Vint _ => true
  | Vptr _ _ => true
  | _ => false
  end.


Inductive get_var_or_funvar (lenv: temp_env): positive -> Values.val -> Prop :=
|F_gVoF:
   forall b x,
     Genv.find_symbol (Genv.globalenv p) x = Some b ->
   get_var_or_funvar lenv x (Vptr b (Int.repr 0%Z))
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
        | Some b => Some ((Vptr b Int.zero)::vs)
        | None =>
          (match (M.get x lenv) with
           | Some v =>
             (match v with
              | Vint _ => Some (v::vs)
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
  specialize (IHl l0 (eq_refl _)).
  destruct (Genv.find_symbol (Genv.globalenv p) a) eqn:gfpa.
  - inv H.
    constructor; auto.
    left; auto.
  - destruct  (M.get a lenv) eqn:gal.
    destruct v; inv H. constructor.
    right. apply gfpa. apply gal. auto. auto.
    constructor; auto. right; auto.
    inv H.
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
    Mem.store Mint32 m b  (Int.unsigned (Int.add (Int.repr ofs) (Int.repr (int_size*i)))) v = Some m' ->
    mem_after_n_proj_store_cast b ofs [v] i m m'
| Mem_next_c:
    forall m b ofs i v m' m'' vs,
      Mem.store Mint32 m b (Int.unsigned (Int.add (Int.repr ofs) (Int.repr (int_size*i)))) v = Some m' ->
      mem_after_n_proj_store_cast b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store_cast b ofs (v::vs) i m m''. 


Inductive mem_after_n_proj_store : block -> Z -> (list Values.val) -> Z -> mem -> mem ->  Prop :=
| Mem_last:
    forall m b ofs i v m',
    Mem.store Mint32 m b  (ofs + (int_size*i)) v = Some m' ->
    mem_after_n_proj_store b ofs [v] i m m'
| Mem_next:
    forall m b ofs i v m' m'' vs,
      Mem.store Mint32 m b (ofs + (int_size*i)) v = Some m' ->
      mem_after_n_proj_store b ofs vs (Z.succ i) m' m'' ->
      mem_after_n_proj_store b ofs (v::vs) i m m''. 

(* represent work "already done" while consuming mem_after_n_proj *)
Inductive mem_after_n_proj_snoc :  block -> Z -> (list Values.val)  -> mem -> mem ->  Prop :=
| Mem_nil_snoc: forall m b ofs, 
    mem_after_n_proj_snoc b ofs [] m m
| Mem_cons_snoc: forall m b ofs m' m'' v vs,
    mem_after_n_proj_snoc b ofs vs m m' ->
    Mem.store Mint32 m' b (ofs + (int_size*(Z.of_nat (length vs)))) v = Some m'' ->
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
      rewrite <- app_assoc. eapply IHvs1. apply H6. Focus 2. reflexivity.
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
  assert (ofs + int_size * i  = Int.unsigned (Int.add (Int.repr ofs) (Int.repr (int_size * i))))%Z.
  assert (0 <=  int_size * (i + Z.of_nat (length (a::vs)))<= Int.max_unsigned)%Z.
  unfold int_size in *. simpl size_chunk in *.
  inv H1. omega.
  rewrite Int.add_unsigned.
  unfold int_size in *.
  simpl size_chunk in *.
  inv H1.
  rewrite Int.unsigned_repr with (z := ofs).
  rewrite Int.unsigned_repr with (z := (4 * i)%Z).
  rewrite Int.unsigned_repr.
  reflexivity.
  omega. omega.
  omega.
  simpl length in H1.
  rewrite Nat2Z.inj_succ in H1.  
  rewrite Z.add_succ_r in H1.
  split; intro; inv H3.
  - constructor. rewrite H2. auto.
  - econstructor. rewrite H2. apply H8.
    rewrite <- IHvs; auto. omega.
    rewrite Z.add_succ_l.
    apply H1.    
  - constructor. rewrite <- H2. auto.
  - econstructor. rewrite <- H2. apply H8.
    rewrite IHvs; auto. omega.
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
      Mem.load Mint32 m' b' ofs' = Mem.load Mint32 m b' ofs'.
Proof.
  induction vs; intros; inv H.
  - eapply Mem.load_store_other.
    apply H8.
    unfold int_size in *.
    rewrite <- Zred_factor3 in H0.
    rewrite Z.add_assoc in H0.
    simpl length in H0. simpl Z.of_nat in H0.
    inv H0; auto.
    inv H; auto.
    right; right.
    rewrite Z.add_comm with (n := i) in H0.
    rewrite  <- Zred_factor3 in H0.
    rewrite Z.add_assoc in H0.  simpl size_chunk in H0. simpl size_chunk. omega.
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
       simpl size_chunk in *. omega.
     }
     {
       unfold int_size in *.
       simpl size_chunk in *.
       simpl length in H0.
       rewrite Nat2Z.inj_succ in H0.
       destruct H0; auto.
       destruct H. right. left. omega.
       right. right. omega.
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
    apply H0. unfold int_size in *.
    simpl size_chunk in *.
    simpl length. simpl Z.of_nat.    
    omega.
  - apply Mem.unchanged_on_trans with (m2 := m'0).
    + eapply Mem.store_unchanged_on; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      unfold int_size in *.
      simpl size_chunk in *.
      omega.
    + eapply IHvs; eauto.
      intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      unfold int_size in *.
      simpl size_chunk in *.
      omega.
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
      rewrite Nat2Z.inj_succ in H0.        intros. apply H0. int_red.
      omega.
    + eapply Mem.store_unchanged_on; eauto.
      intros.
      simpl length in H0.
      rewrite Nat2Z.inj_succ in H0. intros. apply H0. int_red.
      omega. 
Qed.
   
       
(* trunkated headers at 32 bits (or at size_of_int) *)
Definition repr_unboxed_L7: N -> Z -> Prop :=
 fun t => fun h => Int.eqm h (Z.of_N ((N.shiftl t 1) + 1)).


Definition boxed_header: N -> N -> Z -> Prop :=
  fun t => fun a =>  fun h => Int.eqm h (Z.of_N ((N.shiftl a 10) + t)).

Definition arity_of_header (h:Z): N :=
  let n := Z.to_N h in
  N.shiftr n 10.

Definition tag_of_header (h:Z): N :=
  let n := Z.to_N h in
  n.


Inductive repr_asgn_constr: positive -> cTag -> list positive -> statement -> Prop :=
| Rconstr_ass_boxed: forall x (t:cTag) vs s a n h,
    (* boxed x *)   
    M.get t rep_env = Some (boxed n a) ->
    boxed_header n a h -> 
    Forall_statements_in_seq (is_nth_projection_of_x x) vs s -> 
    repr_asgn_constr x t vs (x ::= [val] (allocPtr +' (c_int Z.one val));
                                     allocIdent ::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val); Field(var x, -1) :::= c_int h val;  s)
| Rconstr_ass_enum: forall x t n h,
    (* unboxed x *)
    M.get t rep_env  = Some (enum n) ->
    repr_unboxed_L7 n h  ->
    repr_asgn_constr x t nil (x ::= c_int h val).


Inductive repr_switch_L6_L7: positive -> labeled_statements -> labeled_statements -> statement -> Prop :=
| Mk_switch: forall x ls ls',
    repr_switch_L6_L7 x ls ls'
                      (isPtr isptrIdent caseIdent x;
                         Sifthenelse
                           (var caseIdent)
                           (Sswitch (Ebinop Oand (Field(var x, -1)) (Econst_int (Int.repr 255) val) val) ls)
                           (
                             Sswitch (Ebinop Oshr (var x) (Econst_int (Int.repr 1) val) val)
                                     ls')).

(* relate a L6.exp -| cEnv, fEnv to a series of statements in a clight program (passed as parameter) -- syntactic relation that shows the right instructions have been generated for functions body. There should not be function definitions (Efun), or primitive operations (they are not supported by our backend) in this 
TODO: maybe this should be related to a state instead? 
 *)
 
Inductive repr_expr_L6_L7: L6.cps.exp -> statement -> Prop :=
| Rconstr_e:
    forall x t vs  s s' e, 
    repr_asgn_constr x t vs s -> 
    repr_expr_L6_L7 e  s' ->
    repr_expr_L6_L7 (Econstr x t vs e)  (s; s')    
| Rproj_e: forall x t n v e  s,
    repr_expr_L6_L7 e  s ->
    repr_expr_L6_L7 (Eproj x t n v e)  (x ::= Field(var v, Z.of_N n) ; s)
| R_app_e: forall f inf ys t s,
    (* 1 - assign vs to the right args acording to fenv(f)*)
    M.get f fenv = Some inf ->
    repr_asgn_fun ys (snd inf) s -> 
    (* 2 - call f *)
    repr_expr_L6_L7 (Eapp f t ys)  (s; call ([pfunTy]funVar f))

| R_halt_e: forall v e,
    (* halt v <-> end with v in args[1] *)
    var_or_funvar v e -> 
    repr_expr_L6_L7 (Ehalt v)  (args[Z.of_nat 1 ] :::= e)
| Rcase_e: forall v cl ls ls' s ,
    (* 1 - branches matches the lists of two lists of labeled statements *)
    repr_branches_L6_L7 cl ls ls' -> 
    (* 2 - switch-header matches  *)
    repr_switch_L6_L7 v ls ls' s ->
    repr_expr_L6_L7  (Ecase v cl)  s
                     (* default case for last boxed and unboxed constructor 
                        OS: perhaps want to include a *)
with repr_branches_L6_L7: list (cTag * exp) -> labeled_statements -> labeled_statements -> Prop :=
     | Rempty_br : repr_branches_L6_L7 nil LSnil LSnil
     | Runboxed_default_br: forall t e cl ls n s, repr_branches_L6_L7 cl ls LSnil ->
                            M.get t rep_env  = Some (enum n) ->
                            repr_branches_L6_L7 ((t, e) ::cl) ls (LScons None s LSnil)
     | Runboxed_br: forall cl ls lsa' lsb' lsc' t n tag e s, repr_branches_L6_L7 cl ls (LScons lsa' lsb' lsc') ->
                                                repr_expr_L6_L7 e s ->
                                                M.get t rep_env  = Some (enum n) ->
                                                repr_unboxed_L7 n tag ->
                                                repr_branches_L6_L7 ((t, e) ::cl) ls (LScons (Some (Z.shiftr tag 1)) (Ssequence s Sbreak) (LScons lsa' lsb' lsc'))
     | Rboxed_default_br : forall cl  ls' t a n e s, repr_branches_L6_L7 cl LSnil ls' ->
                                           repr_expr_L6_L7 e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           repr_branches_L6_L7 ((t, e)::cl) (LScons None s  LSnil) ls'
     | Rboxed_br : forall cl lsa lsb lsc ls' t a n tag e s, repr_branches_L6_L7 cl (LScons lsa lsb lsc) ls' ->
                                           repr_expr_L6_L7 e s ->
                                           M.get t rep_env = Some (boxed n a) ->
                                           boxed_header n a tag ->
                                           repr_branches_L6_L7 ((t, e)::cl) (LScons (Some (Z.land tag 255)) (Ssequence s Sbreak)  (LScons lsa lsb lsc)) ls'.

                    



Definition gc_vars := ((allocIdent, valPtr)::(limitIdent, valPtr)::(argsIdent, valPtr)::(caseIdent, val) ::nil).

Definition gc_set := (allocIdent ::= Efield tinfd allocIdent valPtr ;
                                                    limitIdent ::= Efield tinfd limitIdent valPtr ;
                                                    argsIdent ::= Efield tinfd argsIdent (Tarray uintTy maxArgs noattr)).


Definition gc_test (gcArrIdent:positive) (l:N) := (reserve allocIdent limitIdent gcIdent threadInfIdent tinfIdent gcArrIdent
                                                            (Z.of_N (l + 2))).

Inductive right_param_asgn: list positive -> list N -> statement -> Prop :=
| asgn_nil: right_param_asgn nil nil Sskip
| asgn_cons: forall v vs n ns s,  right_param_asgn vs ns s -> right_param_asgn (v::vs) (n::ns) ((v ::=args[Z.of_N n]);s).


(* IMPORTANT: this is deprecated, use repr_val_L_L6_L7 instead *)
 (* relate a  L6.val -| cEnv, fEnv to an address in a Clight memory  *)
 (* not sure the int and the enum case will ever happen *)
 Inductive repr_val_ptr_L6_L7: L6.cps.val -> mem -> (block *  int) ->   Prop :=

| RPint_v : forall n m b  h i,
    Mem.load Mint32 m b (Int.unsigned i) = Some (Vint h) ->
    repr_unboxed_L7 (Z.to_N n) (Int.unsigned h) ->
    repr_val_ptr_L6_L7 (cps.Vint  n) m (b, i)
| RPconstr_enum_v: forall t n m b i h,
    M.get t rep_env = Some (enum n) ->
    Mem.load Mint32 m b (Int.unsigned i) = Some (Vint h) ->
    repr_unboxed_L7 n (Int.unsigned h) ->
    repr_val_ptr_L6_L7 (cps.Vconstr t nil) m (b, i)
| RPconstr_boxed_v :
    forall t vs m b i h a n,
      M.get t rep_env = Some (boxed n a) ->
      (* 1) well-formedness of the header block *)
      Mem.load Mint32 m b (Int.unsigned (Int.sub i Int.one)) = Some (Vint h) ->
      boxed_header n a  (Int.unsigned h) ->
      (* 2) all the fields are also well-represented *)
      Forall_in_mem_block (fun v loc  =>
                             let (b, i) := loc in 
                             exists v7, Mem.load Mint32 m b (Int.unsigned  i) = Some v7  /\ 
                             repr_val_L6_L7 v m v7) vs (b, i) (Int.repr (sizeof (M.empty composite) uintTy)) ->      
    repr_val_ptr_L6_L7 (cps.Vconstr t vs) m (b, i)
| RPfun_v :
    forall  vars fds f m b i  F t vs e asgn body l locs finfo,
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some finfo -> (* TODO: check this *)
      (* b points to an internal function in the heap [and i is 0] *)
      Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler, 
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      fn_return F = Tvoid ->
      (*
       - calling convention?  
        - only param is the threadinfo (tinfIdent of type threadInf) *)
       fn_params F = ((tinfIdent, threadInf)::nil) ->
      (*
        - all the vars match + the 3 gc vars *)       
       fn_vars F = List.app vars gc_vars ->
       Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
       (* - no temps *)
       fn_temps F = nil ->
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_L6_L7)
        *)
              fn_body F = Ssequence gc_set (Ssequence (gc_test finfo l)
                                               (Ssequence asgn body)) ->              
       right_param_asgn vs locs asgn ->
       repr_expr_L6_L7 e body ->
    repr_val_ptr_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (b, i)
(* like repr_val but not defered (i.e. positive is in tempval 
  if local_env is really holding blocks to lookup in memory, then should rework this *)
with repr_val_L6_L7:  L6.cps.val -> mem -> Values.val -> Prop :=
| Rint_v: forall z r m,
    repr_unboxed_L7 (Z.to_N z) (Int.unsigned r) ->
    repr_val_L6_L7 (L6.cps.Vint z) m (Vint r)
| Rconstr_unboxed_v:
    forall t arr n m,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_L7 arr (Int.unsigned n) ->
      repr_val_L6_L7 (L6.cps.Vconstr t nil) m (Vint n)
| Rconstr_boxed_v: forall t vs arr a b i m,
    (* t is a boxed constructor, n ends with 0 and represents 
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed arr a) ->
    repr_val_ptr_L6_L7 (L6.cps.Vconstr t vs) m (b, i) ->
    (* todo: this might actually be a Vint that needs to be interpreted as a pointer *)
    repr_val_L6_L7 (L6.cps.Vconstr t vs) m (Vptr b i)
| Rfunction_v: forall fds f m b i, 
    repr_val_ptr_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (b, i) ->
    repr_val_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (Vptr b i)
.



Definition locProp := block -> Z -> Prop.
About Mem.load.
(* m and m' are the _same_ over subheap L *)

Definition sub_locProp: locProp -> locProp -> Prop :=
  fun L L' => forall b ofs, L b ofs -> L' b ofs.

      





Inductive repr_val_L_L6_L7:  L6.cps.val -> mem -> locProp -> Values.val -> Prop :=
| RSint_v: forall L z r m,
    repr_unboxed_L7 (Z.to_N z) (Int.unsigned r) ->
    repr_val_L_L6_L7 (L6.cps.Vint z) m L (Vint r)
| RSconstr_unboxed_v:
    forall t arr n m L,
      M.get t rep_env = Some (enum arr) ->
      repr_unboxed_L7 arr (Int.unsigned n) ->
      repr_val_L_L6_L7 (L6.cps.Vconstr t nil) m L (Vint n)
| RSconstr_boxed_v: forall (L:block -> Z -> Prop) t vs n a b i m h,
    (* t is a boxed constructor, n ends with 0 and represents 
      a pointer to repr_val_ptr of (t, vs)  *)
    M.get t rep_env = Some (boxed n a) ->
    (forall j : Z, (Int.unsigned (Int.sub i (Int.repr int_size)) <= j <
   Int.unsigned (Int.sub i (Int.repr int_size)) + size_chunk Mint32)%Z  -> L b j%Z) ->
    (* 1) well-formedness of the header block *)

    Mem.load Mint32 m b (Int.unsigned (Int.sub i (Int.repr int_size))) = Some (Vint h) ->
    boxed_header n a  (Int.unsigned h) ->
    (* 2) all the fields are also well-represented *)
    repr_val_ptr_list_L_L6_L7 vs m L b i ->
    repr_val_L_L6_L7 (L6.cps.Vconstr t vs) m L (Vptr b i)
| RSfunction_v: 
    forall (L:block -> Z -> Prop)  vars fds f m b   F t vs e asgn body l locs finfo,
      find_def f fds = Some (t, vs, e) ->
      M.get t fenv = Some (l, locs) ->
      M.get f finfo_env = Some finfo -> (* TODO: check this *)
      (* b points to an internal function in the heap [and i is 0] *)
      Genv.find_funct (globalenv p) (Vptr b  Int.zero) = Some (Internal F) ->
      (* F should have the shape that we expect for functions generated by our compiler, 
       > see translate_fundefs i.e.
        - returns a Tvoid *)
      fn_return F = Tvoid ->
      (*
       - calling convention?  
        - only param is the threadinfo (tinfIdent of type threadInf) *)
      fn_params F = ((tinfIdent, threadInf)::nil) ->
       (*
        - all the vars match + the 3 gc vars *)       
       fn_vars F = List.app vars gc_vars ->
       Forall2 (fun x xt =>  xt = (x, val))  vs vars  ->
       (* - no temps *)
       fn_temps F = nil ->
       (*
        - function header: threadInfo, gc check, load parameters,  then body equivalent to e (related according to repr_exp_L6_L7)
        *)
       fn_body F = Ssequence gc_set (Ssequence (gc_test finfo l)
                                                      (Ssequence asgn body)) ->              
              right_param_asgn vs locs asgn ->
       repr_expr_L6_L7 e body ->
    repr_val_L_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m L (Vptr b Int.zero) 
with repr_val_ptr_list_L_L6_L7: (list L6.cps.val) -> mem -> locProp -> block -> int -> Prop := 
     | RSnil_l:
         forall m L b i,
           repr_val_ptr_list_L_L6_L7 nil m L b i
     | RScons_l:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, ((Int.unsigned i) <= j < (Int.unsigned i) + int_size)%Z -> L b j) ->
           Mem.load Mint32 m b (Int.unsigned  i) = Some v7 ->
           repr_val_L_L6_L7 v m L v7 -> 
           repr_val_ptr_list_L_L6_L7 vs m L b (Int.add i (Int.repr int_size)) ->
           repr_val_ptr_list_L_L6_L7 (v::vs) m L b i.
 
Inductive  repr_val_ptr_list_L_L6_L7_Z: (list L6.cps.val) -> mem -> locProp -> block -> Z -> Prop := 
     | RSnil_l_Z:
         forall m L b i,
           repr_val_ptr_list_L_L6_L7_Z nil m L b i
     | RScons_l_Z:
         forall v vs m (L:block -> Z -> Prop) b i v7,
           (forall j : Z, (i <= j < i + int_size)%Z -> L b j) ->
           Mem.load Mint32 m b i = Some v7 ->
           repr_val_L_L6_L7 v m L v7 -> 
           repr_val_ptr_list_L_L6_L7_Z vs m L b (i+ int_size)%Z ->
           repr_val_ptr_list_L_L6_L7_Z (v::vs) m L b i.
 
    
Theorem repr_val_ptr_list_Z:
  forall m L b vs i,
    uint_range ((Int.unsigned i) + (Z.of_nat (length vs)* int_size))%Z -> 
  repr_val_ptr_list_L_L6_L7 vs m L b i <-> repr_val_ptr_list_L_L6_L7_Z vs m L b (Int.unsigned i).
Proof.
  induction vs; intros.
  - split; intro; constructor.
  - assert  (Hi4 : (Int.unsigned i + 4)%Z = (Int.unsigned (Int.add i (Int.repr 4)))).
    { 
      unfold int_size in *; simpl size_chunk in *.
      rewrite Int.add_unsigned.
      rewrite Int.unsigned_repr.
      rewrite Int.unsigned_repr. reflexivity.
      unfold Int.max_unsigned. simpl. omega.
      rewrite Int.unsigned_repr.
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
      rewrite Z.mul_succ_l in H.
      assert (0 <= Z.of_nat (length vs))%Z.     
      apply Zle_0_nat.
      rewrite Z.add_assoc in H.
      assert (0 <= Int.unsigned i)%Z by apply Int.unsigned_range.
      inv H. split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. auto. 
      omega. omega.       
      unfold Int.max_unsigned in *. simpl in *. omega.
      }
    split; intro; inv H0.
    + econstructor; eauto; unfold int_size in *; simpl size_chunk in *.
      apply IHvs in H10.
      rewrite Hi4.
      auto.
      rewrite <- Hi4.
      
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.
     
      assert (0 <= Int.unsigned i)%Z by apply Int.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Zle_0_nat.
      inv H.
      rewrite Z.mul_succ_l in H7.
      rewrite Z.add_assoc in H7.
      split; omega.
    + econstructor; eauto.
      unfold int_size in *; simpl size_chunk in *.
      apply IHvs.
      rewrite <- Hi4. 
      simpl length in H.
      rewrite Nat2Z.inj_succ in H.     
      assert (0 <= Int.unsigned i)%Z by apply Int.unsigned_range.
      assert (0 <= Z.of_nat (length vs))%Z by       apply Zle_0_nat.
      inv H.
      rewrite Z.mul_succ_l in H6.
      rewrite Z.add_assoc in H6.
      split; omega.
      rewrite <- Hi4. auto.
Qed.      
      
    

(* this is the sum of get_var_or_funvar and repr_val_L_L6_L7 (-> and <-\-) *)
Inductive repr_val_id_L_L6_L7: L6.cps.val -> mem -> locProp -> temp_env -> positive -> Prop := 
| RVid_F:
   forall b x lenv fds f L m,
     Genv.find_symbol (Genv.globalenv p) x = Some b ->
     repr_val_L_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m L (Vptr b (Int.zero)) ->
     repr_val_id_L_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m L lenv x
| RVid_V:
    forall x m lenv L v6 v7,
      Genv.find_symbol (Genv.globalenv p) x = None -> 
      M.get x lenv = Some v7 ->
      repr_val_L_L6_L7 v6 m L v7 ->
      repr_val_id_L_L6_L7 v6 m L lenv x.

Theorem repr_val_id_implies_var_or_funvar:
  forall v6 m L lenv x,
  repr_val_id_L_L6_L7 v6 m L lenv x ->
  exists v7, get_var_or_funvar lenv x v7 /\
             repr_val_L_L6_L7 v6 m L v7.
Proof.
  intros. inv H.
  - exists (Vptr b Int.zero).
    split. constructor; auto.
    auto.
  - exists v7.
    split. constructor 2; auto. inv H2; auto.
    auto.
Qed.

Theorem repr_val_id_set:
  forall v6 m L lenv x,
    repr_val_id_L_L6_L7 v6 m L lenv x ->
    forall x0 v, 
    x <> x0 ->
    repr_val_id_L_L6_L7 v6 m L (M.set x0 v lenv) x.
Proof.
  intros. inv H.
  - econstructor; eauto.
  - econstructor 2; eauto.
    rewrite M.gso; auto.
Qed.
                                
Scheme repr_val_ind' := Minimality for repr_val_L_L6_L7 Sort Prop
  with repr_val_list_ind' := Minimality for repr_val_ptr_list_L_L6_L7 Sort Prop.
 (* Combined Scheme repr_val_L_L6_L7_mutind from repr_val_L_L6_L7_ind, repr_val_ptr_list_L_L6_L7_ind. *)
 
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
  rewrite Zpower.shift_equiv; auto. omega.
Qed.


Theorem repr_val_ptr_list_L_Z_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_L6_L7_Z vs m L b i -> 
 nthN vs n = Some v6 ->
 exists v7, Mem.load Mint32 m b (i + (Z.of_N n * int_size))  = Some v7 /\
 repr_val_L_L6_L7 v6 m L v7.
Proof.  
  induction vs; intros. inv H0.
  inv H. 
  destruct n. simpl in H0. inv H0.
  exists v7.
  simpl. rewrite Z.add_0_r. auto.
  apply nthN_pos_pred in H0.
  eapply IHvs in H0; eauto. destruct H0. exists x. inv H.
  int_red.
  rewrite N2Z.inj_pred in H0.
  rewrite Z.mul_pred_l in H0.
  replace (i + 4 + (Z.of_N (N.pos p0) * 4 - 4))%Z with (i + Z.of_N (N.pos p0) * 4)%Z in H0 by omega.
  auto.
  unfold N.lt. auto. 
Qed.


Theorem repr_val_ptr_list_L_nth:
  forall {m L  v6 vs n b i},
 repr_val_ptr_list_L_L6_L7 vs m L b i -> 
 nthN vs n = Some v6 ->
 exists v7, Mem.load Mint32 m b (Int.unsigned (Int.add i (Int.mul (Int.repr (Z.of_N n)) (Int.repr int_size))))  = Some v7 /\
 repr_val_L_L6_L7 v6 m L v7.
Proof.  
  induction vs; intros. inversion H0.
  destruct n.
  - simpl. inv H0.
    inv H.
    rewrite Int.add_zero. 
    exists v7; auto.
  - simpl.
    inv H.
    apply nthN_pos_pred in H0.
    specialize (IHvs _ _ _ H10 H0).
    destruct IHvs. destruct H.
    exists x; split; auto.
    replace (Int.unsigned
           (Int.add (Int.add i (Int.repr int_size))
              (Int.mul (Int.repr (Z.of_N (N.pred (N.pos p0))))
                       (Int.repr int_size)))) with
        (Int.unsigned
           (Int.add i (Int.mul (Int.repr (Z.pos p0)) (Int.repr int_size)))) in H.
    auto.
    rewrite Int.add_assoc.
    unfold Int.mul.
    unfold Int.add.
    erewrite  Int.eqm_samerepr.
    reflexivity.
    apply Int.eqm_add.
    apply Int.eqm_refl.
    eapply Int.eqm_trans.
    apply Int.eqm_unsigned_repr_l.
    Focus 2.    
    apply Int.eqm_unsigned_repr_r.
    apply Int.eqm_refl.
    rewrite Z.add_comm.
    rewrite N2Z.inj_pred by (unfold N.lt; auto).
    int_red.
    rewrite N2Z.inj_pos.
    eapply Int.eqm_trans.
    apply Int.eqm_mult.
    apply Int.eqm_unsigned_repr_l.
    apply Int.eqm_refl.
    apply Int.eqm_unsigned_repr_l.
    apply Int.eqm_refl. 
    eapply Int.eqm_trans.
    Focus 2.
    apply Int.eqm_add.
    apply Int.eqm_unsigned_repr_r.
    apply Int.eqm_mult.
    apply Int.eqm_unsigned_repr_r.
    apply Int.eqm_refl.
    apply Int.eqm_unsigned_repr_r.
    apply Int.eqm_refl.
    apply Int.eqm_unsigned_repr_r.
    apply Int.eqm_refl.
    rewrite Z.mul_pred_l.
    apply Int.eqm_refl2. omega.
Qed.



Theorem repr_val_L_unchanged:
  forall v6 m L v7, 
  repr_val_L_L6_L7 v6 m L v7 ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_L_L6_L7 v6 m' L v7.
Proof.
  apply (repr_val_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_L6_L7 v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_L6_L7 vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5). 
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.  
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Theorem repr_val_id_L_unchanged:
  forall v6 m lenv L x, 
  repr_val_id_L_L6_L7 v6 m L lenv x ->
  forall m', Mem.unchanged_on L m m' ->
  repr_val_id_L_L6_L7 v6 m' L lenv x.
Proof.
    intros. inv H.
  - econstructor; eauto. eapply repr_val_L_unchanged; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_ptr_list_L_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_L6_L7 vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_L6_L7 vs m' L b i.
Proof.
  apply (repr_val_list_ind' (fun v m L v7 => forall m', Mem.unchanged_on L m m' -> repr_val_L_L6_L7 v m' L v7)
                       (fun vs m L b i => forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_L6_L7 vs m' L b i)); intros; try (now econstructor; eauto).
  - specialize (H4 _ H5). 
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.  
  - econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto.
Qed.

Corollary repr_val_ptr_list_L_Z_unchanged:
  forall vs m L b i,
    repr_val_ptr_list_L_L6_L7_Z vs m L b i ->
forall m', Mem.unchanged_on L m m' -> repr_val_ptr_list_L_L6_L7_Z vs m' L b i.
Proof.
  induction vs; intros.
  constructor.
  inv H. econstructor; eauto.
  eapply Mem.load_unchanged_on; eauto.  
  eapply repr_val_L_unchanged; eauto.
Qed.

Theorem repr_val_L_sub_locProp:
    forall v6 m L v7, 
  repr_val_L_L6_L7 v6 m L v7 ->
  forall L', sub_locProp L L' -> 
  repr_val_L_L6_L7 v6 m L' v7.
Proof.
  apply (repr_val_ind' (fun v6 m L v7 => forall L', sub_locProp L L' -> 
                                                   repr_val_L_L6_L7 v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_L6_L7 vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Theorem repr_val_id_L_sub_locProp:
  forall v6 m L x lenv, 
    repr_val_id_L_L6_L7 v6 m L lenv x ->
    forall L', sub_locProp L L' -> 
               repr_val_id_L_L6_L7 v6 m L' lenv x.
Proof.
  intros. inv H.
  - econstructor; eauto. eapply repr_val_L_sub_locProp; eauto.
  - econstructor 2; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.

    
Theorem repr_val_ptr_list_L_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_L6_L7 vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_L6_L7 vs m L' b i.
Proof.
  apply (repr_val_list_ind' (fun v6 m L v7 => forall L', sub_locProp L L' -> 
                                                   repr_val_L_L6_L7 v6 m L' v7)
                       (fun vs m L b i => forall L', sub_locProp L L' ->  repr_val_ptr_list_L_L6_L7 vs m L' b i)); intros; try (now econstructor; eauto).
Qed.

Corollary repr_val_ptr_list_L_Z_sub_locProp:
    forall vs m L b i,
      repr_val_ptr_list_L_L6_L7_Z vs m L b i ->
      forall L', sub_locProp L L' ->
                 repr_val_ptr_list_L_L6_L7_Z vs m L' b i.
Proof.
  induction vs; intros.
  -  constructor.
  - inv H. econstructor; eauto.
    eapply repr_val_L_sub_locProp; eauto.
Qed.  



    
(* 
Returns True if the pointer Vptr q_b q_ofs is reachable by crawling v7 
Assumes correct memory layout (i.e. repr_val_L6_L7 v6 m v7)
 *)
Fixpoint reachable_val_L7 (v6:L6.cps.val) (m:mem) (v7:Values.val) (q_b:block) (q_ofs:int): Prop :=
  match v6, v7 with
  | L6.cps.Vint z, Vint r => False
  | L6.cps.Vconstr t vs, Vptr b i =>
    (fst (List.fold_left (fun curr v =>
                            let '(p, (p_b, p_ofs)) := curr in
                            (match Val.cmpu_bool (Mem.valid_pointer m) Ceq (Vptr p_b p_ofs) (Vptr q_b q_ofs) with
                             | Some true => (True, (p_b, (Int.add p_ofs (Int.repr (sizeof (M.empty composite) uintTy)))))
                             | _ => 
                               (match Mem.load Mint32 m p_b (Int.unsigned p_ofs) with
                                | Some v7 => 
                                  (reachable_val_L7 v m v7 q_b q_ofs, (p_b, (Int.add p_ofs (Int.repr (sizeof (M.empty composite) uintTy)))))
                                | _ => curr
                                end)
                             end))                        
                        vs (False, (b,i))))
  | (L6.cps.Vfun rho fds f), Vptr b i => False
  | _, _ => False
  end.


                                                                        

Theorem repr_val_load_result: forall v6 m v7,
    repr_val_L6_L7 v6 m (Val.load_result Mint32 v7)
                   <->
  repr_val_L6_L7 v6 m v7.
Proof.
  intros.
  destruct v7; split; intro H; inv H; simpl in *; econstructor; eauto.
Qed.  

Theorem repr_val_L_load_result: forall v6 m v7 L,
    repr_val_L_L6_L7 v6 m L (Val.load_result Mint32 v7)
                   <->
  repr_val_L_L6_L7 v6 m L v7.
Proof.
  intros.
  destruct v7; split; intro H; inv H; simpl in *; econstructor; eauto.
Qed.  


(* the memory blocks in the sequence (b, i), (b, i+off) ... (b, i+((n-1)*off)) are pairwise related with the sequence (b', i'), (b', i'+off) ... (b', i'+(n-1*off))  *)
Inductive For_N_blocks (P:(block * int) -> (block * int) -> Prop) (loc:block * int) (loc':block * int) (off: int) :  nat -> Prop :=
| FNb_O: For_N_blocks P loc loc' off 0
| FNb_S: forall n,
    P (fst loc, Int.add (snd loc) (Int.mul off (Int.repr (Z.of_nat n)))) (fst loc', Int.add (snd loc') (Int.mul off (Int.repr (Z.of_nat n)))) ->
    For_N_blocks P  loc loc' off n -> 
    For_N_blocks P loc  loc' off (S n). 


(* Related (deep copy) vals that may have been moved by the GC, in such way that they can be used in place of the other in repr_val_ptr_L6_L7 
 *)
Inductive related_boxed_L7: mem -> (block *  int) -> mem -> (block *  int) -> Prop :=
| SV_constr_boxed :
    forall m m' b i b' i' h h' n a,
    (* same tag *)
      Mem.load Mint32 m b (Int.unsigned (Int.sub i Int.one)) = Some (Vint h) ->
      boxed_header n a  (Int.unsigned h) ->
      Mem.load Mint32 m' b' (Int.unsigned (Int.sub i' Int.one)) = Some (Vint h') ->
      boxed_header n a  (Int.unsigned h') ->      
      (* each of the a (arrity) fields are either same int shifted+1, same function or pointers (0-ended) related according to same_boxed *)
      For_N_blocks (fun loc loc' => related_boxed_or_same_val_L7 m loc m' loc') (b,i) (b', i') (Int.repr (sizeof (M.empty composite) uintTy)) (N.to_nat a) -> 
      related_boxed_L7 m (b,i) m' (b', i')
with related_boxed_or_same_val_L7: mem -> (block *  int) -> mem -> (block *  int) -> Prop :=
     | RBSI_fun :
         (* same fun *)
         forall m m' b i b' i' F,
           b = b' /\ i = i' ->
           Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F) ->
           related_boxed_or_same_val_L7 m (b,i) m' (b', i')                                   
     | RBSI_int :
         (* same int/unboxed constructor *)
         forall m b i n m' b' i' h,
           Mem.load Mint32 m b (Int.unsigned i) = Some (Vint h) ->
           Mem.load Mint32 m' b' (Int.unsigned i') = Some (Vint h) ->
           repr_unboxed_L7 n (Int.unsigned h) ->
           related_boxed_or_same_val_L7 m (b,i) m' (b', i')
     | RBSI_pointer:
         forall m b i  m' b' i' b1 i1 b2 i2,
         Mem.load Mint32 m b (Int.unsigned i) = Some (Vptr b1 i1) ->
         Mem.load Mint32 m' b' (Int.unsigned i') = Some (Vptr b2 i2) ->
         (* TODO: may be Vint h and h' that needs to be interpreted as pointers inside m *)
         (* TODO: make sure that *)
         related_boxed_L7 m (b1, i1) m' (b2,i2) ->
         related_boxed_or_same_val_L7 m (b,i) m' (b', i').

(* TODO: related or boxed which also checks that what is reachable is in L *)
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
         (match Mem.load Mint32 m b' ((Int.unsigned i') - int_size) with
          | Some (Vint h) =>
            (* get arity from header *)
            let n := arity_of_header (Int.unsigned h) in
            (* 
            let fix load_val_tree_ptr (m:mem) (b:block) (ofs:Z) (i:nat): option (list val_tree) :=
                (match i with
                | 0 =>  Some nil
                | S i' =>
                  (match Mem.load Mint32 m b ofs with
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

 

  
(* this is just a sketch, ignore for now *)
Theorem repr_same_boxed_L_L6_L7 :
  forall v m  L v7 ,
    repr_val_L_L6_L7 v m L v7 ->
    forall  m' b i b' i', v7 = (Vptr b i) ->
                related_boxed_L7 m (b,i) m' (b', i') ->
                exists L', repr_val_L_L6_L7 v m' L' (Vptr b' i')
.
Proof.  
  apply (repr_val_ind' (fun v m L v7 =>  forall  m' b i b' i', v7 = (Vptr b i) ->
                                                               related_boxed_L7 m (b,i) m' (b', i') ->
                                                               exists L', repr_val_L_L6_L7 v m' L' (Vptr b' i'))
                       (fun vs m L b i => forall m' b' i', 
                            related_boxed_L7 m (b,i) m' (b', i') ->
                            exists L', repr_val_ptr_list_L_L6_L7 vs m' L' b' i')); intros.
  - inv H0.
  - inv H1.
  - inv H5.
    admit.
  - inv H11.
    admit.
  - exists (fun b z => False). constructor.
  - admit.    
Admitted.
  



(* this is false, missing the boxed case which is off-shifted 
Theorem repr_val_ptr_load :
  forall v6 m b i,
    repr_val_ptr_L6_L7 v6 m (b, i) ->
    (exists v7, Mem.load Mint32 m b (Int.unsigned i)  = Some v7 /\ repr_val_L6_L7 v6 m v7)
             \/ exists F, Genv.find_funct (globalenv p) (Vptr b i) = Some (Internal F). *)


(* TODO: write this to ensure that the GC nevers runs out of space in the middle of a function*)
Definition correct_alloc: exp -> Z -> Prop := fun e i => i =  Z.of_nat (max_allocs e ).

Theorem max_allocs_boxed: forall v c e l,
    l <> nil -> 
(max_allocs (Econstr v c l e) = 1 + (length l) + max_allocs e).
Proof.
  intros; simpl. induction l.
  exfalso; auto.
  destruct l. omega.
  simpl.
  simpl in IHl.
  rewrite <- IHl. omega.
  intro. inv H0.
Qed.


(* see make_fundef_info, this is w.r.t. some fenv, another prop should assert the fenv is correct w.r.t. all functions *)
Inductive correct_fundef_info: positive -> fTag -> list positive -> exp -> ident -> Prop :=
  c_funinfo: forall f t vs e tag n l b finfo fi_0 fi_1 fi_rest,
    (* the tag for f points to a record r *)
    M.get f fenv =  Some (n, l) ->
    n = N.of_nat (length l) ->
    (* id points to an array in global memory *)
    Genv.find_symbol (globalenv p) tag = Some b ->
    Genv.find_var_info (globalenv p) b = Some finfo ->
    
    (* the record has the right information w.r.t. vs and r 
       fi[0] = alloc(e)
       fi[1] = number of roots
       |fi| = 2+fi[1] *)
    gvar_init finfo = ((Init_int32 fi_0)::(Init_int32 fi_1)::fi_rest) ->
    correct_alloc e (Int.unsigned fi_0) ->
    fi_1 = Int.repr (Z.of_N n) ->
    n = N.of_nat (length fi_rest) -> 
    correct_fundef_info f t vs e tag. 


(* P is true of every fundefs in a bundle *)
(* TODO: move this to cps_util *)
Inductive Forall_fundefs: (L6.cps.var -> fTag -> list L6.cps.var -> exp -> Prop) -> fundefs -> Prop :=
| Ff_cons : forall (P:(L6.cps.var -> fTag -> list L6.cps.var -> exp -> Prop)) f t vs e fds,
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
   3) global env holds a correct L7 representation of the function *)
Definition correct_environments_for_function:
  genv -> fEnv -> M.t positive -> mem -> fundefs ->  L6.cps.var ->
  fTag -> list L6.cps.var -> exp ->  Prop
  := fun ge fenv finfo_env m fds f t vs e =>
       exists l locs finfo b, 
         (*1*)
         M.get f finfo_env = Some finfo /\
         correct_fundef_info f t vs e finfo /\
         (*2*)
         M.get t fenv = Some (l, locs) /\
         l = N.of_nat (length vs) /\
         (* may want to check that locs are distinct and same as in finfo? *)
         (*3*)
         Genv.find_symbol (globalenv p) f = Some b /\
         repr_val_ptr_L6_L7 (cps.Vfun (M.empty cps.val) fds f) m (b, Int.zero).

(* relates the top level bundle of function fds to a map of fundef_info and a global environment with related functions *) 
Definition correct_environments_for_functions: fundefs -> genv -> fEnv -> M.t positive -> mem ->  Prop := fun fds ge fenv finfo_env m =>
                                                                                                            Forall_fundefs (correct_environments_for_function ge fenv finfo_env m fds) fds.

(* true if alloc, limit or args *)
Definition is_protected_loc lenv b ofs : Prop  :=
  M.get allocIdent lenv = Some (Vptr b ofs)
  \/
  M.get limitIdent lenv = Some (Vptr b ofs)
  \/
  (exists args_ofs i, M.get argsIdent lenv = Some (Vptr b args_ofs) /\
   Int.ltu i (Int.repr max_args) = true /\
  Int.eq (Int.add args_ofs (Int.mul (Int.repr (sizeof (M.empty composite) uintTy)) i))  ofs = true ).

Definition is_protected_id id  : Prop :=
  id = allocIdent \/ id = limitIdent \/ id = argsIdent.

Definition functions_not_bound (e:exp): Prop :=
  forall x,
    bound_var e x ->
    Genv.find_symbol (globalenv p) x = None.


(* UB + disjoint bound and in env *)
Definition unique_bindings_env (rho:L6.eval.env) (e:exp) : Prop :=
      unique_bindings e  /\ 
      forall x,
    (exists v, M.get x rho = Some v) ->
    ~ bound_var e x.
  
Theorem functions_not_bound_subterm:
  forall e,
    functions_not_bound e ->
    forall e',
    subterm_e e' e ->
    functions_not_bound e'.
Proof.
  intros. intro; intros.
  apply H.
  eapply bound_var_subterm_e; eauto.
Qed.  

Definition protected_id_not_bound (rho:L6.eval.env) (e:exp) : Prop :=
  (forall x y v, M.get x rho = Some v ->
                 is_protected_id y ->
                 ~ (x = y \/ bound_var_val v y) )/\
  (forall y, is_protected_id y ->
             ~ bound_var e y).


Inductive empty_cont: cont -> Prop :=
| Kempty_stop: empty_cont Kstop
| Kempty_switch: forall k, empty_cont k ->
                           empty_cont (Kswitch k)
| Kempty_sbreak: forall k, empty_cont k ->
                           empty_cont (Kseq Sbreak k)
| Kempty_sskip: forall k, empty_cont k ->
                           empty_cont (Kseq Sskip k)
.
                                      
Definition protected_non_reachable_val_L7 v6 m v7 (lenv:temp_env) : Prop :=
      exists alloc_b alloc_ofs limit_b limit_ofs args_b args_ofs,
        M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
        ~reachable_val_L7 v6 m v7 alloc_b alloc_ofs /\
        M.get limitIdent lenv = Some (Vptr limit_b limit_ofs) /\
        ~reachable_val_L7 v6 m v7 limit_b limit_ofs /\
        M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
        (forall i,
            Int.ltu i (Int.repr max_args) = true ->                   
            ~reachable_val_L7 v6 m v7 args_b (Int.add args_ofs (Int.mul (Int.repr (sizeof (M.empty composite) uintTy)) i))).

 

Definition protected_not_in_L (lenv:temp_env) (max_alloc:Z) (L:block -> Z -> Prop): Prop :=
  exists alloc_b alloc_ofs limit_ofs args_b args_ofs,
    M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) /\
    (forall j : Z, ((Int.unsigned alloc_ofs) <= j <
                    Int.unsigned (Int.add alloc_ofs (Int.repr (int_size * max_alloc))))%Z  ->
                   ~ L alloc_b j) /\
    M.get limitIdent lenv = Some (Vptr alloc_b limit_ofs) /\
(*         (forall j : Z, ((Int.unsigned limit_ofs) <= j <
                    Int.unsigned limit_ofs + size_chunk Mint32)%Z  ->
                   ~ L alloc_b_b j) *)
    M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
          (forall z j: Z,
              (0 <= z < max_args)%Z -> 
              ((Int.unsigned  (Int.add args_ofs (Int.repr (int_size * z))))
               <= j <
               (Int.unsigned (Int.add args_ofs (Int.repr (int_size * z)))) +  int_size)%Z ->

                       ~ L args_b j).


 
Theorem protected_not_in_L_proper:
  forall lenv lenv' L z,
  map_get_r _ lenv lenv' ->
  protected_not_in_L lenv z L ->
  protected_not_in_L lenv' z L.
Proof.
  intros.
  inv H0. destructAll. rewrite H in *.
  do 5 eexists. repeat split; eauto.
Qed.

Theorem protected_not_in_L_set:
  forall lenv z L x v ,
  protected_not_in_L lenv z L ->
  ~ is_protected_id x ->
  protected_not_in_L (M.set x v lenv) z L.
Proof.
  intros.
  destruct H.
  destructAll.
  exists x0, x1, x2, x3, x4.
  repeat split;auto.
  - destruct (var_dec allocIdent x).
    + exfalso; apply H0.
      unfold is_protected_id.
      auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec limitIdent x).
    + exfalso; apply H0.
      unfold is_protected_id.
      auto.
    +  rewrite M.gso by auto. auto.
  - destruct (var_dec argsIdent x).
    + exfalso; apply H0.
      unfold is_protected_id.
      auto.
    +  rewrite M.gso by auto. auto.
Qed.


(* Mono + extra assumptions to avoid overflow *)
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
  do 2 (eexists). 
  repeat split; eauto.  
  intros. apply H5.
  unfold int_size in *; simpl size_chunk in *.
  assert (Int.unsigned limit_ofs <= Int.max_unsigned)%Z by apply Int.unsigned_range_2 .
  assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range_2 .
  unfold Int.add in *.
  rewrite Int.unsigned_repr with (z := (4 * z)%Z) by omega.
  rewrite Int.unsigned_repr with (z := (4 * z')%Z) in H by omega.
  rewrite Int.unsigned_repr by omega.
  rewrite Int.unsigned_repr in H by omega. omega.
Qed.
 
  
Definition Vint_or_Vconstr (v:cps.val): Prop :=
  (exists i, v = cps.Vint i) \/ (exists c vs, v = cps.Vconstr c vs).
  
(* relates a L6 evaluation environment to a Clight memory up to the free variables in e *)
(* If x is a free variable of e, then it might be in the generated code:
   1) a function (may want to handle this separately as they won't get moved by the GC) in the global environment, evaluates to a location related to f by repr_val_ptr_L6_L7
   2) a local variable in le related to (rho x) according to repr_val_L6_L7 -- this happens when e.g. x := proj m, or after function initialization

All the values are in a space L which is disjoint form protected space

Note that parameters are heap allocated, and at function entry "free variables" are held in args and related according to repr_val_ptr_L6_L7
 
Now also makes sure none of the protected portion are reachable by the v7

 *)

    Definition rel_mem_L6_L7: exp -> L6.eval.env -> mem -> temp_env -> Prop :=
      fun e rho m le =>
        exists L, protected_not_in_L le (Z.of_nat (max_allocs e)) L /\
        forall x, occurs_free e x ->
                  exists v6, M.get x rho = Some v6 /\
                               repr_val_id_L_L6_L7 v6 m L le x.
(*
Theorem rel_mem_update_protected:
  forall e rho m le b ofs v m',
    rel_mem_L6_L7 e rho m le ->
    Mem.store Mint32 m b ofs v = Some m' ->
    is_protected_loc le b (Int.repr ofs) -> 
    rel_mem_L6_L7 e rho m' le.  *)
    
 Fixpoint mem_of_state (s:state) : mem :=
  match s with
  | State f s k e le m => m
  | Callstate f vs k m => m
  | Returnstate x k m =>  m
  end.


  
(* [pure] step with no built-in, i.e. trace is always E0 *)
Definition traceless_step2:  genv -> state -> state -> Prop := fun ge s s' => step2 ge s nil s'. 

Definition m_tstep2 (ge:genv):=  clos_trans state (traceless_step2 ge).

Hint Unfold Int.modulus Int.max_unsigned uint_range.
Hint Transparent Int.max_unsigned Int.modulus uint_range.
 
Inductive mem_after_n_proj_store_rev: block -> Z -> (list Values.val) -> mem -> mem -> Prop :=
| Mem_last_ind: forall m b ofs v m', 
    Mem.store Mint32 m b ofs v = Some m' ->
    mem_after_n_proj_store_rev b ofs [v] m m'
| Mem_next_ind:
    forall b ofs vs v m m' m'', 
    mem_after_n_proj_store_rev b (ofs + int_size) vs m m' ->
    Mem.store Mint32 m' b ofs v = Some m'' ->
    mem_after_n_proj_store_rev b ofs (v::vs) m m''.
  
Theorem set_commute:
  forall A (vx vy:A) (x y:positive) rho, 
    x <> y -> 
    M.set x vx (M.set y vy rho) = M.set y vy  (M.set x vx rho). 
Proof.
  induction x; intros; simpl; destruct y; try solve [simpl; destruct rho; reflexivity].
  - simpl.  destruct rho. rewrite IHx. reflexivity. intro. apply H. subst. auto.
      rewrite IHx. reflexivity. intro; apply H; subst; auto.
  - simpl. destruct rho. rewrite IHx. reflexivity. intro. apply H. subst; auto.
    rewrite IHx. reflexivity. intro; apply H; subst; auto.
  - exfalso. auto.
Qed.
  
(*      
Theorem mem_of_Forall_nth_projection_rev:
  forall x lenv b ofs f, 
    M.get x lenv = Some (Vptr b ofs) ->
    forall a l s m k,
(*       (0 <= Z.of_nat (List.length l) <= Int.max_unsigned)%Z -> *)
      (forall j, 0 <= j <  a -> Mem.valid_access m Mint32 b ((Int.unsigned ofs) + int_size * j) Writable)%Z ->
      forall vs ,
        (Z.of_nat (length vs) <= a )%Z ->
        Forall_statements_in_seq_rev
          (is_nth_projection_of_x x) l s (length vs - 1) ->              
      Forall2 (get_var_or_funvar lenv) l vs ->
      exists m', m_tstep2 (globalenv p) (State f s k empty_env lenv m)
               (State f Sskip k empty_env lenv m') /\ 
      mem_after_n_proj_store_rev b ((Int.unsigned ofs) + int_size * (a - (Z.of_nat (length vs)))) vs m m'.
Proof.
  intros x lenv b ofs f Hxlenv a_l;
  induction l; intros  s m k Hil_max vs Hvs_a H_s Hl_vs; inv H_s. 
  - destruct vs. inv Hl_vs.
    inv Hl_vs. inv H6. inv H3.
    admit.
  - destruct vs. inv Hl_vs.
    inv Hl_vs.
    simpl length in H2.
    replace n with (length vs - 1) in H4 by omega.
    simpl length in *. 
    rewrite Nat2Z.inj_succ in *.
    eapply IHl with (m := m) in H4; eauto. 

    
    assert (Hvas:Mem.valid_access m Mint32 b (Int.unsigned ofs + int_size * (a_l - Z.succ (Z.of_nat (length vs)))) Writable).
    apply Hil_max. omega.
    assert (Hvra := Mem.valid_access_store m Mint32 b  (Int.unsigned ofs + int_size * (a_l - Z.succ (Z.of_nat (length vs)))) v Hvas).
    destruct Hvra as [m2 Hm2].    
    eapply IHl with (m := m2) in H4; eauto.
    Focus 2. admit.

    destruct H4 as [m3 [Hs3 Hm3]].
    
    exists m3. split. Focus 2.
    econstructor. 
    rewrite <- Z.add_assoc.
    replace  (int_size * (a_l - Z.succ (Z.of_nat (@length Values.val vs))) + int_size)%Z with
        (int_size * (a_l - (Z.of_nat (@length Values.val vs))))%Z. apply Hm.
    int_red. omega.
    apply Hm3.
    
    *)     

    
Theorem mem_of_Forall_nth_projection_cast:
  forall x lenv b ofs f, 
    M.get x lenv = Some (Vptr b ofs) ->
    forall l s i m k,
      (0 <= i /\ i + (Z.of_nat (List.length l)) <= Int.max_unsigned )%Z ->
      (forall j, 0 <= j < i + Z.of_nat (List.length l) -> Mem.valid_access m Mint32 b (Int.unsigned (Int.add ofs (Int.repr  (int_size * j)))) Writable)%Z ->
      Forall_statements_in_seq'
        (is_nth_projection_of_x x) l s i ->
      forall vs, 
      Forall2 (get_var_or_funvar lenv) l vs ->
      exists m', m_tstep2 (globalenv p) (State f s k empty_env lenv m)
               (State f Sskip k empty_env lenv m') /\ 
      mem_after_n_proj_store_cast b (Int.unsigned ofs) vs i m m'.
Proof.
  intros x lenv b ofs f Hxlenv.
  induction l; intros s i m k Hil_max; intros.
  - (* empty -- impossible *)
    inv H1. inv H0. 
  -   assert (length (a :: l) = length vs) by (eapply Forall2_length'; eauto). rewrite H2 in *. clear H2.
      assert (Hi_range : uint_range i) by solve_uint_range.
     inv H1.
     assert (Hvas :  Mem.valid_access m Mint32 b
                                      (Int.unsigned (Int.add ofs (Int.repr (4 * i))))
                                      Writable).
     apply H. simpl. split.
     omega.
     rewrite Zplus_0_r_reverse with (n := i) at 1.
     apply Zplus_lt_compat_l.
     apply Pos2Z.is_pos.
     assert (Hvra := Mem.valid_access_store m Mint32 b  (Int.unsigned (Int.add ofs (Int.repr (4* i)))) y Hvas).
     destruct Hvra as [m2 Hsm2].        
     inv H0.
     + (* last statement *)
       inv H6.
       inv H8.
       exists m2.
       split.
       Focus 2.
       constructor. rewrite Int.repr_unsigned. auto.
       inv H0.
       * inv H4.
         Focus 2. exfalso. rewrite H1 in H0. inv H0.
         rewrite H1 in H0; inv H0.
         constructor. econstructor.
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         constructor.
         constructor. econstructor.  apply eval_Evar_global.  apply M.gempty.
         apply H1. constructor. constructor. constructor.
         eapply assign_loc_value. Focus 2.
         rewrite int_z_mul.  eauto. solve_uint_range.
         constructor.
       * inv H4. exfalso; rewrite H1 in H0; inv H0.         
         constructor. eapply step_assign with (v2 := y) (v := y). 
         constructor. econstructor. econstructor.
         econstructor. apply Hxlenv. constructor.
         constructor. constructor. constructor. apply H2.
         simpl. destruct y; inv H3; auto.
         eapply assign_loc_value. Focus 2.
         rewrite int_z_mul. eauto. solve_uint_range. 
         constructor.
     +  (* IH *)
       inv H9.
       eapply IHl with (m := m2) in H5; eauto. destruct H5 as [m3 [H5a H5b]]. exists m3.       
       split. Focus 2.
       econstructor. rewrite Int.repr_unsigned. apply Hsm2. apply H5b.

       inv H0.
       * inv H4.
         Focus 2. exfalso; rewrite H1 in H0; inv H0.
         rewrite H1 in H0; inv H0.
         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. econstructor.
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor. econstructor.          
         apply eval_Evar_global.  apply M.gempty. eauto.  constructor. constructor.
         constructor.  eapply assign_loc_value. constructor.
         rewrite int_z_mul. eauto. solve_uint_range.
         eapply t_trans. constructor. constructor.
         apply H5a.
       * inv H4. exfalso; rewrite H1 in H0; inv H0.
         eapply t_trans.
         econstructor.  constructor.
         eapply t_trans. constructor. eapply step_assign with (v2 := y) (v := y). 
         constructor. econstructor. econstructor. constructor. eauto. constructor.
         constructor. constructor. econstructor. auto. simpl.
         destruct y; inv H3; auto.
         eapply assign_loc_value. Focus 2. rewrite int_z_mul. apply Hsm2. solve_uint_range.  constructor.
         eapply t_trans. constructor. constructor.
         apply H5a.
       * destruct Hil_max.
         split. apply Z.lt_le_incl.  apply Zle_lt_succ. auto.
         simpl in H2. rewrite Zpos_P_of_succ_nat in H2. rewrite Z.add_succ_comm. 
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).         
         rewrite Hll' in *. auto.
       * intros.
         eapply Mem.store_valid_access_1. apply Hsm2.
         apply H. simpl.
         rewrite Zpos_P_of_succ_nat.
         assert (Hll' : length l = length l') by (eapply Forall2_length'; eauto).         
         rewrite Hll' in *. 
         omega.
Qed.         







End RELATION.


 

Section THEOREM.



  (* same as L6_to_Clight *)
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

  Axiom disjointIdent: NoDup (argsIdent::allocIdent::limitIdent::gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).
  

(*
    Variable cenv:L6.cps.cEnv.
  Variable fenv:L6.cps.fEnv.
  Variable finfo_env: M.t positive. (* map from a function name to its type info *)
  Variable p:program.
  
  
  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t cRep.
*)


  (* TODO: move this to cps_util *)
  Definition Forall_constructors_in_e (P: var -> cTag -> list var -> Prop) (e:exp) := 
    forall x t  ys e',
      subterm_or_eq (Econstr x t ys e') e -> P x t ys.
      

  Definition Forall_projections_in_e (P: var -> cTag -> N -> var -> Prop) (e:exp) :=
    forall x t n v e',
      subterm_or_eq (Eproj x t n v e') e -> P x t n v.
  
  (* Note: the fundefs in P is the whole bundle, not the rest of the list *)
  Definition Forall_functions_in_e (P: var -> fTag -> list var -> exp ->  fundefs -> Prop) (e:exp) :=
    forall fds e' f t xs e'',  subterm_or_eq (Efun fds e') e ->
                               fun_in_fundefs fds (f, t, xs, e'') ->
                               P f t xs e'' fds.

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
  Definition correct_cenv_of_exp: L6.cps.cEnv -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (name, it, a, n) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.
  
  Definition correct_ienv_of_cenv: L6.cps.cEnv -> iEnv -> Prop :=
    fun cenv ienv =>
      forall x, forall i n t name, M.get x cenv = Some (name, i, n, t) ->
                                   exists cl, M.get i ienv = Some cl /\ List.In (x, n) cl /\ ~ (exists n', List.In (x, n') cl).
  

  Inductive correct_crep (cenv:cEnv) (ienv:iEnv) : cTag -> cRep -> Prop :=
  | rep_enum :
      forall c name it n' n cl,
        M.get c cenv = Some (name, it, 0%N, n') ->
        M.get it ienv = Some cl ->
        getEnumOrdinal c cl = Some n ->
      correct_crep cenv ienv c (enum n)
  | rep_boxed:
      forall c name it a n' n cl,
        M.get c cenv = Some (name, it, (Npos a), n') ->
        M.get it ienv = Some cl ->
        getBoxedOrdinal c cl = Some n ->
      correct_crep cenv ienv c (boxed n (Npos a)).

  (* also need to go the other way around: if in crep, then in cenv*) 
  Definition correct_crep_of_env: L6.cps.cEnv -> iEnv -> M.t cRep -> Prop :=
    fun cenv ienv crep_env =>
      (forall c name it a n,
        M.get c cenv = Some (name, it, a, n) ->
        exists crep, M.get c crep_env = Some crep /\
                     correct_crep cenv ienv c crep) /\
      (forall c crep, M.get c crep_env = Some crep ->
                     correct_crep cenv ienv c crep).


  Definition correct_envs: cEnv -> iEnv -> M.t cRep -> exp -> Prop :=
    fun cenv ienv crep_env e =>
      correct_ienv_of_cenv cenv ienv /\
      correct_cenv_of_exp cenv e /\
      correct_crep_of_env cenv ienv crep_env. 
   
  Theorem correct_envs_subterm:
    forall cenv ienv crep e,
           correct_envs cenv ienv crep e ->
    forall e', subterm_e e' e ->
               correct_envs cenv ienv crep e'.
  Proof.
    intros.
    inv H. inv H2. split; auto.
    split; auto.
    eapply Forall_constructors_subterm; eauto.
  Qed.    
     
  (* 
   correct_tinfo alloc_id limit_id args_id alloc_max le m
  > alloc and limit are respectively valid and weak-valid pointers in memory, alloc is at least max before limit_id
  > args points to an array of size max_args in memory before alloc 

limit might be on the edge of current memory so weak_valid, alloc and args are pointing in mem. the int is the max number of blocks allocated by the function 
 

   *)
  

Definition correct_tinfo: positive -> positive -> positive -> Z -> temp_env ->  mem  -> Prop :=
  fun alloc_p limit_p args_p max_alloc lenv m  =>
    exists alloc_b alloc_ofs limit_ofs args_b args_ofs,
      M.get alloc_p lenv = Some (Vptr alloc_b alloc_ofs) /\

      (* the max int blocks after alloc are Writable *)
      (forall i, 0 <= i < max_alloc  ->   Mem.valid_access m Mint32 alloc_b (Int.unsigned (Int.add alloc_ofs (Int.repr (int_size *  i)))) Writable )%Z /\
      M.get limit_p lenv = Some (Vptr alloc_b limit_ofs) /\
      (* alloc is at least max blocks from limit *)
      ((Int.unsigned alloc_ofs) + int_size * max_alloc <=  Int.unsigned limit_ofs)%Z /\
      M.get args_p lenv = Some (Vptr args_b args_ofs) /\
      (* args is in a different block from alloc *) 
      args_b <> alloc_b /\
      (* the max_args int blocks after args are Writable *)
      ((Int.unsigned args_ofs)+ int_size * max_args <= Int.max_unsigned)%Z  /\
      (forall i, 0 <= i < max_args ->  Mem.valid_access m Mint32 args_b (Int.unsigned (Int.add args_ofs (Int.mul (Int.repr int_size) (Int.repr i))))  Writable)%Z.

    
   
Theorem correct_tinfo_mono:
  forall  alloc limit args z lenv m,
    correct_tinfo alloc limit args z lenv m ->
    forall z', 
      (0 <= z' <= z)%Z ->
    correct_tinfo alloc limit args z' lenv m. 
Proof.
  intros.
  inv H; destructAll.
  do 5 eexists.
  split; eauto.
  split; eauto.
  intros. 
  assert (0 <= i < z)%Z by omega.
  specialize (H2 _ H10).
  auto.
  split; eauto.
   split; auto. 
  etransitivity.
  Focus 2. eauto. 
  apply Zplus_le_compat_l.
  apply OrdersEx.Z_as_OT.mul_le_mono_pos_l.
  unfold int_size. simpl. omega. omega.
  split; eauto.
Qed.

    
Theorem correct_tinfo_not_protected:
  forall alloc limit args z lenv m,
  correct_tinfo alloc limit args z lenv m ->
  forall x v, 
  ~ is_protected_id args alloc limit x ->
  correct_tinfo alloc limit args z (M.set x v lenv) m. 
Proof.
  intros.
  destruct H as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs H]]]]].
  exists alloc_b, alloc_ofs, limit_ofs, args_b, args_ofs.
  destructAll.
  repeat (split; auto).  
  rewrite M.gso; auto. intro. apply H0. left; auto. 
  rewrite M.gso; auto. intro. apply H0. right; auto. 
  rewrite M.gso; auto. intro. apply H0. right; auto.
Qed.


 
Theorem correct_tinfo_valid_access:
  forall  alloc limit args z lenv m,
    correct_tinfo alloc limit args z lenv m ->
    forall m',
    (forall chunk b ofs p, Mem.valid_access m chunk b ofs p -> Mem.valid_access m' chunk b ofs p) -> 
    correct_tinfo alloc limit args z lenv m'. 
Proof.
  intros.
  unfold correct_tinfo in H.
  destruct H as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [Hget_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args Hrange_args]]]]]]]]]]]].
  do 5 eexists.
  split. eauto.
  split.
  intros. apply H0.  
  eapply Hrange_alloc; eauto.
  split. eauto.
  split. eauto.
  split. eauto.
  split. eauto.
  split. eauto.
  intros.
  apply H0.
  eapply Hrange_args; eauto.  
Qed.

Corollary correct_tinfo_after_store:
  forall  alloc limit args z lenv m,
    correct_tinfo alloc limit args z lenv m ->
    forall m' chunk b ofs v,
      Mem.store chunk m b ofs v = Some m' ->
    correct_tinfo alloc limit args z lenv m'. 
Proof. 
  intros. 
  eapply correct_tinfo_valid_access.
  apply H.
  eapply Mem.store_valid_access_1. eauto.
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
      Focus 2. apply H9.
      eapply Mem.store_valid_access_1; eauto.
Qed.      
      

Corollary correct_tinfo_after_nstore:
  forall  vs alloc limit args z lenv m m' b ofs i,
    correct_tinfo alloc limit args z lenv m ->
      mem_after_n_proj_store b ofs vs i m m' ->
      correct_tinfo alloc limit args z lenv m'. 
Proof.
  induction vs; intros.
  - inv H0.
  -   inv H0.
      + eapply correct_tinfo_after_store; eauto. 
      + eapply IHvs. Focus 2. apply H9.
        eapply correct_tinfo_after_store; eauto.
Qed.         
         
        
 
         
  (* given a program (which at top level is the certicoq translation of e... 
TODO: additional constraints on the environment(s), top level statement, f k etc...
*)


Definition repr_expr_L6_L7_id := repr_expr_L6_L7 argsIdent allocIdent threadInfIdent tinfIdent
     isptrIdent caseIdent.


Definition rel_mem_L6_L7_id := rel_mem_L6_L7 argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent
   isptrIdent caseIdent.


Definition repr_val_L_L6_L7_id := repr_val_L_L6_L7 argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent.

 
Definition protected_id_not_bound_id := protected_id_not_bound argsIdent allocIdent limitIdent.


Theorem Z_non_neg_add:
        forall n m p, 
        (n <= m -> 0 <= p -> n <= p + m)%Z.
Proof.   
  intros.
  etransitivity. eauto. omega.
Qed.
  
(* ident[n] contains either a Vint representing an enum or an integer OR a pointer to a function or the boxed representation of v *)
Inductive nth_arg_rel_L6_L7 (fenv:fEnv) (finfo_env:M.t positive) (p:program) (rep_env: M.t cRep) : L6.eval.env -> positive -> temp_env -> mem -> Z -> Prop :=
| is_in_and_rel:
    forall lenv args_b args_ofs rho m n x L6v L7v L,
       protected_not_in_L argsIdent allocIdent limitIdent lenv 0%Z L -> 
      (* get the value rho(x)*)
      M.get x rho = Some L6v -> 
      (* get Vargs pointer and load the value from it *)
      M.get argsIdent lenv = Some (Vptr args_b args_ofs) ->
      Mem.load Mint32 m args_b (Int.unsigned (Int.add args_ofs  (Int.mul
                   (Int.repr (sizeof (M.empty composite) uintTy))
                   (Int.repr n)))) = Some L7v ->
      (* relate both val *)
      repr_val_L_L6_L7_id fenv finfo_env p rep_env L6v m L L7v ->
          nth_arg_rel_L6_L7 fenv finfo_env p rep_env rho x lenv m n.
 
 
Theorem caseConsistent_findtag_In_cenv:
  forall cenv t e l,
    caseConsistent cenv l t ->
    findtag l t = Some e ->
    exists (a:Ast.name) (ty:iTag) (n:N) (i:N), M.get t cenv = Some (a, ty, n, i). 
Proof.
  destruct l; intros.
  - inv H0.
  - inv H. 
    exists a, ty', n, i; auto.
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
  apply Zle_bool_imp_le in x0ofsle. auto.
  apply Z.ltb_lt in ofsx0lt. auto.
  split; auto. 
  intro. inv H; auto. destruct H0.
  apply OrdersEx.Z_as_DT.ltb_nlt in ofsx0lt.
  exfalso; omega.
  split; auto. intros.
  inv H; auto.
  destruct H0.
  apply Z.leb_nle in x0ofsle. exfalso; omega.
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
    exfalso.  omega.
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
        assert (0 <= Z.of_nat n)%Z by apply Zle_0_nat.        
        assert (Hcase := Z.lt_ge_cases z' (ofs+4)%Z).
        destruct Hcase.
        right.  split; auto.  omega.
        left. right. split; auto. omega.        
    + inv H.
      rewrite <- IHn in H0.
      rewrite bind_n_after_ptr_def.
      rewrite bind_n_after_ptr_def in H0.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. destruct H0. auto. right.
      destruct H. split; auto.
      unfold int_size in *; simpl size_chunk in *.
      omega.
      rewrite bind_n_after_ptr_def.
      right.       unfold int_size in *; simpl size_chunk in *.
      destruct H0. split. auto.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l. omega.      
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
    Val.load_result Mint32 y = y.
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
      unfold int_size in *. simpl size_chunk in *.
      omega.
    + intros. apply H0.
      simpl length.
      rewrite Nat2Z.inj_succ.
      unfold int_size in *. simpl size_chunk in *.
      omega.
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
      SearchAbout Mem.store. 
    + constructor. auto.
    +    
*)
Definition arg_val_L6_L7 (fenv:fEnv) (finfo_env:M.t positive) (p:program) (rep_env: M.t cRep): L6.cps.val -> mem -> temp_env -> Prop :=
  fun v m lenv =>
      exists args_b args_ofs L7v L, M.get argsIdent lenv = Some (Vptr args_b args_ofs) /\
                                  Mem.load Mint32 m args_b (Int.unsigned (Int.add args_ofs (Int.repr int_size))) = Some L7v /\
                                  repr_val_L_L6_L7_id fenv finfo_env p rep_env v m L L7v.
 

Theorem getlist_cons :
  forall A rho v ys vs,
    @getlist A ys rho = Some (v :: vs) ->
  exists y ys', ys = y::ys' /\
                cps.M.get y rho = Some v /\ 
                getlist ys' rho = Some vs. 
Proof.
  intros. destruct ys as [ | y ys'].
  inv H. exists y, ys'.
  split; auto.  simpl in H.
  destruct  (cps.M.get y rho).
  destruct (getlist ys' rho). inv H. auto.
  inv H. inv H.
Qed.
 
      
Theorem exists_getvar_or_funvar_list:
  forall lenv p rho L rep_env finfo_env argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fenv
         m xs vs,
            ( forall x, List.In x xs ->
                        exists v6 : cps.val,
         M.get x rho = Some v6 /\
         repr_val_id_L_L6_L7 argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fenv finfo_env
                             p rep_env v6 m L lenv x)
            ->
            getlist xs rho = Some vs  ->
            exists vs7 : list val, get_var_or_funvar_list p lenv xs = Some vs7.
Proof.  
  induction xs; intros.
  - exists nil. auto.
  - simpl in H0.
    destruct (cps.M.get a rho) eqn:Hgar.
    destruct (getlist xs rho) eqn:Hgxsr.
    inv H0.
    specialize (IHxs l).
    assert ((forall x : positive,
          List.In x xs ->
          exists v6 : cps.val,
            M.get x rho = Some v6 /\
            repr_val_id_L_L6_L7 argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0
                                fenv finfo_env p rep_env v6 m L lenv x)).
    {
      intros. apply H. constructor 2; auto.
    }
    apply IHxs in H0. destruct H0.
    assert 
      (exists v6 : cps.val,
        M.get a rho = Some v6 /\
        repr_val_id_L_L6_L7 argsIdent0 allocIdent0 limitIdent0 gcIdent0 threadInfIdent0 tinfIdent0 isptrIdent0 caseIdent0 fenv
                            finfo_env p rep_env v6 m L lenv a).
    apply H. constructor. reflexivity.
    destruct H1. destruct H1.
    rewrite H1 in Hgar. inv Hgar.
    inv H2. eexists. simpl. rewrite H0. rewrite H3. reflexivity.
    eexists. simpl. rewrite H0. rewrite H3. rewrite H4. inv H5; reflexivity. reflexivity.
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
  elim (H0 ofs0). omega. auto.
Qed.  
 

    
   

(* 
Theorem correct_tinfo_constr:
forall p lenv c max_alloc m alloc_b alloc_ofs,
  M.get allocIdent lenv = Some (Vptr alloc_b alloc_ofs) ->
  correct_tinfo allocIdent limitIdent argsIdent (max_alloc+c) lenv m ->                                                         
  correct_tinfo allocIdent limitIdent argsIdent max_alloc
              (Maps.PTree.set allocIdent
                              (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr c))))
                              lenv) m.
Proof.
  intros p lenv c max_alloc m alloc_b alloc_ofs Halloc Hc_tinfo.
  destruct Hc_tinfo as [alloc_b' [alloc_ofs' [limit_ofs' [args_b [args_ofs [Hget_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hbound_args Hrange_args]]]]]]]]]]].
  rewrite Halloc in Hget_alloc. inv Hget_alloc.
  exists alloc_b', (Int.add alloc_ofs' (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr c))), limit_ofs', args_b, args_ofs.
  split. rewrite M.gss. reflexivity.
  split.
  
  auto.
  split. rewrite M.gso. auto.
  admit.
  split. admit.
  split. rewrite M.gso. auto.
  admit.
  split. auto.
  auto.
Qed.  *)  
             
Theorem repr_bs_L6_L7_related:
  forall p rep_env cenv fenv finfo_env ienv,
  forall rho v e n, bstep_e (M.empty _) cenv rho e v n ->                    
                    correct_envs cenv ienv rep_env e ->
                    protected_id_not_bound_id rho e ->
                    unique_bindings_env rho e ->
                    functions_not_bound p e -> 
                    forall stm lenv m k max_alloc fu, repr_expr_L6_L7_id fenv p rep_env e stm ->
                                              rel_mem_L6_L7_id fenv finfo_env p rep_env e  rho m lenv ->
                                              correct_alloc e max_alloc -> 
                                              correct_tinfo allocIdent limitIdent argsIdent max_alloc lenv m ->
                                              exists m' lenv',  m_tstep2 (globalenv p) (State fu stm k empty_env lenv m) (State fu Sskip k empty_env lenv' m') /\
                                                                arg_val_L6_L7 fenv finfo_env p rep_env v m' lenv'.
Proof.
  intros p rep_env cenv fenv finfo_env ienv rho v e n Hev.
  induction Hev; intros Hc_env Hp_id Hrho_id Hf_id stm lenv m k max_alloc fu Hrepr_e Hrel_m Hc_alloc Hc_tinfo; inv Hrepr_e.
  - (* Econstr *)

    assert (Hx_not:  ~ is_protected_id argsIdent allocIdent limitIdent x). {
          intro. inv Hp_id. eapply H2; eauto.    
    }

    
    (* get the tempenv and mem after assigning the constructor *)
    assert (exists lenv' m', 
               ( clos_trans state (traceless_step2 (globalenv p))
                                     (State fu s (Kseq s' k) empty_env lenv m)  
                                     (State fu Sskip (Kseq s' k) empty_env lenv' m') )
               /\  rel_mem_L6_L7_id fenv finfo_env p rep_env e (M.set x (Vconstr t vs) rho) m' lenv'
               /\ correct_tinfo allocIdent limitIdent argsIdent (Z.of_nat (max_allocs e)) lenv' m').
    {
      inv H6.
      - (* boxed *)

        assert (Ha_l : a = N.of_nat (length ys) /\ ys <> []). {          
          assert (subterm_or_eq (Econstr x t ys e) (Econstr x t ys e)) by constructor 2.
          inv Hc_env. destruct H5.
          apply H5 in H3.   destruct (M.get t cenv) eqn:Hmc. destruct c0. destruct p0. destruct p0.
          subst.
          
          inv H6.
          assert (Hmc' := Hmc). apply H3 in Hmc. destructAll.
          rewrite H6 in H0. inv H0.
          inv H9. rewrite Hmc' in H11. inv H11. split. reflexivity.
          destruct ys. inv H2.
          intro. inv H0.
          inv H3.
        }

        
        (* 1 -> get the alloc info, steps through the assignment of the header *)
        assert (Hc_tinfo' := Hc_tinfo).
        unfold correct_tinfo in Hc_tinfo.
        destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [Hget_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args Hrange_args]]]]]]]]]]]].

        assert (~ is_protected_id argsIdent allocIdent limitIdent x).
        { intro. inv Hp_id. eapply H5; eauto. }

        assert (Hx_loc_eq : (Int.add (Int.add alloc_ofs (Int.mul (Int.repr 4) (Int.repr Z.one))) (Int.mul (Int.repr 4) (Int.repr (-1)))) = alloc_ofs). {
          rewrite Int.add_assoc.
          rewrite Int.mul_mone.
          rewrite Int.mul_one.
          rewrite Int.add_neg_zero.
          apply Int.add_zero.
        }
         
        
        assert ( {m2 : mem |  Mem.store Mint32 m alloc_b
                                      (Int.unsigned alloc_ofs) (Vint (Int.repr h)) = Some m2}). {
          apply Mem.valid_access_store.
           
          specialize (Hrange_alloc 0%Z).
          simpl in Hrange_alloc. 
          rewrite Int.add_zero in Hrange_alloc. 
          apply Hrange_alloc.
          inv Hc_alloc. simpl.  destruct ys. inv H2. simpl. split; try omega.
          apply Pos2Z.is_pos.          
        }
        destruct X as [m2 Hm2]. 
 
        assert (Hstep_m2 : clos_trans state (traceless_step2 (globalenv p))
                            (State fu
         (Ssequence
            (Ssequence
               (Ssequence
                  (Sset x
                     (Ecast
                        (add (Etempvar allocIdent (Tpointer uintTy {| attr_volatile := false; attr_alignas := None |}))
                           (c_int' Z.one uintTy)) uintTy))
                  (Sset allocIdent
                     (add (Etempvar allocIdent (Tpointer uintTy {| attr_volatile := false; attr_alignas := None |}))
                        (c_int' (Z.of_N (a + 1)) uintTy))))
               (Sassign
                  (Ederef
                     (add (Ecast (Etempvar x uintTy) (Tpointer uintTy {| attr_volatile := false; attr_alignas := None |}))
                        (c_int' (-1) intTy)) uintTy) (c_int' h uintTy))) s0) (Kseq s' k) empty_env lenv m)
                           (State fu s0 (Kseq s' k) empty_env
       (Maps.PTree.set allocIdent
          (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))))
          (Maps.PTree.set x
             (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))) lenv)) m2)).
        {
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor. econstructor.
          econstructor. constructor. eauto. constructor. constructor.
          constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          econstructor. constructor. rewrite M.gso. 
          eauto. intro. apply H3. left; auto.
          constructor. constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. econstructor. constructor. simpl. econstructor.
          econstructor. constructor. rewrite M.gso. rewrite M.gss. reflexivity.
          intro. apply H3. left; auto.
          constructor. constructor. constructor. constructor. constructor. simpl.
          econstructor. constructor. simpl.  rewrite Hx_loc_eq.
          apply Hm2.
          constructor. constructor.          
        }
        
        
        (* 2 -> use mem_of_Forall_nth_projection to step through the assignment of vs *)
        assert (Hstep_m3 := mem_of_Forall_nth_projection_cast).
        specialize (Hstep_m3 threadInfIdent p x
                             (Maps.PTree.set allocIdent
                                             (Vptr alloc_b
                                                   (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))))
                                             (Maps.PTree.set x
                                                             (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))))
                                                             lenv))
                             alloc_b
                             (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))
                             fu
                   ).
        assert (Htemp :  M.get x
               (Maps.PTree.set allocIdent
                  (Vptr alloc_b
                     (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))))
                  (Maps.PTree.set x
                     (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))) lenv)) =
             Some (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))))).
        rewrite M.gso. rewrite M.gss. reflexivity. intro; apply Hx_not. left; auto.
        specialize (Hstep_m3 Htemp ys s0 0%Z m2 (Kseq s' k)). clear Htemp.
        assert (Htemp : (0 <= 0)%Z /\ (0 + Z.of_nat (length ys) <= Int.max_unsigned)%Z ).
        {
          split. omega.
          assert (Int.unsigned limit_ofs <= Int.max_unsigned)%Z.
          assert (Htemp := Int.unsigned_range_2 limit_ofs). omega.
          etransitivity; eauto. etransitivity; eauto.
          assert (0 <= Int.unsigned alloc_ofs)%Z.
          assert (Htemp := Int.unsigned_range_2 alloc_ofs). omega.
          inv Hc_alloc.
          destruct ys. inv H2.
          simpl max_allocs.
          rewrite Nat2Z.inj_succ. 
          rewrite Nat2Z.inj_add. simpl length.
          unfold int_size.
          assert (0 <=  Z.succ (Z.of_nat (max_allocs e)))%Z by omega.
          simpl size_chunk.
          omega.
        }          
        specialize (Hstep_m3 Htemp). clear Htemp.
        assert (Htemp : (forall j : Z,
              (0 <= j < 0 + Z.of_nat (length ys))%Z ->
              Mem.valid_access m2 Mint32 alloc_b
                (Int.unsigned
                   (Int.add (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))
                            (Int.repr (int_size * j)))) Writable)). {
          intros.
          specialize (Hrange_alloc (j+1)%Z).
          
          inv Hc_alloc.  destruct ys. inv H2.          
          assert ((0 <= j + 1 <  Z.of_nat (max_allocs (Econstr x t (v0 :: ys) e)))%Z).
          simpl. simpl in H4.
          rewrite Zpos_P_of_succ_nat.
          rewrite Nat2Z.inj_add.
          rewrite Zpos_P_of_succ_nat in H4.
          rewrite Nat2Z.inj_succ. omega.
          specialize (Hrange_alloc H5).
          replace ((Int.add (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))) (Int.repr (int_size * j)))) with (Int.add alloc_ofs (Int.repr (int_size * (j + 1)))).

          eapply Mem.store_valid_access_1; eauto.
          rewrite Int.add_assoc.
          replace (Int.add (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))
                           (Int.repr (int_size * j))) with (Int.repr (int_size * (j + 1))). reflexivity.
          rewrite int_z_mul.
          rewrite int_z_add.
          rewrite Zred_factor4.
          rewrite Z.add_comm. reflexivity.
          constructor. solve_uint_range.
          constructor.
          split. unfold int_size.
          apply Z.mul_nonneg_nonneg. simpl. omega.
          omega.
          assert (Int.unsigned limit_ofs <= Int.max_unsigned)%Z.
          assert (Htemp := Int.unsigned_range_2 limit_ofs). omega.
          etransitivity. Focus 2. apply H6.
          etransitivity. Focus 2. eauto.  
          simpl max_allocs.
          rewrite Nat2Z.inj_succ.
          rewrite Nat2Z.inj_add. simpl in H4. simpl Z.of_nat.
          inv H4.
          assert (Halloc:= Int.unsigned_range  alloc_ofs).
          inv Halloc.
          rewrite <- Z.add_succ_l.          
          rewrite Z.mul_add_distr_l.
          apply Z_non_neg_add. apply Z_non_neg_add.
          apply OrdersEx.Z_as_OT.mul_le_mono_pos_l.
          unfold int_size. simpl. omega.
          omega.
          unfold int_size.
          apply Z.mul_nonneg_nonneg.
          simpl; omega. omega. auto.
          constructor.
          solve_uint_range.
          unfold Z.one. omega.
        }
        specialize (Hstep_m3 Htemp H2). clear Htemp.
        
        (* first prove that allocIdent \/ x is disjoint from ys s.t. can be ignore. then show that get_list works and that vs7 is the right thing  *)
        assert (Htemp : exists vs : list val,
             Forall2
               (get_var_or_funvar p
                  (Maps.PTree.set allocIdent
                     (Vptr alloc_b
                        (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))))
                     (Maps.PTree.set x
                        (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))))
                        lenv))) ys vs).
        {
          assert (exists vs, get_var_or_funvar_list p lenv ys = Some vs).          
          {
            
            inv Hrel_m.  destruct H4.
            eapply exists_getvar_or_funvar_list.
            Focus 2. eauto.
            intros.
            apply H5. constructor. auto.
          } 
          destruct H4 as [x0 Hgv_x0].
          exists x0.
          rewrite get_var_or_funvar_list_correct.
          rewrite <- get_var_or_funvar_list_set.
          rewrite <- get_var_or_funvar_list_set.
          auto.

          intro.
          eapply Hrho_id.
          eapply getlist_In; eauto.
          constructor.
          
          
          intro.
          inv Hp_id.
          
          assert (Hgl := getlist_In _ _ _ _ H H4). destruct Hgl.          
          specialize (H5 _ allocIdent _ H8). apply H5.
          left. auto. left; auto.          
        } 
        destruct Htemp as [vs7 Hvs7].
        specialize (Hstep_m3 vs7 Hvs7).
        destruct Hstep_m3 as [m3 Hstep_m3].
        assert (H_m2_m3 :  mem_after_n_proj_store alloc_b
                                                       (Int.unsigned (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))) vs7 0 m2 m3). {
          apply mem_after_n_proj_wo_cast.
          destruct Hstep_m3; auto.
          apply Int.unsigned_range. reflexivity.
          inv Hc_alloc.
          int_red. simpl max_allocs in Hbound_limit. destruct ys. destruct Ha_l. exfalso. auto.
          rewrite Nat2Z.inj_succ in Hbound_limit.
          rewrite Nat2Z.inj_add in Hbound_limit.

          split.
          apply Z.add_nonneg_nonneg.
          apply Int.unsigned_range.
          assert (0 <= Z.of_nat (length vs7))%Z by apply Zle_0_nat. omega.
          apply Forall2_length' in Hvs7.
          rewrite <- Hvs7 in *.
          etransitivity.
          etransitivity.
          Focus 2. apply Hbound_limit.
          rewrite int_z_mul. 
          unfold Int.add.
          rewrite Int.unsigned_repr with (z := (sizeof (globalenv p) uintTy * Z.one)%Z).
          rewrite Int.unsigned_repr.
          simpl sizeof.
          assert (0 <= Z.of_nat (max_allocs e))%Z by apply Zle_0_nat. rewrite Z.mul_succ_r.
          repeat rewrite <- Z.add_assoc.
          apply Zplus_le_compat_l.
          repeat rewrite Z.mul_add_distr_l. 
          repeat rewrite Z.add_assoc.
          unfold Z.one. 
          simpl Z.mul at 1.
          simpl Z.mul at 1.
          replace (@length positive (@cons var v0 ys)) with
              (@length var (@cons var v0 ys)). omega.
          reflexivity.
          simpl sizeof. unfold Z.one. split.
          apply Z.add_nonneg_nonneg.
          apply Int.unsigned_range. 
          omega.
          etransitivity. etransitivity.
          Focus 2. apply Hbound_limit.
          rewrite Z.mul_succ_r.
          omega.
          apply Int.unsigned_range_2. 
          solve_uint_range.
          omega.
          simpl sizeof. solve_uint_range.
          unfold Z.one.
          omega. apply Int.unsigned_range_2.
          destruct Hstep_m3.
          auto.
        }          
        
        

         
        do 2 eexists.
        split.
        eapply t_trans.
        apply Hstep_m2.
        apply Hstep_m3.
        split.
        { (* rel_mem after adding the new constructor *)
          inversion Hrel_m as [L [Hrel_pL Hrel_mL]].
          assert (Hbound_max:
                    (Int.unsigned alloc_ofs + int_size * (Z.succ (Z.of_nat (max_allocs e)) + Z.of_N a) <= Int.unsigned limit_ofs)%Z). {
            inv Hc_alloc.
            simpl max_allocs in Hbound_limit.
            destruct ys. exfalso.
            destruct Ha_l. auto. 
            
            rewrite Nat2Z.inj_succ in Hbound_limit.
            rewrite Nat2Z.inj_add in Hbound_limit.
            destruct Ha_l.
            
            replace (Z.of_N a) with (Z.of_nat (length (v0 :: ys))).  
            rewrite  Z.add_succ_l. auto.                   
            rewrite H4.

            rewrite nat_N_Z. reflexivity.            
          }
          assert (H_unchanged_m2_m3: Mem.unchanged_on L m2 m3). {                          
            inv Hrel_pL.
            destructAll.
            rewrite H4 in Hget_alloc. inv Hget_alloc.

            eapply mem_after_n_proj_store_unchanged.
            eauto.            
            intros.
            apply H10.
            simpl max_allocs in *.
            destruct ys.
            exfalso; auto.
            simpl length. unfold int_size in *; simpl size_chunk in *.
            simpl sizeof in *.
            simpl length in Hbound_max.
            rewrite Nat2Z.inj_succ in *.
            rewrite nat_N_Z in Hbound_max.
            rewrite Nat2Z.inj_succ in *.
            rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_succ.
            unfold Int.add.
            rewrite Int.unsigned_repr with (z := (4 * Z.succ (Z.of_nat (max_allocs e) + Z.succ (Z.of_nat (length ys))))%Z). 
            rewrite Int.unsigned_repr.
            assert ( (Int.unsigned (Int.add alloc_ofs (Int.mul (Int.repr 4) (Int.repr Z.one))) = Int.unsigned alloc_ofs + 4)%Z).

            unfold Int.mul. unfold Z.one. rewrite Int.unsigned_repr.
            rewrite Int.unsigned_repr. unfold Int.add.
            simpl Z.mul. 
            rewrite Int.unsigned_repr with (z := 4%Z).
            rewrite Int.unsigned_repr.
            reflexivity.

            split.
            apply Z_non_neg_add. omega. apply Int.unsigned_range.
            etransitivity. etransitivity. Focus 2. apply Hbound_max.
            rewrite Z.add_succ_l.            
            rewrite Z.mul_succ_r.
            omega.
            apply Int.unsigned_range_2.
            
            
            unfold Int.max_unsigned; simpl; omega.
            unfold Int.max_unsigned; simpl; omega.
            unfold Int.max_unsigned; simpl; omega.
            
            rewrite H14 in *. apply Forall2_length' in Hvs7. rewrite <- Hvs7 in H8.
            simpl length in H8.
            rewrite Nat2Z.inj_succ in *. split.
            omega.
            rewrite Z.mul_succ_r.
            destruct H8.
            eapply Z.lt_le_trans.
            apply H15.
            assert (0 <=  Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.            
            assert (0 <= Z.of_nat (max_allocs e))%Z by apply Zle_0_nat.
            assert ((@length positive ys) = (@length var ys)) by reflexivity.
            omega.
            
            split.
            apply Z_non_neg_add. omega.
            apply Int.unsigned_range.
            etransitivity. etransitivity. Focus 2.
            apply Hbound_max.
            omega. apply Int.unsigned_range_2.
            split. omega.
            etransitivity. etransitivity. Focus 2.
            apply Hbound_max.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            omega.
            apply Int.unsigned_range_2.
          } 
          assert (H_unchanged_m_m3:   Mem.unchanged_on L m m3). {
             
            inv Hrel_pL.
            destructAll.
            rewrite H4 in Hget_alloc. inv Hget_alloc.

            eapply Mem.unchanged_on_trans.
            eapply Mem.store_unchanged_on.
 
            eauto.
            intros.
            apply H10.
            unfold Int.add.
            simpl max_allocs. destruct ys. exfalso; auto.
            simpl length.
            
            rewrite Int.unsigned_repr with (z :=  (int_size * Z.of_nat (S (max_allocs e + S (length ys))))%Z).
            rewrite Int.unsigned_repr.
            rewrite Nat2Z.inj_succ.
            unfold int_size. simpl size_chunk in *.
            rewrite Z.mul_succ_r.
            assert (0 <= Z.of_nat (max_allocs e + S (length ys)))%Z by apply Zle_0_nat.
            omega.
            unfold int_size in *; simpl size_chunk in *.
            split.
            apply Z_non_neg_add. omega.
            apply Int.unsigned_range.
            etransitivity. etransitivity.
            Focus 2. apply Hbound_max.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            simpl length.
            rewrite Nnat.Nat2N.inj_succ.
             
            rewrite Nat2Z.inj_succ.
            rewrite N2Z.inj_succ.
            rewrite nat_N_Z.
            omega.
            apply Int.unsigned_range_2.
            unfold int_size in *; simpl size_chunk in *.
            split. omega.
            etransitivity.
            etransitivity.
            Focus 2. apply Hbound_max.
            simpl length.
            rewrite Nnat.Nat2N.inj_succ.           
            rewrite Nat2Z.inj_succ.
            rewrite N2Z.inj_succ.
            rewrite nat_N_Z.
            rewrite Nat2Z.inj_add.
            rewrite Nat2Z.inj_succ.
            assert (0 <=  Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            omega.
            apply Int.unsigned_range_2.
            auto.
              }
          
          exists (bind_n_after_ptr (Z.of_N (a+1) * 4) alloc_b (Int.unsigned alloc_ofs)  L).
          split.
          - (* protected okay since only took the space from Econstr to e *)
            exists alloc_b, (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))),
            limit_ofs, args_b, args_ofs.
            assert (H_dj := disjointIdent).            
            repeat split. 
            + rewrite M.gss. reflexivity.
            + intros.
              inv Hrel_pL.
              destructAll.
              inv Hc_alloc.
              destruct ys. exfalso; auto.
              simpl max_allocs in *.
              int_red.
              rewrite Nat2Z.inj_succ in Hbound_limit.
              rewrite Nat2Z.inj_add in Hbound_limit.
              rewrite H5 in Hget_alloc. inv Hget_alloc. intro.
              apply bind_n_after_ptr_def in H10.
              rewrite Int.add_unsigned with (x := alloc_ofs) in * .
              replace (Int.unsigned
                         (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (N.of_nat (@length var (v0 :: ys)) + 1))))) with
                  (4 * Z.of_nat (length (v0 :: ys)) + 4)%Z in *.
              unfold Int.add in H6.                     
              replace  (Int.unsigned (Int.repr (4 * Z.of_nat (max_allocs e)))) with
                  (4 * Z.of_nat (max_allocs e))%Z in *.                            
              replace (Int.unsigned (Int.repr (Int.unsigned alloc_ofs + (4 * Z.of_nat (length (v0 :: ys)) + 4)))) with
                  (Int.unsigned alloc_ofs + (4 * Z.of_nat (length (v0 :: ys)) + 4))%Z in *.
              rewrite Int.unsigned_repr in H6.
              inv H10.
              * revert H16.
                eapply H12.
                rewrite Int.unsigned_repr with (z := (4 * Z.of_nat (S (max_allocs e + S (length ys))))%Z).
                rewrite Int.unsigned_repr.
                simpl length in *.
                rewrite Nat2Z.inj_succ.
                rewrite Nat2Z.inj_add.
                omega.
                split.
                apply Z_non_neg_add. omega. apply Int.unsigned_range.
                rewrite Nat2Z.inj_succ.
                rewrite Nat2Z.inj_add.
                etransitivity; eauto. apply Int.unsigned_range_2.
                split.
                omega. 
                rewrite Nat2Z.inj_succ.
                rewrite Nat2Z.inj_add.
                etransitivity. etransitivity.
                Focus 2. apply Hbound_limit.
                assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
                omega.
                apply Int.unsigned_range_2.
              * inv H16.
                rewrite N2Z.inj_add in H17.
                rewrite nat_N_Z in H17.
                simpl Z.of_N in *.
                omega.
                 
              * assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range. split.
                omega.
                etransitivity. etransitivity.
                Focus 2. apply Hbound_limit. simpl length. rewrite Nat2Z.inj_succ. omega.
                apply Int.unsigned_range_2.
              * rewrite Int.unsigned_repr. reflexivity.
                split. apply Z_non_neg_add. omega. apply Int.unsigned_range.
                etransitivity.
                etransitivity. Focus 2. apply Hbound_limit. simpl length.
                omega.
                apply Int.unsigned_range_2.
              * rewrite Int.unsigned_repr. reflexivity.
                split. omega. 
                etransitivity.
                etransitivity. Focus 2. apply Hbound_limit. simpl length.
                rewrite Z.mul_succ_r.
                assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.                
                omega.
                apply Int.unsigned_range_2.
              * simpl sizeof.
                unfold Int.mul.
                rewrite Int.unsigned_repr with (z :=  (Z.of_N (N.of_nat (length (v0 :: ys)) + 1))).
                rewrite Int.unsigned_repr with (z := 4%Z).
                rewrite Int.unsigned_repr. reflexivity.
                split. apply Z.mul_nonneg_nonneg. omega.
                apply N2Z.is_nonneg.
                etransitivity. etransitivity. Focus 2. apply Hbound_limit. simpl length.
                assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
                rewrite Z.mul_succ_r.
                rewrite N2Z.inj_add.
                rewrite nat_N_Z.
                simpl Z.of_N.
                rewrite Z.mul_add_distr_l.
                rewrite Z.mul_add_distr_l. omega.
                apply Int.unsigned_range_2.
                unfold Int.max_unsigned. simpl. omega.
                rewrite N2Z.inj_add.
                rewrite nat_N_Z.
                simpl Z.of_N.
                split.
                apply Z_non_neg_add. omega. omega.
                etransitivity. etransitivity. Focus 2. apply Hbound_limit.
                simpl length.
                rewrite Z.mul_succ_r.
                assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
                omega.
                apply Int.unsigned_range_2.
            + rewrite M.gso. rewrite M.gso.
              auto.
              intro.
              apply H3.
              subst. right. auto.
              intro. subst.
              clear H4. inv H_dj.
              inv H8.
              apply H9. constructor.
              auto.
            + rewrite M.gso. rewrite M.gso.
              auto. intro.
              apply H3. subst. right; auto.
              intro; subst. clear H4. inv H_dj. apply H6; constructor; auto.
            + intros.
              inv Hrel_pL.
              destructAll. 
              rewrite H16 in Hget_args; inv Hget_args.
              intro.
              apply bind_n_after_ptr_def in H12. inv H12.
              revert H18. apply H17 with (z := z); auto.
              destruct H18.
              apply Hdj_args.
              auto.
          - intros. destruct (var_dec x0 x).
            + (* x0 = x *)
              subst. eexists. split.
              rewrite M.gss. reflexivity.
              eapply RVid_V.
              apply Hf_id. constructor. (* x is not global *)
              rewrite M.gso. rewrite M.gss. reflexivity.
              intro. apply H3. subst. left. auto.
              eapply RSconstr_boxed_v.
              *  eauto.
              *  rewrite Int.sub_add_opp.                 
                rewrite Int.mul_one. 
                rewrite Int.add_assoc.
                rewrite Int.add_neg_zero.
                rewrite Int.add_zero. intros.
                rewrite bind_n_after_ptr_def. right. split; auto.
                simpl size_chunk in *.
                rewrite N2Z.inj_add.
                simpl Z.of_N.
                rewrite Z.mul_add_distr_r.
                rewrite Z.add_assoc.
                simpl Z.mul.
                assert (0 <=  Z.of_N a)%Z by apply N2Z.is_nonneg. 
                omega.
              * (* skip m3, (repr H) is what is stored for m2 *)
                rewrite Int.sub_add_opp.
                rewrite Int.mul_one. 
                rewrite Int.add_assoc.
                rewrite Int.add_neg_zero.
                rewrite Int.add_zero.
                destruct Hstep_m3 as [Hstep_m3_s Hstep_m3_mem].
                apply Mem.load_store_same in Hm2. simpl in Hm2.
                erewrite mem_after_n_proj_store_load.
                apply Hm2.
                apply H_m2_m3.
                right. left.
                simpl.
                rewrite Int.mul_one.
                unfold Int.add.
                rewrite Int.unsigned_repr with (z := 4%Z).
                rewrite Int.unsigned_repr.
                unfold int_size; simpl.
                omega.
                split.
                apply Z_non_neg_add.
                omega. apply Int.unsigned_range.
                etransitivity. etransitivity.
                Focus 2. apply Hbound_limit.
                inv Hc_alloc. simpl max_allocs.
                destruct ys.  inv Ha_l. exfalso; auto.
                rewrite Nat2Z.inj_succ.
                rewrite Z.mul_succ_r.
                int_red.
                assert (0 <=  Z.of_nat (max_allocs e + length (v0 :: ys))%nat)%Z by       apply Zle_0_nat.
                omega.
                apply Int.unsigned_range_2.
                unfold Int.max_unsigned.                
                simpl. omega.
              * unfold boxed_header.
                eapply Int.eqm_trans.
                Focus 2.
                apply H1.
                apply Int.eqm_unsigned_repr_l.
                apply Int.eqm_refl.
                              * (* todo: theorem linking repr_val_ptr_list and mem_after_n_proj_store *)
                (* need to clear a few things here before inducting on vs *)
                { clear IHHev.
                  assert (H_alloc4 :(Int.unsigned (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))
                                     = (Int.unsigned alloc_ofs) + 4)%Z).
                  {
                    simpl sizeof. rewrite Int.mul_one.
                    rewrite Int.add_unsigned.
                    rewrite Int.unsigned_repr with (z := 4%Z).
                    rewrite Int.unsigned_repr. auto.
                    inv Hc_alloc.
                    split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply Int.unsigned_range. omega.
                    etransitivity. Focus 2. eapply Int.unsigned_range_2. etransitivity. Focus 2. apply Hbound_limit.
                    simpl max_allocs. destruct ys. exfalso. apply Ha_l. auto.
                    rewrite Nat2Z.inj_succ.
                    rewrite Z.mul_succ_r.
                    rewrite Z.add_assoc. unfold int_size; simpl size_chunk.
                    assert (0 <=  Int.unsigned alloc_ofs)%Z.
                    apply Int.unsigned_range.
                    assert (0 <= Z.of_nat (max_allocs e + length (v0 :: ys)))%Z by 
                    apply Zle_0_nat.
                    omega.
                    unfold Int.max_unsigned. simpl. omega.
                  }                    
                  


                    
                  rewrite repr_val_ptr_list_Z.
                  Focus 2.
                  rewrite H_alloc4. 
                    unfold int_size in *; simpl size_chunk in *.
                    inv Hc_alloc.
                    split. apply OrdersEx.Z_as_OT.add_nonneg_nonneg. apply OrdersEx.Z_as_OT.add_nonneg_nonneg.
                    apply Int.unsigned_range. omega.  omega.
                    etransitivity. Focus 2. eapply Int.unsigned_range_2. etransitivity. Focus 2. apply Hbound_limit.
                    simpl max_allocs.
                    apply getlist_length_eq in H. 
                    destruct ys. exfalso. apply Ha_l. auto.
                    rewrite Nat2Z.inj_succ.
                    rewrite Nat2Z.inj_add.
                    simpl length.
                    simpl in H. rewrite <- H.
                    rewrite Nat2Z.inj_succ.
                    rewrite Nat2Z.inj_succ.
                    assert (0 <=  Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.                    
                    rewrite Z.mul_succ_r.
                    rewrite Z.mul_add_distr_l.
                    rewrite Z.mul_succ_r.
                    rewrite Z.add_assoc.
                    assert (0 <= (Z.of_nat (length ys)))%Z by                     apply Zle_0_nat.
                    assert (0 <= (Z.of_nat (max_allocs e)))%Z by                     apply Zle_0_nat.
                    rewrite Z.mul_succ_l.
                    rewrite <- Z.add_assoc.
                    rewrite <- Z.add_assoc.
                    apply Zplus_le_compat_l.
                    rewrite Z.add_comm.
                    rewrite Z.add_assoc.
                    rewrite Z.mul_comm.
                    rewrite <- Z.add_0_l at 1.
                    replace  (4 * Z.of_nat (max_allocs e) + 4 * Z.of_nat (length ys) + 4 + 4)%Z with  (4 * Z.of_nat (max_allocs e) + ( 4 * Z.of_nat (length ys) + 4 + 4))%Z by omega.

                    apply Z.add_le_mono.
                    omega. reflexivity.
                    (* done *)

                    
                    rewrite H_alloc4.
                    rewrite H_alloc4 in H_m2_m3.
                  clear H_alloc4.

                  


                  

                  
                  
                  (* creating an intermediate memory representing the work done so far, with equality that will be cleared before induction *)
                  assert (H_mmid: exists m_mid vs1 vs2, mem_after_n_proj_snoc alloc_b (Int.unsigned alloc_ofs + 4) vs1 m2 m_mid /\
                                                        (rev (vs1) ++ vs2 = vs7) /\ vs7 = vs2 /\ vs1 = [] /\  m2 = m_mid). {
                    
                    exists m2, [], vs7. split. constructor.
                    auto.
                  }
                  destruct H_mmid as [m_mid [vs1 [vs2 [H_m2_mmid [H_rev_vs7 [H_eq_vs7 [H_eq_vs1 H_eq_m2]]]]]]].
                  rewrite H_eq_vs7 in H_m2_m3.
                  rewrite H_eq_m2 in H_m2_m3.
                  rewrite H_eq_vs7 in Hvs7.
                  replace 0%Z with (Z.of_nat (length vs1)) in H_m2_m3 by (rewrite H_eq_vs1; auto).
                  
                  
                  

                  


                  
                  (* IH needs to walk on the total (a) size of ys *)
                  (* TODO: update the walk! show that this works with intermediate mem *)
                  assert (Hays: (Z.of_N a - Z.of_nat (length ys) = 0)%Z).
                  destruct Ha_l; subst. rewrite nat_N_Z.
                  omega.


                  replace (Int.unsigned alloc_ofs + 4)%Z with  (Int.unsigned alloc_ofs + 4 + 4 * Z.of_nat (length vs1))%Z by (rewrite H_eq_vs1; simpl; omega).
                  

                  assert (Hrel_pL' :  protected_not_in_L argsIdent allocIdent limitIdent lenv (Z.succ (Z.of_nat (max_allocs e)) + Z.of_nat (length vs7) )%Z L). {                                        
                    simpl in Hrel_pL. destruct ys. exfalso; destruct Ha_l. apply H6; auto.
                    rewrite Nat2Z.inj_succ in Hrel_pL.
                    rewrite Nat2Z.inj_add in Hrel_pL.
                    replace (Z.of_nat (length vs7)) with (Z.of_nat (length (v0 :: ys))).
                    rewrite  Z.add_succ_l. auto.
                    rewrite H_eq_vs7.
                    apply Forall2_length' in Hvs7. rewrite <- Hvs7; auto.
                    
                  }
                  assert (forall y, List.In y ys -> 
                                    exists v6 : cps.val,
              M.get y rho = Some v6 /\
              repr_val_id_L_L6_L7 argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fenv
                                  finfo_env p rep_env v6 m L lenv y).  
                  intros. apply Hrel_mL. constructor. auto.
 
                  (* replacing bind_n_after_ptr to something easier to induct on *)
                  assert (Hll' := bind_n_after_ptr_exists  (length vs2) alloc_b (Int.unsigned alloc_ofs + 4 + 4 * Z.of_nat (length vs1)) L). 
                  destruct Hll' as [L' [H_ll' H_eql']].
                  eapply  repr_val_ptr_list_L_Z_sub_locProp with (L := L'); auto.
                  Focus 2.                  
                  intro. intro. intro. apply bind_n_after_ptr_def.
                  rewrite <- H_eql' in H6.
                  apply bind_n_after_ptr_def in H6.
                  inv H6. auto.
                  destruct H8. right. split. auto.
                  split. omega.
                  rewrite N2Z.inj_add.
                  replace (Z.of_N a) with (Z.of_nat (length ys)) by omega.
                  replace (length ys) with (length vs2). int_red. simpl in H8. simpl Z.of_N. omega.
                  apply Forall2_length' in Hvs7. auto.

                  (* current locprop, from L + 1 to L + 1 + length vs *)
                  assert (H_ll'':= bind_n_after_ptr_exists' (length vs1) alloc_b  (Int.unsigned alloc_ofs + 4) L).
                  destruct H_ll'' as [L'' H_ll''].

                  assert (H_not_in_L:
                            (forall j:Z,
                                (Int.unsigned alloc_ofs  <= j <
                                 Int.unsigned alloc_ofs + 4 + 4  * (Z.of_nat (length vs7)))%Z -> ~ L alloc_b j)).
                  {
                    inv Hrel_pL. destructAll. rewrite H6 in Hget_alloc. inv Hget_alloc.
                    intros.
                    apply H12.
                    simpl max_allocs. destruct ys. exfalso; auto.
                    rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add.
                      int_red. unfold Int.add.
                      rewrite Int.unsigned_repr with (z :=  (4 * Z.succ (Z.of_nat (max_allocs e) + Z.of_nat (@length var (v0::ys))))%Z).
                      rewrite Int.unsigned_repr.
                      apply Forall2_length' in Hvs7. replace (@length var (@cons var v0 ys)) with (@length val vs2).
                      simpl length in H10. simpl Z.of_nat in H10.
                      rewrite Z.mul_succ_r. omega.
                      (* TODO: this proof again...should be factored out and kept around *)
                      split. apply Z_non_neg_add. omega. apply Int.unsigned_range.
                      etransitivity. etransitivity. Focus 2. apply Hbound_limit. inv Hc_alloc. simpl max_allocs. simpl length.
                      do 2 rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add.
                      rewrite Nat2Z.inj_succ. reflexivity. apply Int.unsigned_range_2.
                      split. omega. 
                      etransitivity. etransitivity. Focus 2. apply Hbound_limit. inv Hc_alloc. simpl max_allocs. simpl length.
                      do 2 rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_add.
                      rewrite Nat2Z.inj_succ. assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
                      omega. apply Int.unsigned_range_2.                       
                  }                  
                  assert (H_u_mmid_m3: Mem.unchanged_on L'' m_mid m3). {                    
                    eapply mem_after_n_proj_store_unchanged. eauto. 
                    intros; intro.
                    eapply bind_n_after_ptr_from_rev in H_ll''. rewrite <- H_ll'' in H8.                    
                    rewrite bind_n_after_ptr_def in H8.
                    destruct H8.
                    - (* L alloc_b j is protected *)
                      revert H8. apply H_not_in_L. subst. simpl length in *. int_red. simpl Z.of_nat in *.  omega.
                      
                    - (* j is both in and after vs1 so impossible *)
                      int_red. omega.
                    }

                  clear H_eql'.
                  
                  rewrite get_var_or_funvar_list_correct in Hvs7. rewrite <- get_var_or_funvar_list_set in Hvs7.
                  rewrite <- get_var_or_funvar_list_set in Hvs7.
                  Focus 2. intro. eapply Hrho_id.
                  eapply getlist_In; eauto.
                  constructor.
                  Focus 2. intro.
                  inv Hp_id.
                  eapply getlist_In in H.
                  destruct H. 
                  eapply H8. apply H.
                  left. reflexivity.
                  left. reflexivity.
                  auto.
                  rewrite <- get_var_or_funvar_list_correct in Hvs7. 
                  
                  clear Hrel_mL.
                  clear Hev.  clear Hc_env. revert H. clear Hp_id. clear Hf_id. revert H5.  clear Hrel_m. clear Hc_alloc.
                  clear H2. 
                  clear H1.  clear H0.   clear Hstep_m2.  destruct Hstep_m3 as [Htemp Hm3]. clear Htemp.

                  

                   
                  clear Hm3.
                  revert H_m2_m3.
                  revert H_m2_mmid.
                  revert H_rev_vs7.

                  
(*                   clear H_m2_m3.
                  
                  assert (Hm3: mem_after_n_proj_store_rev alloc_b
                                                                (Int.unsigned alloc_ofs + 4 + 4 * (Z.of_N a - Z.of_nat (length ys))) vs7 m2 m3) by admit. (* need to modify the rest to use rev instead of cast *)

                  revert Hm3. *)    (*    revert  (* clear *) H_unchanged_m_m3. clear H_unchanged_m2_m3. revert m3. *)
                  revert H_ll'. revert L'.
                  revert H_ll''. revert H_u_mmid_m3. revert L''.
                  revert Hvs7.
                  clear Hrel_pL.
                  clear Hays.

                  clear Hrho_id.
                  clear Ha_l.
                  revert ys.


                  clear H_eq_vs7. clear H_eq_vs1. clear H_eq_m2.
                  revert m_mid.
                  revert vs1. revert vs2.
                  
                  induction vs. constructor.
                   intros.
                  apply getlist_cons in H. destruct H as [y [ys' [H_ys [Hyrho Hget_ys']]]].
                  subst.
                  inv Hvs7.

                  assert (H_repr_a0: repr_val_L_L6_L7_id fenv finfo_env p rep_env a0 m3 L'  (Val.load_result Mint32 y0)). {
                    assert (List.In y (y::ys')) by (constructor; auto). apply H5 in H. destructAll.
                    rewrite H in Hyrho. inv Hyrho.                    
                    inv H1; inv H0; rewrite H2 in H1; inv H1.
                    - (* fun *)
                      eapply repr_val_L_sub_locProp.
                      Focus 2. intro.  intros. eapply bind_n_after_ptr_from_rev in H_ll'. rewrite <- H_ll'.
                      apply bind_n_after_ptr_def. left. apply H0.
                      eapply repr_val_L_unchanged; eauto.
                    - (* constr *)
                      rewrite load_ptr_or_int.
                      rewrite H8 in H10. inv H10. 
                      eapply repr_val_L_sub_locProp.
                      Focus 2. intro.  intros. eapply bind_n_after_ptr_from_rev in H_ll'. rewrite <- H_ll'.
                      apply bind_n_after_ptr_def. left. apply H0.
                      eapply repr_val_L_unchanged; eauto.
                      auto.                      
                  }

                  
                   simpl length in H_ll'.
                   inv H_ll'.  


                   
                   inv H_m2_m3.
                  - (* vs2 = [a] last case *)
                    inv H6. inv Hget_ys'. econstructor.
                    + intros.
                      right. split; auto.
                    + int_red.
                      eapply Mem.load_store_same. auto. apply H13.                      
                    + auto.
                    + constructor.
                   - (* vs2 = a::vs2' IH *)
                     
                     assert (H_m2_m': mem_after_n_proj_snoc alloc_b (Int.unsigned alloc_ofs + 4) (y0::vs1) m2 m') by (econstructor; eauto).
                     assert (H_ll''_new:= bind_n_after_ptr_exists (length (y0::vs1)) alloc_b  (Int.unsigned alloc_ofs + 4) L).
                     destruct H_ll''_new as [L3 [H_ll3 H_ll3_def]].
                     assert (H_unchanged_L3: Mem.unchanged_on L3 m' m3).
                     {  eapply mem_after_n_proj_store_unchanged. apply H14.
                       intros. intro. rewrite <- H_ll3_def in H2.
                       rewrite bind_n_after_ptr_def in H2.
                       destruct H2.
                       * revert H2. apply H_not_in_L.
                         int_red.
                         rewrite app_length.
                         rewrite rev_length.
                         simpl length.
                         rewrite Nat2Z.inj_add.
                         rewrite Nat2Z.inj_succ. omega.                         
                       * destruct H2. simpl length in H8.
                         rewrite Nat2Z.inj_succ in H8. int_red. omega.
                     }
                     eapply IHvs in H_m2_m'; eauto.
                     + econstructor.
                       * intros. right. auto.
                       * int_red. 
                         eapply Mem.load_unchanged_on.
                         eauto.
                         intros. rewrite <- H_ll3_def.
                         rewrite bind_n_after_ptr_def. right. split; auto. simpl length.
                         rewrite Nat2Z.inj_succ. int_red. omega.
                         eapply Mem.load_store_same. apply H10. 
                       * (* this is from m3 unchanged m over L *)
                         auto.
                         
                       *  eapply repr_val_ptr_list_L_Z_sub_locProp; auto. 
                          replace (Int.unsigned alloc_ofs + 4 + 4 * Z.of_nat (length vs1) + int_size)%Z
                           with
                             (Int.unsigned alloc_ofs + 4 + 4 * Z.of_nat (length (y0 :: vs1)))%Z.
                         apply H_m2_m'. simpl length. rewrite Nat2Z.inj_succ.
                         rewrite Z.mul_succ_r. int_red. omega.
                         intro. intros. left. eauto. 
                     + simpl length. rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_r. int_red. rewrite Z.add_assoc. eauto.
                     + simpl. rewrite <- app_assoc. simpl. auto.
                     + simpl length. rewrite Nat2Z.inj_succ. auto.
                     + intros. apply H5. constructor 2. auto.
                     }                     
        (* 

 getlist ys rho = Some vs ->
Forall2
           (get_var_or_funvar p
              (Maps.PTree.set allocIdent
                 (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1))))))
                 (Maps.PTree.set x
                    (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))) lenv)))
           ys vs7
 rel_mem_L6_L7_id fenv finfo_env p rep_env (Econstr x t ys e) rho m lenv
 -> 
 mem_after_n_proj_store_cast alloc_b
               (Int.unsigned (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))) vs7 0 m2 m3
 ->
  repr_val_ptr_list_L_L6_L7 argsIdent allocIdent limitIdent gcIdent threadInfIdent tinfIdent isptrIdent caseIdent fenv finfo_env
    p rep_env vs m3 (bind_n_after_ptr (Z.of_N (a + 1)) alloc_b (Int.unsigned alloc_ofs) L) alloc_b
    (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one)))

*)                                
            + (* x0 <> x*)
              assert (occurs_free (Econstr x t ys e) x0).
              constructor 2; auto.
              specialize (Hrel_mL _ H5).
              destruct Hrel_mL as [v6 [Hx0_v6 Hrepr_v6]].
              exists v6. split.
              rewrite M.gso; auto.
              apply repr_val_id_set.
              apply repr_val_id_set.
              eapply repr_val_id_L_sub_locProp with (L := L).
              eapply repr_val_id_L_unchanged. apply Hrepr_v6. auto.
              intro. intros.
              rewrite bind_n_after_ptr_def. auto.
              auto.
              inv Hp_id.
              intro.
              eapply H6. apply Hx0_v6.
              left. reflexivity. auto.
        }        
        { (* correct_tinfo after adding the constructor *)


          assert (correct_tinfo allocIdent limitIdent argsIdent (Z.of_nat (max_allocs e))
                                (Maps.PTree.set x (Vptr alloc_b (Int.add alloc_ofs (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr Z.one))))
                                                lenv) m3).
          
          eapply correct_tinfo_not_protected.
          eapply correct_tinfo_mono.                    
          destruct Hstep_m3.          
          eapply correct_tinfo_after_nstore.
          Focus 2. eauto.
          
          eapply correct_tinfo_after_store; eauto.
          inv Hc_alloc.
          simpl max_allocs. destruct ys. omega.
          rewrite Nat2Z.inj_succ.
          rewrite Nat2Z.inj_add.
          omega.
          auto.
          (* alloc is moved to an OK location *)
          {

            
            
            destruct H4 as [alloc_b' [alloc_ofs' [limit_ofs' [args_b' [args_ofs' [Hget_alloc' [Hrange_alloc' [Hget_limit' [Hbound_limit' [Hget_args' [Hdj_args' [Hbound_args' Hrange_args']]]]]]]]]]]].
            assert (alloc_b' = alloc_b /\ alloc_ofs' = alloc_ofs').  rewrite M.gso in Hget_alloc'. rewrite Hget_alloc' in Hget_alloc. inv Hget_alloc. auto.            
            intro.  apply H3. subst. left. auto.
            destruct H4; subst. clear H5.
            assert (args_b' = args_b /\ args_ofs' = args_ofs').  rewrite M.gso in Hget_args'. rewrite Hget_args' in Hget_args. inv Hget_args. auto.            
            intro.  apply H3. subst. right. auto. 
            destruct H4; subst. clear H5.
            assert (limit_ofs = limit_ofs'). rewrite M.gso in Hget_limit'. rewrite Hget_limit' in Hget_limit. inv Hget_limit. auto.
            intro.  apply H3. subst. right. auto. 
            subst.
            do 5 eexists. split.
            rewrite M.gss. reflexivity.
            split.
            intros. inv Hc_alloc.
            assert ( (0 <= i + (Z.of_N (a + 1)) < Z.of_nat (max_allocs (Econstr x t ys e))))%Z.
            simpl max_allocs.   destruct ys. inv H2.
            rewrite Nat2Z.inj_succ. 
            rewrite Nat2Z.inj_add.
            destruct Ha_l. rewrite H5. simpl.  rewrite Pos2Z.inj_add.
            rewrite Z.add_1_r.
            rewrite Z.add_succ_r.
            split.
            apply Z.le_le_succ_r.
            apply Z_non_neg_add.
            apply Pos2Z.is_nonneg.
            apply H4.
            omega.
            apply Hrange_alloc in H5.
            rewrite Z.mul_add_distr_l in H5.
            rewrite Z.add_comm in H5.
            rewrite Int.add_assoc.
            replace (Int.add (Int.mul (Int.repr (sizeof (globalenv p) uintTy)) (Int.repr (Z.of_N (a + 1)))) (Int.repr (int_size * i)))  with (Int.repr (int_size * Z.of_N (a + 1) + int_size * i)).
            eapply valid_access_after_nstore.
            eapply Mem.store_valid_access_1.
            eauto. apply H5.
            destruct Hstep_m3; eauto.


            assert (Halloc_ofs := Int.unsigned_range_2 alloc_ofs).
            assert (Hlimit_ofs' := Int.unsigned_range_2 limit_ofs').
            simpl max_allocs in Hbound_limit.
            destruct ys. inv Ha_l. exfalso. apply H8; auto.
            destruct Ha_l.
            rewrite Nat2Z.inj_succ in Hbound_limit.
            rewrite Nat2Z.inj_add in Hbound_limit.
            rewrite <- nat_N_Z with (n := (length (v0 :: ys))) in Hbound_limit.
            rewrite <- H6 in Hbound_limit.
            rewrite N.add_1_r.
            rewrite N2Z.inj_succ.
            rewrite Zplus_succ_r_reverse in Hbound_limit.
            rewrite Z.mul_add_distr_l in Hbound_limit.            
            
            rewrite int_z_mul.

            rewrite int_z_add. reflexivity. 
            simpl sizeof. int_red.
            constructor.
            split.
            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range. omega.
            apply Int.unsigned_range_2.
            constructor. split. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg. omega.
            apply Int.unsigned_range_2.
            constructor.
            simpl sizeof. constructor. solve_uint_range. constructor.

            assert (0 <= Z.of_N a)%Z by apply N2Z.is_nonneg.
            split. omega.
            etransitivity. etransitivity. Focus 2. apply Hbound_limit.
            assert (0 <= Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            int_red.
            omega.
            apply Int.unsigned_range_2.
            constructor. 
            split. rewrite M.gso.
            subst.
            eauto. intro.
            assert (H_nodup := disjointIdent).
            inv H_nodup. inversion H9.
            apply H10. constructor. constructor.
            split. 
            etransitivity. Focus 2. apply Hbound_limit.
            inv Hc_alloc.
            simpl max_allocs. 
            destruct ys. inv H2.
            simpl sizeof. int_red.
            destruct Ha_l. rewrite H4.
            rewrite N2Z.inj_add.
            rewrite nat_N_Z.
            simpl Z.of_N.
            rewrite int_z_mul.
            unfold Int.add.
            rewrite Int.unsigned_repr with (z := (4 * (Z.of_nat (length (v0 :: ys)) + 1))%Z).
            rewrite Int.unsigned_repr. 

            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.
            omega.
            split. apply Z_non_neg_add.
            omega.
            apply Int.unsigned_range.
            etransitivity. etransitivity. Focus 2.
            apply Hbound_limit. simpl max_allocs. simpl length. 
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.                                                
            rewrite Nat2Z.inj_succ.
            omega.
            apply Int.unsigned_range_2.
            split. omega.
            etransitivity. etransitivity. Focus 2.
            apply Hbound_limit. simpl max_allocs. simpl length. 
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.                                                
            rewrite Nat2Z.inj_succ.
            assert (0 <=  Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            omega.
            apply Int.unsigned_range_2.
            constructor. solve_uint_range.
            constructor.
            split. omega.
            etransitivity. etransitivity. Focus 2.
            apply Hbound_limit. simpl max_allocs. simpl length. 
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_succ.
            rewrite Nat2Z.inj_add.                                                
            rewrite Nat2Z.inj_succ.            
            assert (0 <=  Int.unsigned alloc_ofs)%Z by apply Int.unsigned_range.
            omega.
            apply Int.unsigned_range_2.
            constructor.
            split. rewrite M.gso. eauto.
            intro.
            assert (H_nodup := disjointIdent). subst. 
            inversion H_nodup. apply H8. constructor. auto.
            split. auto. auto.
        }} 

      - (* unboxed *)
        eexists. eexists. split.
        constructor. constructor. constructor.
        split.
        + (* mem *)
          destruct Hrel_m as [L  [Hnot_in_L Hrepr_m]].
          exists L. split.
          eapply protected_not_in_L_set; eauto.
          intros.
          destruct (var_dec x0 x).
          * subst.
            exists (Vconstr t vs). split.
            rewrite M.gss. reflexivity.
            econstructor 2.
            apply Hf_id. constructor.
            rewrite M.gss. reflexivity.
            simpl in H. inv H.
            econstructor; eauto.
            eapply Int.eqm_trans.
            apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
            auto.
          * assert (occurs_free (Econstr x t [] e) x0).
            constructor 2; auto.
            specialize (Hrepr_m _ H3).
            destruct Hrepr_m as [v6 [Hx0v6 Hrepr_v6]].
            exists v6.
            split.
            rewrite M.gso; auto.
            apply repr_val_id_set; auto.
        + (* tinfo *)
          apply correct_tinfo_not_protected.
          eapply correct_tinfo_mono; eauto.
          inv Hc_alloc. simpl. omega.
          intro.
          inv Hp_id.
          eapply H4; eauto.
    }   
    destruct H0 as [lenv' [m' [Hstep [Hrel_m' Htinfo_e]]]].
    
    (* set up the with the recursive call *)
    assert (Hc_env_e: correct_envs cenv ienv rep_env e). {
      eapply correct_envs_subterm; eauto. constructor. constructor.
    }
    assert (Hp_id_e: protected_id_not_bound_id (cps.M.set x (Vconstr t vs) rho) e).
    { split; intros.
      - inv Hp_id.
        destruct (var_dec x0 x).
        + subst. intro. inv H4; subst.
          eapply H3; eauto.                    
          rewrite M.gss in H0. inv H0.
          inv H5.
          assert (Hgi_v := getlist_In_val _ _ _ _ H H10).
          destructAll.           
          eapply H2; eauto. 
        + rewrite M.gso in H0 by auto. eapply H2; auto. 
      - inv Hp_id.
        intro. eapply H2; eauto.
    }
    assert (Hf_id_e:  functions_not_bound p e). eapply functions_not_bound_subterm; eauto. constructor. constructor.
    assert (H_rho_e:  unique_bindings_env (cps.M.set x (Vconstr t vs) rho) e ).
    { destruct Hrho_id as [Hub Hrho_id].
      split.
      inv Hub; auto.
      intro. intros. destruct H0.
      destruct (var_dec x0 x).
      - subst. (* need unique binding *)
        inv Hub. auto.
      -  rewrite M.gso in H0 by auto.
         intro.
         eapply Hrho_id. exists x1. eauto. constructor 2. auto.
    }
    specialize (IHHev Hc_env_e Hp_id_e H_rho_e Hf_id_e).
    assert (Hca_e : correct_alloc e (Z.of_nat (max_allocs e))).
    unfold correct_alloc. reflexivity.
    specialize (IHHev _ _ _ k _ fu H7 Hrel_m' Hca_e Htinfo_e).
    destruct IHHev as [m'' [lenv'' [Hstep' Hargs]]].
    exists m'', lenv''.
    split; auto.
    eapply t_trans. eapply t_trans.
    constructor. constructor. apply Hstep.
    eapply t_trans. constructor. constructor.
    auto.        
  - (* Eproj *)
     
    (* > representation in memory of the Vconstr *)
    assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
    destruct (Hrel_m) as [L [HL_pro Hmem]].
    apply Hmem in Hy. destruct Hy as [v6 [Hyv6 Hrepr_v6]].    
    rewrite Hyv6 in H. inv H.     
    inversion Hrepr_v6; subst.
    
    rename H1 into Hyv7.
    inv H2.
    (* impossible that v7 is an enum, if taking proj, then vs is not empty so c is boxed *) 
    { exfalso.  
      inv H0.
    }
    (* get the value on the nth of vs in memory *)
    
    assert (Hvn := repr_val_ptr_list_L_nth argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent  threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent  cenv _ _ _ _ H12  H0).
 
    (* done setting up, taking the proj step *)
    destruct Hvn as [v7' [Hv7'_l Hv7'_rep]]. 
    assert (m_tstep2 (globalenv p)
      (State fu
         (Ssequence
            (Sset x
               (Ederef
                  (add
                     (Ecast (Etempvar y uintTy)
                        (Tpointer uintTy
                           {|
                           attr_volatile := false;
                           attr_alignas := None |}))
                     (c_int' (Z.of_N n) intTy)) uintTy)) s) k empty_env
         lenv m)
      (State fu s k empty_env (Maps.PTree.set x v7' lenv) m)).
    {
      eapply t_trans.
      constructor. constructor.
      eapply t_trans.
      constructor. constructor. eapply eval_Elvalue. apply eval_Ederef.
      econstructor. econstructor. constructor.
      eauto. reflexivity. constructor.
      simpl. unfold sem_add. simpl. reflexivity.
      eapply deref_loc_value. constructor. simpl.
      rewrite Int.mul_commut. apply Hv7'_l.
      constructor. constructor.
    }

    simpl in Hc_alloc.
    assert (Hc_env_e: correct_envs cenv ienv rep_env e). {
      eapply correct_envs_subterm; eauto. constructor. constructor.
    }
    specialize (IHHev Hc_env_e).
    assert (Hp_id_e: protected_id_not_bound_id (cps.M.set x v rho) e).
    { split; intros.
      - inv Hp_id.
        destruct (var_dec x0 x).
        + subst. intro. inv H11; subst.
          eapply H10. apply H3. constructor.
          rewrite M.gss in H2. inv H2.
          eapply H9. apply Hyv6. apply H3.
          right. econstructor.
          apply H13. eapply nthN_In; eauto.
        + rewrite M.gso in H2 by auto. eapply H9. apply H2. auto.
      - inv Hp_id.
        intro. eapply H9. apply H2.
        constructor; auto.
    }
    specialize (IHHev Hp_id_e).
    assert (Hf_id_e: functions_not_bound p e). eapply functions_not_bound_subterm; eauto. constructor. constructor.
    assert (Hrho_id_e: unique_bindings_env (cps.M.set x v rho) e). {
      destruct Hrho_id as [Hub Hrho_id].
      split.
      inv Hub; auto.
      intros. destruct H2. destruct (var_dec x0 x).
      - subst. inv Hub; auto.
      - rewrite M.gso in H2 by auto. intro.
        eapply Hrho_id. exists x1. apply H2. constructor; auto.
    }
    specialize (IHHev Hrho_id_e Hf_id_e _ (Maps.PTree.set x v7' lenv) m k max_alloc fu H7).    
    assert (Hx_not:  ~ is_protected_id argsIdent allocIdent limitIdent x). {
      intro. inv Hp_id. eapply H9; eauto.    
    }
    assert (rel_mem_L6_L7_id fenv finfo_env p rep_env e (cps.M.set x v rho) m (Maps.PTree.set x v7' lenv)).
    { exists L.
      
      split.
      -   apply protected_not_in_L_set; auto.
      - intros.
        destruct (var_dec x0 x).
        + subst. exists v. split.
          rewrite M.gss; auto.
          econstructor 2. 
          (* x is bound in Eproj x t n y e so cannot be a function name  *)
          apply Hf_id. constructor.
          rewrite M.gss. reflexivity.
          apply Hv7'_rep.
        + rewrite M.gso by auto.
          assert ( occurs_free (Eproj x t n y e) x0). constructor; auto.
          specialize (Hmem _ H3). destructAll.
          exists x1; split; auto.
          inv H10.
          * econstructor; eauto.
          * econstructor 2; eauto.
            rewrite M.gso; auto.
    } 
    assert ( correct_alloc e max_alloc). inv Hc_alloc.
    simpl. constructor.
    assert ( correct_tinfo allocIdent limitIdent argsIdent max_alloc
            (Maps.PTree.set x v7' lenv) m ).
    apply correct_tinfo_not_protected; auto.
    specialize (IHHev H2 H3 H9).
    destruct IHHev as [m' [lenv' [Hstep Hargs]]].
    exists m', lenv'.
    split; auto.
    eapply t_trans; eauto.    
  - (* Ecase *)    

    (* get the representation of y *)
    assert (Hrel_m' := Hrel_m).
    destruct Hrel_m' as [L [Hmem_p Hmem_rel]].
    assert (occurs_free (Ecase y cl) y) by constructor.
    apply Hmem_rel in H2. destruct H2 as [y6 [Hy6 Hrepr_id_y6]].
    rewrite Hy6 in H. inv H.

    assert (Htcenv := caseConsistent_findtag_In_cenv _ _ _ _ H0 H1).
    destruct Htcenv as [a [ty [n [i Htcenv]]]].
    (** Hrepr_id_y6 must be RVid_V *)
    inv Hrepr_id_y6.
    rename H into Hglob_y. rename H2 into Hlenv_y. rename H3 into Hrepr_y.


    (* step through the assignment and the isptr check *)
    inv H6.
    
    
    
    (* break into boxed and unboxed cases *)
    inv Hrepr_y.
    + (* y is unboxed *)
      admit.

    + (* y is boxed *)
      admit.

  - (* Eapp *)
    
    admit.
  - (* Ehalt *)

    (* find out what v looks like in memory *)
    assert (Hof: occurs_free (Ehalt x) x) by constructor.
    destruct (Hrel_m) as [L [HL_pro Hmem]].
    apply Hmem in Hof. destruct Hof as [v6 [Hxrho Hrel_v6]].
    clear Hmem.

    (* show that we have write access to args[1] *)
    unfold correct_tinfo in Hc_tinfo.
    destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [Hget_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args Hrange_args]]]]]]]]]]]].
    assert (Htemp : (0 <= 1 < max_args)%Z) by (unfold max_args; omega).

    assert (Hvalid_args1:= Hrange_args _ Htemp).
    clear Htemp.

    inv Hrel_v6.
     
    + (* halt on a function *)
      inv H1. rewrite H0 in H3. inv H3. 
      
      assert (Hvv  :=  Mem.valid_access_store _ _ _ _ (Vptr b0 Int.zero) Hvalid_args1).
      destruct Hvv as [m2 Hm2].
      
      assert (Hm2_u : Mem.unchanged_on L m m2). {
        inv HL_pro.
        destructAll.
        eapply Mem.store_unchanged_on; eauto; intros.
        rewrite Hget_args in H5; inv H5.
        apply H6 with (z := 1%Z).
        unfold max_args; omega.
        rewrite Int.mul_one in *.
        simpl. unfold int_size in *; eauto.
      }
      exists m2, lenv.
      
      split.
      
      * apply t_step. eapply step_assign with (v := (Vptr b0 Int.zero)) (m' := m2).  
        { 
          constructor.
          econstructor. constructor; eauto.
          constructor. simpl. unfold sem_add. simpl. reflexivity.      
        }
        econstructor. constructor 2.
              apply M.gempty. eauto. constructor.
      constructor. constructor.
      econstructor. simpl. reflexivity. apply Hm2.
      * unfold arg_val_L6_L7. exists args_b, args_ofs, (Vptr b0 Int.zero), L.
        split; auto. rewrite Int.mul_one in Hm2. split.
        eapply Mem.load_store_same in Hm2.
        simpl in Hm2. auto.
        rewrite Hxrho in H; inv H.
        eapply repr_val_L_unchanged; eauto.
      * rewrite H0 in H3; inv H3.                        
    + (* halt on constr or int *)
      inv H1. rewrite H4 in H0; inv H0.
      clear H4.
      assert (Hvv  :=  Mem.valid_access_store _ _ _ _ v7 Hvalid_args1).
      destruct Hvv as [m2 Hm2].      
      assert (Hm2_u : Mem.unchanged_on L m m2). {
        inv HL_pro.
        destructAll.
        eapply Mem.store_unchanged_on; eauto; intros.
        rewrite Hget_args in H6; inv H6.
        apply H7 with (z := 1%Z).
        unfold max_args; omega.
        rewrite Int.mul_one in *.
        simpl. unfold int_size in *; eauto.
      }
      exists m2, lenv.
      split.
      * apply t_step. eapply step_assign with (v := v7) (m' := m2).  
        { 
          constructor.
          econstructor. constructor; eauto.
          constructor. simpl. unfold sem_add. simpl. reflexivity.      
        }
        econstructor. eauto.  simpl. 
        unfold sem_cast. simpl. inv H3; reflexivity.
        econstructor. constructor.
        simpl. apply Hm2.
      * unfold arg_val_L6_L7. exists args_b, args_ofs, v7, L.
        split; auto. split.
        rewrite Int.mul_one in Hm2.
        eapply Mem.load_store_same in Hm2. simpl in Hm2. destruct v7; inv H3; auto.
        rewrite H in Hxrho. inv Hxrho.
        eapply repr_val_L_unchanged; eauto.
Admitted.



(* Top level theorem on the L6_to_Clight translation 
Theorem top_repr_L6_L7_are_related: *)
  