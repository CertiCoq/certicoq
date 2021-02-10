(* Conversion from L4.expression to L6.cps using ANF or CPS tranformation *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String
        Coq.Sorting.Sorted Coq.Arith.Arith Coq.Sets.Ensembles.
Require Import ExtLib.Data.String.
Require Import Common.AstCommon Common.compM.

Require Import L4.expression.
Require Import L6.cps L6.cps_show L6.eval L6.ctx L6.List_util L6.Ensembles_util L6.state. 
Require Import compcert.lib.Coqlib compcert.lib.Maps.

Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import ListNotations.
Import Monad.MonadNotation.
Open Scope monad_scope.


Section Translate.

  Context (prim_map : M.t (kername * string (* C definition *) * nat (* arity *))). 
  Context (func_tag kon_tag default_tag default_itag : positive)
          (next_id : positive).

  
  Section COMMON.
    
    Definition conId_map:= list (dcon * ctor_tag).
    
    Theorem conId_dec: forall x y:dcon, {x = y} + {x <> y}.
    Proof.
      intros. destruct x,y.
      assert (H:= AstCommon.inductive_dec i i0).
      destruct H.
      - destruct (classes.eq_dec n n0).
        + subst. left. auto.
        + right. intro. apply n1. inversion H. auto.
      - right; intro; apply n1. inversion H; auto.
    Defined.

    Fixpoint dcon_to_info (a:dcon) (sig:conId_map) :=
      match sig with
      | nil => default_tag
      | ((cId, inf)::sig') => match conId_dec a cId with
                              | left _ => inf
                              | right _ => dcon_to_info a sig'
                              end
      end.

    Definition dcon_to_tag (a:dcon) (sig:conId_map) :=
      dcon_to_info a sig.

    Definition name_env := M.t BasicAst.name.
    Definition n_empty : name_env := M.empty _.
    
    Definition constr_env:Type := conId_map.
    
    Definition ienv := list (BasicAst.kername * AstCommon.itypPack).
    
    
    (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
    Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
      match m with
      | O => (nil, n)
      | S m' =>
        let (l, nm ) := (fromN (n+1) (m')) in
        (n::l, nm)
      end.
    
    (* Bind m projections. The first variable in the list binds the last constructor argument. *)
    Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (vars : list var) (args:nat) (* initially the length of args list *)
      : exp_ctx :=
      match vars with
      | [] => Hole_c
      | v :: vars =>
        let ctx_p':= ctx_bind_proj tg r vars (args - 1) in
        (Eproj_c v tg (N.of_nat (args - 1)) r ctx_p')
      end.
    
    
    (** process a list of constructors from inductive type ind with ind_tag niT.
    - update the ctor_env with a mapping from the current ctor_tag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of
      ind to the ctor_tag of the current constructor *)
    Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr)
             (ind:BasicAst.inductive) (nCon:N) (unboxed : N) (boxed : N)
             (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
      match (cct, itC) with
      | (cn::cct', cst::icT') =>
        let (cname, ccn) := cst in
        let is_unboxed := Nat.eqb ccn 0 in
        let info := {| ctor_name := BasicAst.nNamed cname
                       ; ctor_ind_name := BasicAst.nNamed tyname
                       ; ctor_ind_tag := niT
                       ; ctor_arity := N.of_nat ccn
                       ; ctor_ordinal := if is_unboxed then unboxed else boxed
                    |} in
        convert_cnstrs tyname cct' icT' ind (nCon+1)%N
                       (if is_unboxed then unboxed + 1 else unboxed)
                       (if is_unboxed then boxed else boxed + 1)
                       niT
                       (M.set cn info ce)
                       (((ind,nCon), cn)::dcm (** Remove this now that params are always 0? *))
      | (_, _) => (ce, dcm)
      end.
    

    (** For each inductive type defined in the mutually recursive bundle,
    - use tag niT for this inductive datatype
    - reserve constructor tags for each constructors of the type
    - process each of the constructor, indicating they are the ith constructor
      of the nth type of idBundle
    np: number of type parameters for this bundle
     *)
    Fixpoint convert_typack typ (idBundle:BasicAst.kername) (n:nat)
             (ice : (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map))
      : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
      let '(ie, ce, ncT, niT, dcm) := ice in
      match typ with
      | nil => ice
      (* let cct := (ncT::nil) in
      let ncT' := Pos.succ ncT in
      let itN := "Unit"%string in
      let itC := ((mkCnstr "prf"%string 0%nat) :: nil) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 niT ce dcm
      in
      let ityi := ((ncT, N.of_nat 0%nat)::nil) in
      (M.set niT ityi ie, ce', ncT', (Pos.succ niT), dcm') *)
      | (AstCommon.mkItyp itN itC ) ::typ' =>
        let (cct, ncT') := fromN ncT (List.length itC) in
        let (ce', dcm') :=
            convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 0 0 niT ce dcm
        in
        let ityi :=
            combine cct (map (fun (c:AstCommon.Cnstr) =>
                                let (_, n) := c in N.of_nat n) itC)
        in
        convert_typack typ' idBundle (n+1)
                       (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
      end.


    Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map)
      : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
      let '(ie, ce, ncT, niT, dcm) := ice in
      match g with
      | nil => ice
      | (id, ty)::g' =>
        (* id is name of mutual pack ty is mutual pack *)
        (* constructors are indexed with : name (string) of the mutual pack
       with which projection of the ty, and indice of the constructor *)
        convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
      end.    

    (** As we process the L4 inductive environment (ienv), we build:
    - an L6 inductive environment (ind_env) mapping tags (ind_tag) to constructors

      and their arities
      - an L6 constructor environment (ctor_env) mapping tags (ctor_tag) to
      information about the constructors
      - a map (conId_map) from L4 tags (conId) to L6 constructor tags (ctor_tag)
      convert_env' is called with the next available constructor tag and the
      next available inductive datatype tag, and inductive and constructor
      environment containing only the default "box" constructor/type
     *)
    Definition convert_env (g:ienv): (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map) :=
      let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
      let info := {| ctor_name := BasicAst.nAnon
                     ; ctor_ind_name := BasicAst.nAnon
                     ; ctor_ind_tag := default_itag
                     ; ctor_arity := 0%N
                     ; ctor_ordinal := 0%N
                  |} in
      let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
      convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).

  End COMMON.


  (* Zoe: For erasing boxes translating proof. TODO *)
  Definition consume_fun (f x : var) : exp_ctx :=
    Efun1_c (Fcons f func_tag [x] (Ehalt f) Fnil) Hole_c. 



  Section CPS.

    Definition cpsM := @compM' unit.

    (* TODO move *)
    Definition get_named_str_lst (s : list string) : cpsM (list var) :=
      mapM get_named_str s.

    Fixpoint convert_prim (n : nat) (* arity *)
             (prim : positive) (args : list var) (kont : var) : cpsM cps.exp :=
      match n with
      | 0%nat =>
        pr <- get_named_str "prim"%string ;;
        ret (Eprim pr prim (List.rev args) (Eapp kont kon_tag [pr]))
      | S n =>
        arg <- get_named_str "p_arg"%string ;;
        kont1 <- get_named_str "p_k"%string ;;
        f <- get_named_str "prim_wrapper"%string ;;
        trm <- convert_prim n prim (arg :: args) kont1 ;;
        ret (Efun (Fcons f func_tag [kont1; arg] trm Fnil) (Eapp kont kon_tag [f]))
      end.                  


    
    Fixpoint names_lst_len (ns : list name) (m : nat) : list name :=
      match ns, m with
      | _, 0%nat => []
      | [], S _ => repeat nAnon m
      | n :: ns, S m => n :: names_lst_len ns m
      end.

    Lemma names_lst_length ns m :
      List.length (names_lst_len ns m) = m.
    Proof.
      revert m; induction ns; intros m; destruct m; simpl; try reflexivity.
      - rewrite repeat_length. reflexivity.
      - rewrite IHns. reflexivity.
    Qed.
    

    (** ** Main CPS conversion program *)
  
    Fixpoint cps_cvt (e : expression.exp) (vn : list var) (k : var) (tgm : constr_env) : cpsM cps.exp :=
      match e with
      | Var_e x =>
        match nth_error vn (N.to_nat x) with
        | Some v => ret (cps.Eapp k kon_tag (v::nil))
        | None => failwith  "Unknown DeBruijn index"
        end
      | App_e e1 e2 =>
        x1 <- get_named_str "x1"%string ;;
        k1 <- get_named_str "k1"%string ;;
        x2 <- get_named_str "x2"%string ;;
        k2 <- get_named_str "k2"%string ;;
        e1' <- cps_cvt e1 vn k1 tgm;;
        e2' <- cps_cvt e2 vn k2 tgm;;
        ret (Efun
               (Fcons k1 kon_tag (x1::nil)
                      (cps.Efun
                         (Fcons k2 kon_tag (x2::nil)
                                (cps.Eapp x1 func_tag (k::x2::nil)) Fnil)
                         e2') Fnil)
               e1')
      | Lam_e n e1 =>
        x1 <- get_named_str "x1"%string ;;
        f <- get_named n ;;
        k1 <- get_named_str "k1"%string ;;
        e1' <- cps_cvt e1 (x1::vn) k1 tgm ;;
        ret (Efun
               (Fcons f func_tag (k1::x1::nil) e1' Fnil)
               (cps.Eapp k kon_tag (f::nil)))

      | Let_e n e1 e2 =>
        x <- get_named_str (string_of_name n);;
        k1 <- get_named_str "k"%string ;;
        e2' <- cps_cvt e2 (x::vn) k tgm ;;
        e1' <- cps_cvt e1 vn k1 tgm ;;
        ret (Efun
               (Fcons k1 kon_tag (x::nil) e2' Fnil)
               e1')

      | Con_e dci es =>
        let c_tag := dcon_to_tag dci tgm in
        x' <- get_named_str "x'"%string ;;
        xs <- get_named_str_lst (map (fun _ => "x") (exps_as_list es)) ;;
        ks <- get_named_str_lst (map (fun _ => "k") (exps_as_list es)) ;;
        cps_cvt_exps es vn (Econstr x' c_tag xs (Eapp k kon_tag (x'::nil))) xs ks tgm

      | Fix_e fnlst i =>
        let names_lst :=  fnames fnlst in
        nlst <- get_named_lst names_lst ;;
        fdefs <- cps_cvt_efnlst fnlst (List.rev nlst ++ vn) nlst tgm;;
        match nth_error nlst (N.to_nat i) with
        | Some i' => 
          ret (Efun fdefs (Eapp k kon_tag (i'::nil)))
        | None => failwith "Unknown function index"
        end
          
      | Match_e e1 n bl =>
        x1 <- get_named_str "x1"%string ;;
        k1 <- get_named_str "k1"%string ;;
        e1' <- cps_cvt e1 vn k1 tgm;;
        cbl <- cps_cvt_branches bl vn k x1 tgm;;
        ret (Efun (Fcons k1 kon_tag (x1::nil) (Ecase x1 cbl) Fnil) e1')
            
      | Prf_e =>
        x <- get_named_str "x"%string ;;
        ret (Econstr x default_tag nil (Eapp k kon_tag (x::nil)))
            
      (* f <- get_named_str "f"%string ;; *)
      (* x <- get_named_str "x"%string ;; *)
      (* let c := consume_fun f x in *)
      (* ret (c |[ cps.Eapp k kon_tag (f::nil) ]|) *)
            
      | Prim_e p =>
        match M.get p prim_map with
        | Some (nm, s, ar) => convert_prim ar p [] k
        | None => failwith "Internal error: identifier for primitive not found"
        end
      end

    with cps_cvt_exps (es : expression.exps) (vn : list var) (e_app : exp) (xs ks : list var) (tgm : constr_env)
         : cpsM cps.exp :=
           match es with
           | enil => ret e_app
           | econs e es' =>
             match xs, ks with
             | [], _ | _, [] => failwith "Internal error: wrong number of arguments in constructor continuation"
             | x1 :: xs, k1 :: ks =>
               e' <- cps_cvt e vn k1 tgm;;
               e_exp <- cps_cvt_exps es' vn e_app xs ks tgm;;
               ret (Efun (Fcons k1 kon_tag (x1::nil) e_exp Fnil) e')
             end
           end
    (* nlst must be of the same length as fdefs *)
    with cps_cvt_efnlst (fdefs : expression.efnlst) (vn : list var)
                        (nlst : list var) (tgm : constr_env)
         : cpsM fundefs :=
           match fdefs with
           | eflnil => ret Fnil
           | eflcons n1 e1 fdefs' =>
             x <- get_named_str "x"%string ;;
             k' <- get_named_str "k"%string ;;
             let curr_var := List.hd 1%positive nlst in
             match e1 with
             | Lam_e n2 e2 =>
               ce <- cps_cvt e2 (x::vn) k' tgm;;
               cfdefs <- cps_cvt_efnlst fdefs' vn (List.tl nlst) tgm;;
               ret (Fcons curr_var func_tag (k'::x::nil) ce cfdefs)
             | _ => failwith "body of fix must be a lambda expr"
             end
           end

    with cps_cvt_branches (bl : expression.branches_e) (vn : list var) (k : var)
                          (r : var) (tgm : constr_env)
         : cpsM (list (ctor_tag * exp)) :=
           match bl with
           | brnil_e => ret nil
           | brcons_e dc (i, lnames) e bl' =>
             (* Zoe: Did some refactoring to remove list rev and make the proof easier. Double check it's still OK.
              Now the first variable in vars binds the last constructor argument.
              *)
             let tg := dcon_to_tag dc tgm in
             cbl <- cps_cvt_branches bl' vn k r tgm;;
             vars <- get_named_lst (names_lst_len lnames (N.to_nat i)) ;;
             let ctx_p := ctx_bind_proj tg r vars (List.length vars) in
             ce <- cps_cvt e (vars ++ vn) k tgm ;; 
             ret ((tg, app_ctx_f ctx_p ce)::cbl)
           end.


    Definition convert_whole_exp (e : expression.exp ) (dcm : conId_map) : cpsM exp := 
      k <- get_named_str "k"%string ;;
      f <- get_named_str "f"%string ;;
      x <- get_named_str "x"%string ;;    
      e' <- cps_cvt e nil k dcm ;;
      ret (Efun
             (Fcons f kon_tag (k::nil) e'
                    (Fcons k kon_tag (x::nil) (Ehalt x) Fnil))
             (cps.Eapp f kon_tag (k::nil))). 
    

    Definition convert_top (ee:ienv * expression.exp) : error cps.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env (fst ee) in

      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil))
                                  (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in

      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_whole_exp (snd ee) dcm) comp_d tt in
      (res_err, comp_d').

    
    
    (** ** Declarative definition of CPS conversion used in proofs **)
    
  
  Inductive cps_cvt_rel : Ensemble var -> (* Input fresh identifiers *)
                          expression.exp -> (* Input L4 exp *)
                          list var -> (* deBruijn index map *)
                          var -> (* Continuation variable *)
                          constr_env ->
                          Ensemble var -> (* Output fresh identifiers *)
                          cps.exp -> (* CPS converted exp *)
                          Prop :=
  | e_Var :
      forall S v vn x k tgm,
        nth_error vn (N.to_nat x) = Some v -> 
        cps_cvt_rel S (Var_e x) vn k tgm S (cps.Eapp k kon_tag (v::nil))
  | e_Lam :
      forall S S' na e1 e1' x1 vn k k1 f tgm,
        x1 \in S ->
        f \in (S \\ [set x1]) ->
        k1 \in (S \\ (f |: [set x1])) ->
        cps_cvt_rel (S \\ [set x1] \\ [set f] \\ [set k1]) e1 (x1::vn) k1 tgm S' e1' ->
        cps_cvt_rel S
                    (Lam_e na e1)
                    vn
                    k
                    tgm
                    S'
                    (cps.Efun (Fcons f func_tag (k1::x1::nil) e1' Fnil)
                              (cps.Eapp k kon_tag (f::nil)))
  | e_App :
      forall S1 S2 S3 e1 e1' e2 e2' k k1 k2 x1 x2 vn tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        x2 \in (S1 \\ [set x1] \\ [set k1]) ->
        k2 \in (S1 \\ [set x1] \\ [set k1] \\ [set x2]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1] \\ [set x2] \\ [set k2]) e1 vn k1 tgm S2 e1' ->
        cps_cvt_rel S2 e2 vn k2 tgm S3 e2' ->
        cps_cvt_rel S1
                    (App_e e1 e2)
                    vn
                    k
                    tgm
                    S3
                    (cps.Efun (Fcons k1 kon_tag (x1::nil)
                                     (cps.Efun (Fcons k2 kon_tag (x2::nil)
                                                      (cps.Eapp x1 func_tag
                                                                (k::x2::nil))
                                                      Fnil)
                                               e2') Fnil)
                              e1')
  | e_Con :
      forall S1 S2 c_tag dci tgm es e' k x1 k1 vn vx xs ks,
        c_tag = dcon_to_tag dci tgm ->

        x1 \in S1 ->
        FromList xs \subset (S1 \\ [set x1] \\ [set k1] \\ FromList vx) ->
        FromList ks \subset (S1 \\ [set x1] \\ [set k1] \\ FromList vx \\ FromList xs) ->
               
        Datatypes.length vx = N.to_nat (exps_length es) ->
        NoDup vx ->
        NoDup xs ->
        NoDup ks -> 
        cps_cvt_rel_exps (S1 \\ [set x1] \\ [set k1] \\ FromList vx \\ FromList xs \\ FromList ks) 
                         es vn (Econstr x1 c_tag xs (Eapp k kon_tag [x1])) xs ks tgm S2 e' ->
        cps_cvt_rel S1
                    (Con_e dci es)
                    vn
                    k
                    tgm
                    S2
                    e'
  | e_Let :
      forall S1 S2 S3 na e1 e1' e2 e2' x1 vn k k1 tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e2 (x1::vn) k tgm S2 e2' ->
        cps_cvt_rel S2 e1 vn k1 tgm S3 e1' ->
        cps_cvt_rel S1
                    (Let_e na e1 e2)
                    vn
                    k
                    tgm
                    S3
                    (cps.Efun (Fcons k1 kon_tag (x1::nil) e2' Fnil) e1')
  | e_Match :
      forall S1 S2 S3 e1 e1' bs bs' vn k x1 k1 n tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e1 vn k1 tgm S2 e1' ->
        cps_cvt_rel_branches S2 bs vn k x1 tgm S3 bs' ->
        cps_cvt_rel S1
                    (Match_e e1 n bs)
                    vn
                    k
                    tgm
                    S3
                    (Efun (Fcons k1 kon_tag [x1] (Ecase x1 bs') Fnil) e1')
  | e_Fix :
      forall S1 S2 i f fnlst fnames vn k fdefs tgm,
        FromList fnames \subset S1 ->
        NoDup fnames ->
        List.length fnames = efnlength fnlst ->
        cps_cvt_rel_efnlst (S1 \\ (FromList fnames)) fnlst (List.rev fnames ++ vn) fnames tgm S2 fdefs ->
        nth_error fnames (N.to_nat i) = Some f ->
        cps_cvt_rel S1
                    (Fix_e fnlst i)
                    vn
                    k
                    tgm
                    S2
                    (cps.Efun fdefs (cps.Eapp k kon_tag (f::nil)))
  | e_Prf :
      forall S vn k tgm x,
        x \in S ->
        cps_cvt_rel S Prf_e vn k tgm (S \\ [set x]) (Econstr x default_tag nil (Eapp k kon_tag (x::nil)))
                    
  with cps_cvt_rel_exps :
         Ensemble var -> expression.exps -> list var -> exp -> list var -> list var ->
         constr_env -> Ensemble var -> exp -> Prop :=
  | e_Enil :
      forall S vn e_app  tgm,
        cps_cvt_rel_exps S enil vn e_app [] [] tgm S e_app
  | e_Econs :
      forall S1 S2 S3 vn e_app x1 xs k1 ks e es e' es' tgm,
        cps_cvt_rel S1 e vn k1 tgm S2 e' ->
        cps_cvt_rel_exps S2 es vn e_app xs ks tgm S3 es' ->
        cps_cvt_rel_exps S1
                         (econs e es)
                         vn
                         e_app
                         (x1 :: xs)
                         (k1 :: ks)
                         tgm
                         S3
                         (Efun (Fcons k1 kon_tag [x1] es' Fnil) e')
                         
  with cps_cvt_rel_efnlst :
         Ensemble var ->
         expression.efnlst ->
         list var ->
         list var ->
         constr_env ->
         Ensemble var ->
         fundefs ->
         Prop :=
  | e_Eflnil :
      forall S vn tgm,
        cps_cvt_rel_efnlst S eflnil vn [] tgm S Fnil
  | e_Eflcons :
      forall S1 S2 S3 vn fnames e1 e1' fnlst fdefs n n1 na x1 k1 tgm,
        x1 \in S1 ->
        k1 \in (S1 \\ [set x1]) ->
        cps_cvt_rel (S1 \\ [set x1] \\ [set k1]) e1 (x1::vn) k1 tgm S2 e1' ->
        cps_cvt_rel_efnlst S2 fnlst vn fnames tgm S3 fdefs ->
        cps_cvt_rel_efnlst
          S1 (eflcons n1 (Lam_e na e1) fnlst)
          vn (n :: fnames) tgm S3
          (Fcons n func_tag (k1::x1::nil) e1' fdefs)
  with cps_cvt_rel_branches :
         Ensemble var ->
         expression.branches_e ->
         list var ->
         var (* continuation variable *) ->
         var (* binding for scrutinee *) ->
         constr_env ->
         Ensemble var ->
         list (ctor_tag * exp) ->
         Prop :=
  | e_Brnil :
      forall S vn k r tgm,
        cps_cvt_rel_branches S brnil_e vn k r tgm S []
  | e_Brcons:
      forall S1 S2 S3 vn k r e ce bs' cbs' vars lnames n ctx_p tg dc tgm,
        tg = dcon_to_tag dc tgm ->
        FromList vars \subset S2 ->

        NoDup vars ->
        Datatypes.length vars = N.to_nat n ->


        ctx_bind_proj tg r vars (N.to_nat n) = ctx_p ->

        cps_cvt_rel_branches S1 bs' vn k r tgm S2 cbs' ->
        
        cps_cvt_rel (S2 \\ (FromList vars)) e (vars ++ vn) k tgm S3 ce ->

        cps_cvt_rel_branches
          S1 (brcons_e dc (n, lnames) e bs') vn k r tgm S3 ((tg, app_ctx_f ctx_p ce)::cbs').


  End CPS.


  Section ANF.
    
    Definition anfM := @compM' unit.
    
  
  (* Converting a DeBruijn index to named variable *)
  (** The actual map grows from 1 onward. We keep the pointer p to the last entry of the map. 
      When we have to lookup DeBruijn index i in the map, we lookup (p - i). *)

    Definition var_map := (M.t var * N)%type.
    
    Definition get_var_name (vmp : var_map) (x : N) :=
      let (vm, p) := vmp in
      match (p - x)%N with
      | N0 => None
      | Npos pos => M.get pos vm
      end.
    
    Definition add_var_name (vmp : var_map) (x' : var) :=
      let (vm, p) := vmp in
      let p' := N.succ_pos p in
      (M.set p' x' vm, Npos p').

    Definition new_var_map := (M.empty var, 0%N). 


    Inductive anf_value :=
    | Anf_Var (x : var)
    | Anf_App (f x : var)
    | Constr (c : ctor_tag) (xs : list var)
    | Proj (c : ctor_tag) (n : N) (y : var)
    | Fun (ft : cps.fun_tag) (x : var) (e : cps.exp)
    | Prim (pr : positive) (xs : list var).

    Definition anf_term : Type := anf_value * exp_ctx.

    Definition anf_term_to_exp (t : anf_term) : anfM cps.exp :=
      let '(v, C) := t in
      match v with
      | Anf_Var x => ret (C |[ Ehalt x ]|)
      | Anf_App f x => ret (C |[ Eapp f func_tag [x] ]|)
      | Constr c xs =>
        x' <- get_named_str "y" ;; (* Get variable for interim result *)
        ret (C |[ Econstr x' c xs (Ehalt x') ]|)
      | Proj c n y =>
        x' <- get_named_str "y" ;; (* Get variable for interim result *)
        ret (C |[ Eproj x' c n y (Ehalt x') ]|)
      | Fun ft x e =>
        x' <- get_named_str" y" ;; (* Get variable for interim result *)
        ret (C |[ Efun (Fcons x' ft [x] e Fnil) (Ehalt x') ]|)
      | Prim pr xs =>
        x' <- get_named_str "y" ;; (* Get variable for interim result *)
        ret (C |[ Eprim x' pr xs (Ehalt x') ]|)
      end.

    Definition anf_term_to_ctx (t : anf_term) (n : name) : anfM (var * exp_ctx) :=
      let '(v, C) := t in
      match v with
      | Anf_Var x => ret (x, C)
      | Anf_App f x =>
        x' <- get_named n ;; (* Get variable for interim result *)
        ret (x', comp_ctx_f C (Eletapp_c x' f func_tag [x] Hole_c))
      | Constr c xs =>
        x' <- get_named n ;; (* Get variable for interim result *)
        ret (x', comp_ctx_f C (Econstr_c x' c xs Hole_c))
      | Proj c i y =>
        x' <- get_named n ;; (* Get variable for interim result *)
        ret (x', comp_ctx_f C (Eproj_c x' c i y Hole_c))
      | Fun ft x e =>
        x' <- get_named n ;; (* XXX keep n or n'? *)
        ret (x', comp_ctx_f C (Efun1_c (Fcons x' ft [x] e Fnil) (Hole_c)))
      | Prim pr xs =>
        x' <- get_named n ;; (* Get variable for interim result *)
        ret (x', comp_ctx_f C (Eprim_c x' pr xs Hole_c))
      end.

    Definition def_name := nNamed "y".
    

    Section Convert.

      Context (tgm : conId_map).
      
      Fixpoint proj_ctx (names : list name) (i : N)
               (scrut : var) (vm : var_map) ct : anfM (exp_ctx * var_map) :=
        match names with
        | [] => ret (Hole_c, vm)
        | n :: ns =>
          x <- get_named n;;
          let vm' := add_var_name vm x in
          cvm <- proj_ctx ns (i+1)%N scrut vm' ct ;; 
          let (C, vm'') := cvm in
          ret (Eproj_c x ct i scrut C, vm'')
        end.

      Fixpoint add_fix_names (B : efnlst) (vm : var_map) : anfM (list var * var_map):=
        match B with
        | eflnil => ret ([], vm)
        | eflcons n _ B' =>
          f_name <- get_named n ;;
          lvm <- add_fix_names B' (add_var_name vm f_name) ;;
          let '(fs, vm') := lvm in
          ret (f_name :: fs, vm')     
        end.

      Fixpoint convert_prim_anf (n : nat) (* arity *)
               (prim : positive) (args : list var) : anfM anf_term :=
        match n with
        | 0%nat =>
          x <- get_named_str "prim" ;; 
          ret (Anf_Var x, Eprim_c x prim (List.rev args) Hole_c)
        | S n =>
          arg <- get_named_str "p_arg" ;; 
          f <- get_named_str "prim_wrapper" ;; 
          '(anf_val, C) <- convert_prim_anf n prim (arg :: args) ;;
          match anf_val with
          | Anf_Var x =>
            ret (Anf_Var f,  Efun1_c (Fcons f func_tag [arg] (C|[ Ehalt x ]|) Fnil) Hole_c)
          | _ => failwith "Internal error: Expected Anf_Var but found something else."
          end
        end.


      Fixpoint convert_anf (e : expression.exp) (vm : var_map) : anfM anf_term :=
        match e with
        | Var_e x =>
          match get_var_name vm x with
          | Some v => ret (Anf_Var v, Hole_c)
          | None => failwith  "Unknown DeBruijn index"
          end
        | App_e e1 e2 =>
          a1 <- convert_anf e1 vm ;;
          a2 <- convert_anf e2 vm ;;
          xc1 <- anf_term_to_ctx a1 def_name ;;
          xc2 <- anf_term_to_ctx a2 def_name ;;
          let '(x1, C1) := xc1 in
          let '(x2, C2) := xc2 in
          ret (Anf_App x1 x2, comp_ctx_f C1 C2)
        | Lam_e n e1 =>
          x <- get_named n ;; (* get the name of the argument *)
          a1 <- convert_anf e1 (add_var_name vm x) ;;
          e_body <- anf_term_to_exp a1 ;;
          ret (Fun func_tag x e_body, Hole_c)
        | Let_e n e1 e2 =>
          a1 <- convert_anf e1 vm ;;
          vC <- anf_term_to_ctx a1 n ;;
          let '(x, C1) := vC in
          a2 <- convert_anf e2 (add_var_name vm x) ;;
          let '(v, C2) := a2 in
          ret (v, comp_ctx_f C1 C2)
        | Con_e dci es =>
          let c_tag := dcon_to_tag dci tgm in
          ts <- convert_anf_exps es vm ;;
          let (ys, C) := ts in
          ret (Constr c_tag ys, C)
        | Fix_e fnlst i =>
          lvm <- add_fix_names fnlst vm ;;
          let (names, vm') := lvm in
          ds <- convert_anf_efnlst fnlst names i vm' ;;
          let (x, defs) := (ds : var * fundefs) in
          ret (Anf_Var x, Efun1_c defs Hole_c)
        | Match_e e1 n bl =>
          (* Zoe: For pattern matching compilation the situation is tricky because they always have to occur in tail
           * position in L6. Our solution currently is to create a function that receives the scrutiny as an arg 
           * pattern matches it, and returns the result of the pattern match. For those that are in tail position
           * these functions will be inlined by shrink reduction yielding the expected compilation result.
           * However, for those that are intermediate results these functions will appear in the C code.
           * Another approach would be to use some form of local continuations (join points) to capture the continuation
           * of the pattern-match. This might be preferable because the join point will always be a tail call. 
           *)
          a <- convert_anf e1 vm ;;
          f <- get_named_str "f_case" ;; (* Case-analysis function *)
          y <- get_named_str "s" ;; (* Scrutinee argument *)
          pats <- convert_anf_branches bl y vm ;;
          xc <- anf_term_to_ctx a def_name ;;
          let (x, C) := xc in
          let C_fun := Efun1_c (Fcons f func_tag [y] (Ecase y pats) Fnil) C in
          ret (Anf_App f x, C_fun)
        | Prf_e =>
          (* Zoe: Because a lot of dead code is *not* being eliminated *)
          ret (Constr default_tag [], Hole_c)            
        (* f <- get_named_str "f_proof" ;; *)
        (* y <- get_named_str "x" ;; *)
        (* let c := consume_fun f y in              *)
        (* ret (Anf_Var f, c) *)
        | Prim_e p =>
          match M.get p prim_map with
          | Some (nm, s, ar) => convert_prim_anf ar p []
          | None =>failwith "Internal error: identifier for primitive not found"
          end
        end    
      with convert_anf_exps (es : expression.exps) (vm : var_map) : anfM (list var * exp_ctx) :=
             match es with
             | enil => ret ((@nil var), Hole_c)
             | econs e es' =>
               ts <- convert_anf_exps es' vm ;;
               a <- convert_anf e vm ;;
               t <- anf_term_to_ctx a def_name ;;
               let (y, C1) := (t : var * exp_ctx) in
               let (ys, C2) := ts in
               ret (y :: ys, comp_ctx_f C1 C2)
             end
      with convert_anf_efnlst (fdefs : expression.efnlst) (names : list var) (i : N) (vm : var_map) : anfM (var * fundefs) :=
             match fdefs, names with
             | eflnil, nil => ret (1%positive (* dummy var *), Fnil)
             | eflcons n e fdefs', f_name :: names =>
               a1 <- convert_anf e vm ;;
               match a1 with
               | (Fun ft arg e_body, Hole_c) =>
                 ds <- convert_anf_efnlst fdefs' names (i - 1)%N vm ;;
                 let (fi, defs') := ds in
                 let fi' := match i with
                            | 0%N => f_name
                            | Npos _ => fi
                            end in
                 ret (fi', Fcons f_name func_tag [arg] e_body defs')
               | (_, _) => failwith ("Unexpected body of fix in function " ++  print_name n)
               end
             |_, _ => failwith "Wrong number of names for mut. rec. functions"
             end
      with convert_anf_branches (bl : expression.branches_e) (scrut : var) (vm : var_map) : anfM (list (ctor_tag * exp)) :=
             match bl with
             | brnil_e => ret nil
             | brcons_e dc (i, lnames) e bl' =>
               let ctag := dcon_to_tag dc tgm in
               cm <- proj_ctx lnames 0%N scrut vm ctag ;;
               let (Cproj, vm') := cm in
               a <- convert_anf e vm' ;;
               e' <- anf_term_to_exp a ;;
               pats' <- convert_anf_branches bl' scrut vm ;;
               ret ((ctag, Cproj |[ e' ]|) :: pats')
             end.
      
    End Convert.
    

    Definition convert_anf_exp dcm e : anfM cps.exp :=
      a <- convert_anf dcm e new_var_map ;;
      anf_term_to_exp a.
    
    (** * Top-level convert function *)
    
    Definition convert_top_anf (ee: ienv * expression.exp) : error cps.exp * comp_data :=
      let '(_, cenv, ctag, itag, dcm) := convert_env (fst ee) in
      let ftag := (func_tag + 1)%positive in
      let fenv : fun_env := M.set func_tag (1%N, (0%N::nil)) (M.empty _) in
      let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
      let '(res_err, (comp_d', _)) := run_compM (convert_anf_exp dcm (snd ee)) comp_d tt in
      (res_err, comp_d').
    
  End ANF.


End Translate. 
