Require Import MetaCoq.Utils.bytestring.
From Coq Require Import ZArith.ZArith Lists.List micromega.Lia Arith
     Ensembles Relations.Relation_Definitions.
Require Import Common.AstCommon.
Require compcert.lib.Maps compcert.lib.Coqlib.
Require Import set_util.

Import ListNotations.
Open Scope list_scope.

Require Import LambdaBoxLocal.expression LambdaBoxLocal.fuel_sem.
Require Import cps cps_show eval ctx logical_relations
        List_util algebra alpha_conv functions Ensembles_util
        LambdaBoxLocal_to_LambdaANF LambdaBoxLocal_to_LambdaANF_util LambdaBoxLocal_to_LambdaANF_corresp
        LambdaBoxLocal_to_LambdaANF_correct
        LambdaANF.tactics identifiers bounds cps_util rename.


Require Import ExtLib.Data.Monads.OptionMonad ExtLib.Structures.Monads.

Import Monad.MonadNotation.

Open Scope monad_scope.


Section ANF_proof.

  Context (cenv : conId_map) (ctenv : ctor_env).
  Context (func_tag default_tag : positive).

  (** ** ANF value relation *)

  Definition convert_anf_rel := convert_anf_rel func_tag default_tag.
  Definition convert_anf_rel_exps := convert_anf_rel_exps func_tag default_tag.

  Definition anf_env_rel' (P : value -> val -> Prop) (vn : list var)
             (vs : list value) (rho : M.t val) :=
    Forall2 (fun v x => exists v',  M.get x rho = Some v' /\ P v v') vs vn.


  Inductive anf_fix_rel (fnames : list var) (env : list var) : Ensemble var -> list var -> efnlst -> fundefs -> Ensemble var -> Prop :=
  | fix_fnil :
    forall S, anf_fix_rel fnames env S [] eflnil Fnil S
  | fix_fcons :
    forall S1 S1' S2 S2' S3 fnames' e1 C1 r1 n n' efns B f x,
      x \in S1 ->
      S1' \subset S1 \\ [set x] ->
      S2' \subset S2 ->

      convert_anf_rel S1' e1 (x :: List.rev fnames ++ env) cenv S2 C1 r1 ->

      anf_fix_rel fnames env S2' fnames' efns B S3 ->

      anf_fix_rel fnames env S1 (f :: fnames') (eflcons n' (Lam_e n e1) efns) (Fcons f func_tag (x::nil) (C1 |[ Ehalt r1 ]|) B) S3.


  Inductive anf_val_rel : value -> val -> Prop :=
  | rel_Con :
    forall vs vs' dc c_tag,
      Forall2 (fun v v' => anf_val_rel v v') vs vs' ->
      dcon_to_tag default_tag dc cenv = c_tag ->
      anf_val_rel (Con_v dc vs) (Vconstr c_tag vs')
  | rel_Clos :
    forall vs rho names na x f e C r S1 S2,
      anf_env_rel' anf_val_rel names vs rho ->

      NoDup names ->

      Disjoint var (x |: FromList names) S1 ->

      ~ x \in [set f] :|: FromList names ->
      ~ f \in FromList names ->

     convert_anf_rel S1 e (x::names) cenv S2 C r ->

     anf_val_rel (Clos_v vs na e)
                 (Vfun rho (Fcons f func_tag (x::nil) (C |[ Ehalt r ]|) Fnil) f)
  | rel_ClosFix :
    forall S1 S2 names fnames vs rho efns Bs n f,
      anf_env_rel' anf_val_rel names vs rho ->

      NoDup names ->
      NoDup fnames ->

      Disjoint _ (FromList names :|: FromList fnames) S1 ->
      Disjoint _ (FromList names) (FromList fnames) ->

      nth_error fnames (N.to_nat n) = Some f ->

      anf_fix_rel fnames names S1 fnames efns Bs S2 ->

      anf_val_rel (ClosFix_v vs efns n) (Vfun rho Bs f).


  Definition anf_env_rel := anf_env_rel' anf_val_rel.


  Definition convert_anf_correct_exp (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat) :=
    forall rho env C r x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->
      ~ x \in FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv (cps_bound f t) eq_fuel i
                               (Ehalt x, (M.set x v' (M.empty cps.val)))
                               (C|[ Ehalt x ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, (f <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).


  Definition convert_anf_correct_exp_step (vs : fuel_sem.env) (e : expression.exp) (r : fuel_sem.result) (f t : nat)  :=
    forall rho env C r x S S' i,
      well_formed_env vs ->
      exp_wf (N.of_nat (Datatypes.length env)) e ->

      Disjoint _ (FromList env) S ->
      ~ x \in FromList env ->

      anf_env_rel env vs rho ->

      convert_anf_rel S e env cenv S' C x ->

      (* Source terminates *)
      (forall v v', r = (Val v) -> anf_val_rel v v' ->
                    preord_exp ctenv
                               (cps_bound (f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e)
                                          (t <+> @one_i _ _ trace_resource_LambdaBoxLocal e))
                               eq_fuel i
                               (Ehalt x, (M.set x v' (M.empty cps.val)))
                               (C|[ Ehalt x ]|, rho)) /\
      (* Source diverges *)
      (r = fuel_sem.OOT ->
       exists c, ((f <+> @one_i _ _ fuel_resource_LambdaBoxLocal e) <= c)%nat /\ bstep_fuel ctenv rho (C|[ Ehalt x ]|) c eval.OOT tt).



  Definition convert_anf_correct_exps (vs : fuel_sem.env) (es : expression.exps) (vs1 : list value) (f t : nat)  :=
    forall rho env C rs S S' vs2 xs ys x ctag,
      well_formed_env vs ->
      exps_wf (N.of_nat (Datatypes.length env)) es ->

      Disjoint _ (FromList env :|: FromList xs :|: FromList ys) S ->

      Disjoint _ (FromList env) (FromList xs :|: FromList ys) ->
      Disjoint _ (FromList xs) (FromList ys) ->
      NoDup xs ->

      anf_env_rel env vs rho ->

      convert_anf_rel_exps S es env cenv S' C rs ->

      Forall2 (anf_val_rel) vs1 vs2 ->

      exists rho',
        set_lists ys vs2 (M.empty _) = Some rho' /\
        forall i,
          preord_exp ctenv (cps_bound f (t <+> (2 * Datatypes.length (exps_as_list es))%nat))
                     eq_fuel i (Econstr x ctag ys (Ehalt x), rho') (C |[ Econstr x ctag rs (Ehalt x) ]|, rho).



  Lemma convert_anf_correct :
      forall vs e r f t, eval_env_fuel vs e r f t -> convert_anf_correct_exp vs e r f t.
    Proof.
      eapply eval_env_fuel_ind' with (P1 := convert_anf_correct_exp)
                                     (P0 := convert_anf_correct_exps)
                                     (P := convert_anf_correct_exp_step).
      - (* Con_e terminates *)

    Admitted.
