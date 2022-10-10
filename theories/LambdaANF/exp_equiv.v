(* Equivalences on ANF expressions.  Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2020
 *)
 
Require Import compcert.lib.Coqlib.

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets MSets.MSetRBT
     Lists.List micromega.Lia Sets.Ensembles.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.identifiers LambdaANF.ctx LambdaANF.map_util
        LambdaANF.Ensembles_util LambdaANF.List_util LambdaANF.tactics LambdaANF.set_util LambdaANF.algebra LambdaANF.logical_relations.
    
Import ListNotations.

Close Scope Z_scope.



Section LogRelEquiv.

  (** "Logical" equivalence of ANF expressions. *)

  Context (cenv : ctor_env)
          (fuel : Type) (Hf : @fuel_resource fuel)
          (trace : Type) (Ht : @trace_resource trace)
          (Post : @PostT fuel trace) (PostG : @PostGT fuel trace)
          (Hprop : Post_properties cenv Post Post PostG)
          (HpropG : Post_properties cenv PostG PostG PostG). 


  
  Definition equiv_exp (p1 p2 : exp * env) : Prop := 
    (forall k, preord_exp cenv Post PostG k p1 p2) /\
    (forall k, preord_exp cenv Post PostG k p2 p1).


  
  Global Instance equiv_exp_Reflexive : Reflexive equiv_exp.
  Proof.
    constructor; destruct x; intros jk.
    - eapply preord_exp_refl. eassumption.
      eapply preord_env_P_refl. eassumption.
    - eapply preord_exp_refl. eassumption.
      eapply preord_env_P_refl. eassumption.
  Qed. 

  Context (Hincl : inclusion _ (comp PostG PostG) PostG)
          (HinclG1 : inclusion _ PostG Post)
          (HinclG2 : inclusion _ Post PostG).

  
  (* TODO move. + inclusion_refl in rel_comp.v *)
  Lemma inclusion_trans A P1 P2 P3 :
    inclusion A P1 P2 -> inclusion A P2 P3 -> inclusion A P1 P3.
  Proof.
    clear. firstorder.
  Qed. 
  
  Global Instance equiv_exp_Transitive : Transitive equiv_exp.
  Proof.
    constructor; destruct x, y, z; intros k.
    - eapply preord_exp_post_monotonic.
       
      eapply inclusion_trans. eapply Hincl. eassumption. 
      
      inv H. inv H0.
      eapply preord_exp_trans; eauto.
      eapply preord_exp_post_monotonic; eauto.
      intros. 
      eapply preord_exp_post_monotonic; eauto.
      
    - eapply preord_exp_post_monotonic.
      
      eapply inclusion_trans. eapply Hincl. eassumption. 
      
      inv H. inv H0.
      eapply preord_exp_trans; eauto.
      eapply preord_exp_post_monotonic; eauto.
      intros. 
      eapply preord_exp_post_monotonic; eauto.

  Qed.
  

  Global Instance equiv_exp_PreOrder : PreOrder equiv_exp.
  Proof. constructor; tci. Qed.
  

  Example rewrite_exp_equiv p1 p2 p3 :
    equiv_exp p2 p1 -> equiv_exp p2 p3.
  Proof.
    intros H. rewrite H.
  Abort.

  Example rewrite_exp_equiv p1 p2 p3 :
    equiv_exp p2 p1 -> equiv_exp p2 p3.
  Proof.
    intros H. rewrite H.
  Abort.

    Global Instance equiv_exp_Symmetric : Symmetric equiv_exp.
  Proof.
    constructor; destruct x, y; intros k; inv H; eauto.
  Qed.



  Global Instance equiv_exp_Equivalence : Equivalence equiv_exp.
  Proof. constructor; tci. Qed.

  Example rewrite_exp_equiv p1 p2 p3 :
    equiv_exp p1 p2 -> equiv_exp p2 p3.
  Proof.
    intros H. rewrite <- H.
  Abort.

End LogRelEquiv.

