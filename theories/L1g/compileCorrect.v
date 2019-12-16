
From MetaCoq.Template Require Import utils.
From MetaCoq.Erasure Require Import EWcbvEval.
Require Import L1g.compile L1g.term L1g.program L1g.wcbvEval.



Lemma WcbvEval_hom:
  forall (Σ : global_declarations) t t',
    EWcbvEval.eval t t' -> True.

(**********************
                    L2d.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2d.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
Admitted.
*********************)