# Structure of the directory

## λ_ANF definitions

* `cps.v`: The definition of λ_ANF. (file is named CPS for historical reasons)
* `eval.v`: Semantics of λ_ANF
* `cps_show.v`: Pretty printing λ_ANF
* `algebra.v`: Monoid definitions used in the semantics
* `ctx.v`: 1-hole contexts
* `cps_util.v`: useful facts about λ_ANF
* `identifiers.v`: definitions related to λ_ANF variables (free, bound, etc.)
* `stemctx.v`: bound vars in the stems of 1-hole contexts
 
Lines of code: spec 4394/proof 4980/comments 874

## Transformations and proofs

* `LambdaBoxLocal_to_LambdaANF.v`: CPS conversion to λ_ANF
* `LambdaBoxLocal_to_LambdaANF_ANF.v`: direct-style conversion to λ_ANF
* `closure_conversion.v`: Closure conversion (as a computation and as a relation)
* `closure_conversion_util.v`: Useful facts about closure conversion 
* `closure_conversion_correct.v`: Closure conversion (relation) is semantically correct
* `closure_conversion_corresp.v`: The closure conversion program refines the closure conversion relation
* `lambda_lifting.v`: Lambda lifting (as a computation and as a relation)
* `lambda_lifting_correct.v`: Lambda lifting (relation) is semantically correct
* `lambda_lifting_corresp.v`: The lambda lifting program refines the lambda lifting relation
* `hoisting.v`: Implementation and correctness for the hoisting transformation
* `inline_letapp.v`: Inlining helper to inline let-bound calls (+ proofs)
* `inline.v` : Implementation of inlining
* `dead_param_elim.v` : Dead parameter elimination (DPE) program
* `dead_param_elim_util.v` : Useful facts about DPE (includes soundness of liveness analysis)
* `dead_param_elim_correct.v` : Useful facts about DPE (includes soundness of liveness analysis)
* `shrink_cps.v` : Shrink reduction
* `shrink_cps_correct.v`: Shrinking as rewrite rules + semantic correctness
* `shrink_cps_corresp.v`: Shrinking transformation sound w.r.t. shrinking as rewrite rules
* `shrink_cps_toplevel.v`: Shrinking toplevel theorem 
* `uncurry.v`: Old implementation of uncurrying (now derived automatically)
* `uncurry_rel.v`L Uncurry relation
* `uncurry_correct.v`: Correctness of uncurrying relation
* `bounds.v` : concrete bounds for transformations
* `toplevel.v` : λ_ANF pipeline
* `toplevel_theorems.v` : Top-level theorems for each transformation and top-level theorem + corollaries for the λ_ANF pipeline

Lines of code: spec 10121/proof 25568/comments 5254


## Proof frameworks

* `logical_relations.v`: The reflexive LR
* `logical_relations_cc.v`: The closure conversion LR
* `rel_comp.v`: The compositional relational framework (+ behavioral refinement definitions)

Lines of code: spec 1729/proof 2603/comments 884


## Various libraries

* `rename.v`: renaming utils
* `state.v`: definition of the λ_ANF compilation monad
* `List_util.v`: List utilities
* `map_util.v`: Map utilities
* `relations.v`: useful facts about relations
* `set_util.v`: Set utilities
* `Ensembles_util.v`: Ensemble utilities
* `functions.v`: useful facts about functions
* `tactics.v`: some tactics

Lines of code: spec 2725/proof 4251/comments 171


Rewriting framework

* `MockExpr.v`
* `Prototype.v`
* `PrototypeGenFrame.v`
* `PrototypeTests.v`
* `Rewriting.v`
* `cps_proto.v`
* `uncurry_proto.v`
* `proto_util.v`
* `Frame.v`