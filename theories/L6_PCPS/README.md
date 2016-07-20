# Description of the L6_PCPS directory

### cps.v
The syntax of the L6 language.

### eval.v
The evaluation semantics of the L6 language. 
  
### cps_util.v
Useful lemmas and definitions about the L6 language.
 
(TODO: Once we semantics are updated, we should clean-up a bit these three files) 

### identifiers.v
Definitions and lemmas about identifiers in L6. Among others, it contains
formalizations of free variables, bound variables, unique bindings, and useful
lemmas about them.

### logical_relations.v
Step-indexed logical relations. They are used in the correctness proofs of
function hoisting and closure conversion.

### L5_to_L6.v
Translation from L5 to L6.

### shrink_cps.v
Shrink reduction.

### uncurry.v  
Uncurrying transformation for the L6 language.

### closure_conversion.v
Relational and computational definitions of closure conversion.

### closure_conversion_correct.v
Semantics preservation for the closure conversion relation.

### closure_conversion_corresp.v
Correspondence of the relational and computational definitions of closure
conversion.

### hoisting.v
Function hoisting (relational and computational definition), correspondence of
the two definitions and semantics preservation proof.

### cps_show.v
Pretty printer for the L6 language.

### alpha_conv.v
Formalization of alpha equivalence and semantics preservation proof.

### ctx_approx.v
Definition of of contextual approximation and equivalence. Proof that one of the
logical relations is sound w.r.t. contextual approximation.

### env.v
Formalization of well-scopedness. (Maybe change the name of the file?)

  
## General libraries (not L6 related. Maybe move them to an other directory?)

### hoare.v
Hoare triples definitions and lemmas to reason about the state monad.
### Ensembles_Util.v
Useful definitions and lemmas about ensembles.
### List_util.v
Useful definitions and lemmas about lists.
### set_util.v
Useful definitions and lemmas about red-black sets (MSetRBT).
### functions.v
Useful definitions and lemmas about functions (extensional equality, image,
codomain, injectivity, etc.).
