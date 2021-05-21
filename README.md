# Compositional Optimizations for CertiCoq, supplementary material

We provide the sources of the CertiCoq compiler as supplementary
material for the ICFP'21 conditionally accepted paper "Compositional
Optimizations for CertiCoq".

The artifact includes the Coq sources of the CertiCoq
compiler. Compiling CertiCoq checks the proof and extracts the code of
the compiler to OCaml. 

We provide the source code of CertiCoq as a separate tarball and also
inside a virtual machine image. 


## Compiling the project in your machine

See INSTALL.md (in top-level CertiCoq directory) for installation instructions.

## Pointers from paper definitions and theorems to code

The code (implementation and proofs) for the λ_ANF pipeline lives in `theories/L6_PCPS`. 
The file `theories/L6_PCPS/STRUCTURE.md` describes the directory organization and provides some 
information about the size of the files (implementation and proofs).

### Section 2

* shrinking
  file `shrink_cps.v` line 1407: shrink_top
* uncurrying
  file `uncurry.v` contains an implementation that it is not used anymore
  now it's automatically derived from its relational spec with a new tool (not in the scope of this paper)
  file `uncurry_proto.v`  line 314: uncurry_top
* inlining
  file `inline.v` line 239: inline_top and line 259: inline_loop
* lambda lifting
  file `lambda_lift.v` line 503: lambda_lift
* closure conversion 
  file `closure_conversion.v` line 473: closure_conversion_top
* hoisting
  file `hoist.v` line 93: closure_conversion_hoist
* DPE
  file `dead_param_elim.v` line 387: DPE
* ANF Pipeline
  file `toplevel.v` line 168: anf_pipeline

### Section 3
* Semantics: file `eval.v` line 125: bstep_fuel and line 588: diverge
* Expression refinement: file `rel_comp.v` line 1001: refines
* Linking: file `rel_comp.v` line 363: link
* Value refinement: file `rel_comp.v` line 967: value_ref_cc
* Lemma 3.1: (stated using the logical relation) 
   file `logical_relations.v` line 1880: preord_exp_preserves_divergence
   and also 
   file `logical_relations_cc.v` line 1338: cc_approx_exp_preserves_divergence
 
### Section 4
* Logical relation E
   file `logical_relations.v` line 61: preord_exp' line 114: preord_val' 
* Logical relation E_cc
   file `logical_relations_cc.v` line 37: cc_approx_exp' line 94: cc_approx_val'
* Lemma 4.1 (Compatibility (Constructor)) line 701: preord_exp_constr_compat
* Lemma 4.2 (Reflexivity): file `logical_relations.v` line 1493: preord_exp_refl
* Lemma 4.3 (Transitivity): file `logical_relations.v` line 2050: preord_exp_trans
* Lemma 4.5 (Adequacy E_cc): 
   file `rel_comp.v` line 1217: Lemma cc_approx_exp_in_refines
* Lemma 4.6 (Linking compatibility E/E_cc):
   file `rel_comp.v` line 385: Lemma preord_exp_preserves_linking (for relation E) 
   file `rel_comp.v` line 385: Lemma cc_approx_exp_preserves_linking (for relation E_cc) 
* Lemma 4.7 (Linking compatibility E+): 
   file `rel_comp.v` line 616: Lemma preord_exp_n_preserves_linking (for relation E+) 
* Lemma 4.8 (Adequacy E_cc+): 
   file `rel_comp.v` line 1217: Lemma R_n_exp_in_refines
* Lemma 4.9 (Linking compatibility E_cc+): 
   file `rel_comp.v` line 385: Lemma Rel_exp_n_preserves_linking (for relation E_cc+) 

### Section 5
* Top-level theorems of transformations
  - Closure conversion: file `closure_conversion_correct.v` line 1234: exp_closure_conv_correct
  - Lambda lifting: file `lambda_lifting_correct.v` line 1701: lambda_lift_correct_top
  - Uncurry: file `uncurry_correct.v` line 3086: uncurry_correct_top
  - Hoisting: file `hoisting.v` line 1189: exp_hoist_correct_top
  - DPE: file `dead_param_elim_correct.v` line 1315: DPE_correct_top
  - Inlining: file `inline_correct.v` line 2366: inline_correct_top
  - Shrink: file `shrink_cps_toplevel.v` line 77: shrink_corresp_top

The file bound.v contains the definitions of the concrete
instantiating of the local invariants for different transformations.

* Definition 5.1 (correct/correct_cc): 
   file `toplevel_theorems.v` line 64: correct (w.r.t. relation E+) 
   file `toplevel_theorems.v` line 58: correct_cc (for relation E_cc+) 
	
   Top-level theorems w.r.t. correct and correct_cc for all λ_ANF transformations are in lines 73- 482

* Composing correct and correct_cc  (the three bullet points in line 1104): 
   file `toplevel_theorems.v` line 496: correct_compose
   file `toplevel_theorems.v` line 513: correct_cc_compose_l
   file `toplevel_theorems.v` line 534: correct_cc_compose_r
	
* Theorem 5.2 (Correctness of the λ_ANF pipeline): 
   file `toplevel_theorems.v` line 588: anf_pipeline_correct
 
* Corollary 5.3
   file `toplevel_theorems.v` line 661: anf_pipeline_whole_program_correct

* Corollary 5.4
   file `toplevel_theorems.v` line 709: anf_pipeline_linking_correct

## Running the experiments

Once CertiCoq is compiled and installed, you can make the our our benchmark
suite (see benchmarks/README.md). 

This will compile the Gallina programs with CertiCoq, and then the CertiCoq-generated C code with clang.

To reproduce the experiments of the paper, run

	   # sh run_benchmarks.sh N

where N is the desired number of runs (in separate processes). In the paper we use N=10.

This prints a table with the following columns:

* Benchmark: name of the benchmark, some microbenchmarks (that do not appear in the paper) are included too
* CertiCoq: time (in ms) of the -O0 configuration 
* Ratio: CertiCoq -O0 / CertiCoq -O0 (obviously always 1)
* Dev: standard deviation
* CertiCoqO: time (in ms) of the -O1 configuration 
* Ratio: CertiCoq -O1 / CertiCoq -O0
* Dev: standard deviation
* CertiCoqL: time (in ms) of the -O1 -lift-all configuration 
* Ratio: CertiCoq -O1 -lift-all / CertiCoq -O0
* Dev: standard deviation
* CertiCoqCComp: time (in ms) of the -O0 configuration compiled with Compcert
* Ratio: CertiCoq -O1 -lift-all / CertiCoq -O0
* Dev: standard deviation
* ocamlc: time (in ms) of the OCaml bytecode
* Ratio: ocamlc / CertiCoq -O0
* Dev: standard deviation
* ocamlopt: time (in ms) of the OCaml native code
* Ratio: ocamlopt / CertiCoq -O0
* Dev: standard deviation

## Axioms

Our proof development assumes the following axioms: 
(You may also look at the very end of file `theories/L6_PCPS/toplevel_theorems.v`, 
 where the output of the Print Assumptions is given.)


* `inline_exp_eq : forall (St : Type) (IH : InlineHeuristic St) (d : nat) (e : exp) (sig : r_map) 
                     (fm : fun_map) (s : St), inline_exp St IH d e sig fm s = inline_exp' St IH d e sig fm s`

Our definition for inlining is defined by recursion that Coq does not
recognize as structural recursion, therefore we define it using
`Program Fixpoint` (https://coq.inria.fr/refman/addendum/program.html).

Program Fixpoint generates a really large term that is not practical
for proofs. Coq programmers commonly define an (non-recursive) auxiliary 
definition (here inline_exp') that unfolds one step of the recursion (and calls
into inline_exp), and then prove that the two definitions are equal.
We had some technical difficulties proving that fact for inline_exp,
and we are in contact with the Coq developers for getting technical
help (but we are also considering changing the definition a bit to
make it structurally recursive with an additional fuel argument).

We are certain that the two definitions are indeed equal (the code was
copy-pasted and checked multiple times).


* `ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2`

* `FunctionalExtensionality.functional_extensionality_dep : forall (A : Type) (B : A -> Type)
                                                           (f g : forall x : A, B x),
                                                         (forall x : A, f x = g x) -> f = g`

A similar proof as the one described above, but for the shrinking
transformation, requires these facts (in shrink_cps.v).


# CertiCoq

<p align="center">
<img src="ANONYMIZED" alt="MetaCoq" width="100px"/>
</p>

## Overview

CertiCoq is a compiler for Gallina, the specification language of the [Coq proof assistant](https://coq.inria.fr/refman/index.html). CertiCoq targets Clight, a subset of the C language that can be compiled with any C compiler, including the [CompCert](http://compcert.org) verified compiler.

Large parts of the CertiCoq compiler have been verified whereas others are in the process of being verified.

## Documentation

The [CertiCoq Wiki](ANONYMIZED) has instructions for using the [CertiCoq plugin](ANONYMIZED) to compile Gallina to C and interfacing with the generated C code.

You can also find some demos [here](ANONYMIZED) and [here](ANONYMIZED).

## Installation Instructions

See [INSTALL.md](INSTALL.md)  for installation instructions.

## Current Members

ANONYMIZED

## Past Members and Contributors

ANONYMIZED

## License 

CertiCoq is open source and distributed under the [MIT license](LICENSE.md).

## Directory structure

* `theories/` contains the sources of the compiler
* `plugin/` contains the CertiCoq plugin for Coq 
* `benchmarks/` contains the benchmark suite
* `glue/` contains the glue code generator

Structure of the theories directory:

* `theories/common`: contains common code utilities 
* `theories/Compiler`: contains the toplevel CertiCoq pipeline 
* `theories/L1g`: 1st pass, moves from (MetaCoq's) λbox to our similar L1g
* `theories/L2k_noCnstrParams`: 2nd pass, eta expands constructors and removes constructor parameters 
* `theories/L4_deBruijn`: 3rd pass, let-bind environment
* `theories/L6_PCPS` contains the λANF pipeline (and conversions -- direct and CPS -- to λANF)
* `theories/L7` contains the C code generator.
* `theories/compcert` contains a local copy of the compcert compiler


## Bugs 

We use github's [issue tracker](https://github.com/PrincetonUniversity/certicoq/issues) to keep track of bugs and feature requests.
