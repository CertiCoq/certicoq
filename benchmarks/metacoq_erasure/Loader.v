From MetaRocq Require Import ExtractableLoader.
From CertiCoq Require Export CertiCoqVanilla. (* We reuse the ML certicoq plugin to parse options and print Clight code *)
(* Using Export to get the primitives registrations the *)
Declare ML Module "coq-certicoq-bootstrapped-erasure.plugin".
