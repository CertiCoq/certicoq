From MetaRocq Require Import ExtractableLoader.
From CertiCoq Require Export CertiCoqVanilla. (* We reuse the ML certicoq plugin to parse options and print Clight code *)
(* Use Export to export the primitives registrations *)

Declare ML Module "coq-certicoqc.plugin".
