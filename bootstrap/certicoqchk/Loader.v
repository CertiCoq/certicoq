From MetaCoq Require Import ExtractableLoader.
From CertiCoq Require Export CertiCoqVanilla. (* We reuse the ML certicoq plugin to parse options and print Clight code *)

Declare ML Module "coq-certicoqchk.plugin".