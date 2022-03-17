From MetaCoq.Template Require Import ExtractableLoader.
From CertiCoq Require Import CertiCoq. (* We reuse the ML certicoq plugin to parse options and print Clight code *)

Declare ML Module "certicoqc_plugin".