(** Collect all Common together **)

Add LoadPath "../../../template-coq-coq-8.5-coqOpam/theories" as Template.
Require Export Template.Ast.

Add LoadPath "../common" as Common.
Require Export Common.exceptionMonad.
Require Export Common.RandyPrelude.
Require Export Common.AstCommon.
