(** Collect all of L2 together **)

Add LoadPath "../L2_typeStripped" as L2.

Require Export L2.compile.
Require Export L2.term L2.program L2.wndEval L2.wcbvEval L2.wNorm.
Require Export L2.stripEvalCommute.
