(** Collect all of L2 together **)

Add LoadPath "../common" as Common.
Add LoadPath "." as L2.
Require Export L2.term L2.program L2.wndEval L2.wcbvEval L2.wNorm.
Require Export L2.stripEvalCommute.
