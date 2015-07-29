(** Collect all of L3 together **)

Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStrippedL1" as L2.
Add LoadPath "." as L3.
Require Export L3.term L3.program L3.wndEval L3.wcbvEval L3.wNorm 
        L3.unaryApplications.