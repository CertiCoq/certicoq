Require Import run cps.

Check run.

Definition pr0 : prims := M.empty _.

Definition runcps := run _ (stepf pr0).

Check runcps.

