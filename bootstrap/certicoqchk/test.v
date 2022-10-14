From CertiCoq.CertiCoqCheck Require Import Loader.

Definition foo := (fun x : nat => x = 0).

CertiCoqCheck foo.