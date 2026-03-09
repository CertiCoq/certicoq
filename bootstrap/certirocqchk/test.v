From CertiRocq.CertiRocqCheck Require Import Loader.

Definition foo := (fun x : nat => x + 0 = 0).

CertiRocqCheck foo.
