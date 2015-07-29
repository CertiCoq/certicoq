Require Import Template.Template.
Require Import String.

Definition foo := 1 + 1.

Quote Definition foo_syn := Eval cbv delta [ foo ] in foo.

Make Definition foo_sem := Eval compute in foo_syn.
