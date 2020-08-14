From CertiCoq.L6 Require Import PrototypeGenFrame.

Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Import ListNotations.

From MetaCoq Require Import Template.All.

(* Unset Strict Unquote Universe Mode. *)

Definition var := nat.
Definition constr := nat.
Inductive exp :=
| eHalt (x : var)
| eApp (f : var) (xs : list var)
| eCons (x : var) (c : constr) (ys : list var) (e : exp) (* let x = c ys in e *)
| eProj (x : var) (y : var) (n : nat) (e : exp)
| eCase (x : var) (arms : list (constr × exp))
| eFuns (fds : list fundef) (e : exp)
with fundef := fFun (f : var) (xs : list var) (e : exp).

Run TemplateProgram (mk_Frame_ops "exp" exp [var; constr; nat; list var]).

Print exp_univ.
Print exp_univD.
Print exp_frame_t.
Print exp_frameD.
Print exp_Frame_ops.
Print exp_aux_data.

Instance Frame_exp : Frame exp_univ := exp_Frame_ops.
Instance AuxData_exp : AuxData exp_univ := exp_aux_data.
