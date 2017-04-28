Require Export Common.certiClasses.
Require Export Common.certiClasses2.
Require Export L2.instances.
Require Export L1g.instances.
Require Export L2_5.instances.
Require Export L2k.instances.
Require Export L3.instances.
Require Export L4.instances.
Require Export L6.instances.


Set Template Cast Propositions.

                
Open Scope Z_scope.
Require Import ZArith.
(* Print Instances CerticoqLanguage. *)

Require Import Common.Common.
Require Import String.
Open Scope string_scope.






Quote Recursively Definition One := 1%positive.
Quote Recursively Definition p := (3+4)%nat.
(*
Eval vm_compute in (ctranslateEval certiL4 p 100).
Eval vm_compute in (ctranslateEval certiL4_2 p 100).
Eval vm_compute in (ctranslateEval certiL4_5 p 100).
*)



(*
Eval compute in (ctranslateTo certiL4 p).

Time Eval compute in (ctranslateTo certiL5a p).


Eval compute in (cTerm certiL6).

*)

(* 
To debug typeclass resolution problems, try:
Typeclasses eauto := 5. (* or a small number to limit the search depth *)
Typeclasses eauto := debug. (* if your ide doesn't show debug messages, use coqc *)
Print Instances CerticoqTranslation.
Print Instances CerticoqTotalTranslation.
Print Instances CerticoqLanguage.
*)

Definition swap' := 
(fun  (p: nat  * bool) =>
match p with
(x,y) => (y,x)
end).




Quote Recursively Definition swap := ((swap' (S O, false)), (swap' (O, true))).


Ltac computeExtract certiL4 f:=
(let t:= eval compute in (translateTo (cTerm certiL4) f) in 
     match t with
       |Ret ?xx => exact xx
     end).

Definition swap4 : (cTerm certiL4).
computeExtract certiL4 swap.
Defined.

Definition swap4a : cTerm certiL4_5.
computeExtract certiL4_5 swap.
Defined.

Print swap4.


About  Nat.le_lt_trans. 
SearchAbout ( (_ <= _)%nat -> (_ < _)%nat -> (_ < _)%nat).
About OrdersEx.Nat_as_DT.le_lt_trans.

(* Definition swap6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) swap) in 
match t with
|Ret ?xx => exact xx
end).
Defined.
*)


Definition One6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) One) in 
match t with
|Ret ?xx => exact xx
end).
Defined.



Quote Recursively Definition prev := (fun x => 
 match x with
 | 0 => 0
| S n => n
end)%nat.



(*Local Opaque L4_2_to_L5.Match_e.
Local Opaque L4_2_to_L5.Fix_e.
Local Opaque L4_2_to_L5.Con_e.
Local Opaque L4_2_to_L5.Lam_e.
Local Opaque L4_2_to_L5.Let_e.
Local Opaque L4_2_to_L5.App_e.
*)

Definition prev4 : cTerm certiL4.
computeExtract certiL4 prev.
Defined.

Definition prev4a : cTerm certiL4_5.
computeExtract certiL4_5 prev.
Defined.

Definition prev5 : cTerm certiL5.
(let t:= eval vm_compute in (translateTo (cTerm certiL5) prev) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

Definition prev5a : cTerm certiL5a.
(let t:= eval vm_compute in (translateTo (cTerm certiL5a) prev) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Print prev4.
Print prev4a.
Print prev5.
Print prev5a.

Print prev.

Require Import L3.instances.
Eval compute in (cTerm certiL3).

Definition prev3 := ltac:(computeExtract certiL3 prev).

Require Import L3_to_L4.
Definition prev3Ienv := L4.L3_to_L4.inductive_env (AstCommon.env prev3).
Eval vm_compute in prev3Ienv.

Require Import NPeano.
Require Import Recdef.
Set Implicit Arguments.
Require Import Omega.

Function Gcd (a b : nat) {wf lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (b mod S k)  (S k)
end
.
Proof.
- intros m n k Heq. subst. apply Nat.mod_upper_bound.
  omega.
- exact lt_wf.
Defined.

Lemma fooAx1 : forall n n0 : nat, n = S n0 -> (id n0 < id (S n0))%nat.
Admitted.


Check ltac:(let t:= type of fooAx1 in exact t). (** Prop *)
Function foo (n:nat) {measure id n} : nat:=
  match n with
  | O => 1%nat
  | S n => foo n
  end.
exact fooAx1.
Defined.



(** unfold just enough so that the fixpoint structure is visible *)
Quote Recursively Definition pfoo :=
  ltac:(let t:= eval unfold foo,foo_terminate in foo in exact (t 1%nat)).


Definition pfoo3 := Eval native_compute in (ctranslateTo certiL3 pfoo).

(** show the main body (discard the env) of an L3 term *)
Definition showMainBody3 (t : exception (cTerm certiL3)) : exception L3.compile.Term :=
  exception_map (@main _ ) t.

(** Show the definition a particilar item (identified by name) in the environment *)
Definition showEnvNamed (name: string) (t : exception (cTerm certiL3)) :=
  exception_map (fun tt => lookup name (@AstCommon.env _ tt)) t.

Require Import L3.compile.
Set Printing Depth 10000.
Eval vm_compute in (showMainBody3 pfoo3).
Eval vm_compute in (ctranslateEval certiL4 pfoo (N.to_nat 9000)).




Set Template Cast Propositions.
Time Quote Recursively Definition pgcd := Gcd.

Let pcgd2 : cTerm certiL3.
let T:= eval vm_compute in (L3.compile.program_Program pgcd) in exact T.
Defined.

(*
Let pcgd4a : cTerm certiL4_5.
(let t:= eval vm_compute in (certiClasses.translate (cTerm certiL2) (cTerm certiL4_5) pcgd2) in
match t with
|Ret ?xx => exact xx
end).
Defined. *)

Require Import List.
Import ListNotations.
(* the Gcd_terminate function is in the environment. Below, *)
(* we project that part of the environment. *)
(* The environment is too big, because it contains even the *)
(* definitions that were used in the erased proof. *)
(* Eval vm_compute in (nth_error (AstCommon.env pcgd2) 1). *)
(* Eval vm_compute in (nth_error (AstCommon.env pcgd3) 1). *)

Require Import SquiggleEq.terms.

Require Import  ExtLib.Data.String.

(*
Definition pgcd4astr : string.
let t:= eval vm_compute in (print4 pcgd4a) in exact t.
Defined.
Eval compute in pgcd4astr.
*)
(*

Print Instances BigStepOpSemExec.
Definition L42normalize (t: cTerm certiL4_2) (n: nat)
  : exception (cTerm certiL4_2)
  := bigStepEvaln n t.
*)

Require Import Benchmarks.Binom
        Benchmarks.Color
        Benchmarks.vs.

(** MS: fast up to L5, does not seem to terminate in the L5-L6 phase. *)
Definition p5a : cTerm certiL5a.
 (let t:= eval vm_compute in (translateTo (cTerm certiL5a) p) in 
match t with
|Ret ?xx => exact xx
end).
Defined.

About eq_refl.
 Print  Coq.Init.Logic.eq_refl.

Definition p6 :  (cTerm certiL6).
set (t := (certiClasses.translate (cTerm certiL5a) (cTerm certiL6) p5a)).
unfold certiClasses.translate in t.
unfold liftTotal in t. simpl in t.
unfold translateT in t.

(* unfold certiL5a_t0_L6 in t.
native_compute in t. *)
Abort.




Definition ext_comp := fun prog =>
  let t := (translateTo (cTerm certiL6) prog) in
  match t with
  | Ret xx => xx
  | _ => One6
  end.
 
Require Import L6_to_Clight.
Require Import compcert.lib.Maps.


Definition compile_L6 (t : cTerm certiL6) : L5_to_L6.nEnv * Clight.program :=
  let '((_, cenv , nenv), (_, prog)) := t in
  let p := compile prog cenv nenv in
  (fst p, stripOption (snd p)).

Open Scope positive_scope.

(* Definition p7 := compile_L6 p6. *)

Require Import L6.cps L6.cps_show.

Inductive blah : Type :=
| blah1 : blah -> blah
| blah2 : blah -> blah
| blah3 : blah
| blah4 : blah
| blah5 : blah
| blah6 : blah -> blah -> blah
| blah7 : blah
.

Fixpoint blah_fun (b : blah) : blah :=
  match b with
  | blah1 b' => blah_fun b'
  | blah2 b' => blah1 b'
  | blah3 => blah4
  | blah4 => blah1 blah3
  | blah5 => blah6 (blah1 blah7) blah5
  | blah6 b' b'' => blah2 (blah_fun b'')
  | blah7 => blah7
  end.

Definition fst_blah := blah2 (blah1 blah4).

Definition snd_blah := blah6 blah3 (blah2 blah7).

Quote Recursively Definition blahProg := (blah_fun (blah1 (blah6 fst_blah snd_blah))).

(* Definition blahProg6 : cTerm certiL6. *)
(* (let t:= eval vm_compute in (translateTo (cTerm certiL6) blahProg) in  *)
(* match t with *)
(* |Ret ?xx => exact xx *)
(* end). *)
(* Defined. *)

(* Definition blahProg7 := compile_L6 blahProg6. *)

Definition show_exn  (x : exceptionMonad.exception (cTerm certiL6)) : string :=
  match x with
  | exceptionMonad.Exc s => s
  | exceptionMonad.Ret ((p,cenv, nenv), (g, e)) => show_exp nenv cenv e
  end.









Definition L5a_comp_L6 (v:(ienv * L4.L5a.cps)): ((L6.eval.prims * cEnv * L6.eval.env * nEnv)* L6.cps.exp):= 
    match v with
        | pair venv vt => 
          let '(cenv, nenv, t) := L6.L5_to_L6.convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) in
          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv), M.empty _, nenv),   L6.shrink_cps.shrink_top t)
    end.


(*
 Quote Recursively Definition vs := vs.main.  *)

(*
Quote Recursively Definition graph_color := (run G16).

Definition graph_color6 : cTerm certiL6.
  (let t:= eval vm_compute in (translateTo (cTerm certiL6) graph_color) in
       match t with
       | Ret ?xx => exact xx
       end).
Defined.
Definition graph_color7 := compile_L6 graph_color6.
*)

(*
Add LoadPath "../benchmarks".
Require Import vs.

Quote Recursively Definition vs := vs.main.
Definition vs6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) vs) in 
match t with
|Ret ?xx => exact xx
end).
Defined.
Definition vs6' := Eval vm_compute in (L6_translation vs6).


Print vs6.
Print vs6'.

Definition vs7 := compile_L6 vs6.
*)

(*
Quote Recursively Definition comp_fEnv := L6_to_Clight.compute_fEnv.
Definition comp_fEnv6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) comp_fEnv) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Definition comp_fEnv6' := Eval vm_compute in (L6_translation comp_fEnv6).
Print comp_fEnv6'.
Definition comp_fEnv7 := compile_L6 comp_fEnv6.




Quote Recursively Definition make_args := L6_to_Clight.compute_fEnv.
Definition comp_fEnv6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) comp_fEnv) in 
match t with
|Ret ?xx => exact xx
end).
Defined.


Definition comp_fEnv6' := Eval vm_compute in (L6_translation comp_fEnv6).
Print comp_fEnv6'.
Definition comp_fEnv7 := compile_L6 comp_fEnv6.
 *)

Require Import runtime.runtime.

(* Quote Recursively Definition binom := Binom.main.
 Definition binom5 := Eval native_compute in (translateTo (cTerm certiL5a) binom).*)


Definition printProg := fun prog file => L6_to_Clight.print_Clight_dest_names (snd prog) (M.elements (fst prog)) file.



(* Definition test := printProg (compile_L6 (ext_comp binom)) "output/binom.c".*)



(* Definition test := printProg p7 "output/threePlusFour.c".*)
(*Definition test := printProg blahProg7 "output/blah.c".*)
(*  *)
(*Definition test := printProg graph_color7 "output/color.c".*)


(*  Definition binom6 := Eval native_compute in (ctranslateTo certiL6 binom). *)
(* Definition test := printProg (compile_L6 (ext_comp binom)) "output/binom.c".*)



      

(*  Definition vs5 := Eval native_compute in (translateTo (cTerm certiL5a) vs). *)

(*


Set Printing Depth 1000.
Print vs5.

Definition vs3 := Eval native_compute in (translateTo (cTerm certiL3) vs).
*)



(*
Definition test := run_L6_exn (comp_L6 binom).
Eval native_compute in test.
 *)




Definition comp_L6 p := match p
                          with
                            | Exc s => Exc s
                            | Ret v =>  Ret (L5a_comp_L6 v)                                           
                        end.




Definition comp_to_L6:= fun p =>
                       comp_L6 (translateTo (cTerm certiL5a) p).
  









 


(* Multistep *)
Fixpoint mstep_L6  (x : (cTerm certiL6)) (n:nat) :=
  match n with
    | O =>
      Ret x
    | S n' =>
      let '((p,cenv, nenv), (rho, e)) := x in
      (match (L6.eval.sstep_f p cenv rho e) with
         | Ret (rho', e') => mstep_L6 ((p, cenv, nenv), (rho',e')) n'
         | Exc s => Exc ("Error :"++s++" at "++(nat2string10 n)++" from end")%string
       end)
  end.



(* this will be split into two function when I fix the type of values for L6 *)
Definition print_BigStepResult_L6 p  n:=
  let '((prim,cenv, nenv), (rho, e)) := p in
  L7.L6_to_Clight.print (
      match (L6_evaln n p) with
      | Error s _ => s
      | OutOfTime (_, (rho', e')) => "Out of time:"++ (show_env nenv cenv rho')++ (show_exp nenv cenv e')
      | Result v => show_val nenv cenv v
      end).





Definition print_step_L6 p  :=
  L7.L6_to_Clight.print (match p with
                           | exceptionMonad.Exc s =>  s
                           | exceptionMonad.Ret _ => match bind p (fun p => mstep_L6 p 30)  with
                                                                                    | Exc s => s
                                                                                    | Ret ((prim, cenv, nenv), (g', e')) => (show_cenv cenv)++(show_env nenv cenv g') ++ (show_exp nenv cenv e')
                                                                                                                                                                                         end
                        end).





Extraction Language Ocaml.
(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

Extract Constant L7.L6_to_Clight.print => "print_string".

Definition test := printProg (compile_L6 (ext_comp swap)) "output/swap.c".  

(* Definition test := print_step_L6 (comp_L6 vs5).

*)







