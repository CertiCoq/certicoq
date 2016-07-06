
Require Import SquiggleEq.export.
Require Import SquiggleEq.UsefulTypes.
Require Import L4.simpleCPSAA.
Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Set Implicit Arguments.

Require Import SquiggleEq.varImplZ.

Require Import cps.
Notation NVar := var.

(**********************)
(** * CPS expressions *)
(**********************)
Inductive cps : Type :=
| Halt_c : val_c -> cps
| Ret_c : val_c (* cont *) -> val_c (* result *) -> cps
| Call_c : NVar (* fn *) -> NVar (* cont *) -> NVar (* arg *) -> cps
| Match_c : val_c -> list  ((dcon * nat) * ((list NVar)* cps)) -> cps
| Proj_c : val_c (*arg *) -> nat -> val_c (*cont*) -> cps
with val_c : Type :=
| Var_c : NVar -> val_c
| KVar_c : NVar -> val_c
| Lam_c : NVar (* arg *) -> NVar (*cont *) -> cps -> val_c
| Cont_c : NVar (* cont *) -> cps -> val_c
| Con_c : dcon -> list val_c -> val_c
(** In Fix_c [(v1,c1); (v2,c2) ...],
    in ci, vi can occur, and refers to Fix_c [(v1,c1); (v2,c2) ...]
    See [simpleCPSAA.eval_Proj_c] for more details
    
    Unlike previously, when a lambda was implicit in a fix, the ci must now explicitly be a value.
    Currently, [simpleCPSAA.eval_Proj_e] only reduces if cis are lambdas.
    We may allow arbitrary values.
  *)
| Fix_c : list (NVar * val_c) -> val_c.

Section Notations.
Require Import ExtLib.Data.Monads.OptionMonad.

(*
Fixpoint interp  (c: cps) : CTerm :=
match c with
| Halt_c v => coterm CHalt [bterm [] (interpVal v)]
| Ret_c f a => coterm CRet [bterm [] (interpVal f) , bterm [] (interpVal a)]
| Call_c f k a => coterm CCall [bterm [] (vterm f) , bterm [] (vterm k) , bterm [] (vterm a)]
| Match_c discriminee brs => 
    coterm (CMatch (List.map (fun b => (fst (fst (fst b)), length (snd (fst b)))) brs))
                    ((bterm [] (interpVal discriminee))::(List.map (fun b=> bterm (snd (fst b)) (interp (snd b))) brs))
| Proj_c arg selector cont => coterm (CProj selector) [bterm [] (interpVal arg), bterm [] (interpVal cont)]
end
with interpVal (c: val_c) : CTerm :=
match c with
| Var_c v => vterm v
| _ => vterm nvarx
end.
*)

Notation CBTerm := (@terms.BTerm NVar CPSGenericTermSig).
Notation CTerm := (@terms.NTerm NVar CPSGenericTermSig).

Require Import ExtLib.Structures.Monads.

Import Monad.MonadNotation.
Open Scope monad_scope.


(* Move *)
Definition flatten {m} {A: Type} `{Monad m} (lm:list (m A)) : m (list A) :=
fold_left (fun l a => l <- l;; 
                      a <- a;; 
                      ret (a :: l))
          lm 
          (ret []).


(* Move *)
Definition getVar (t:CTerm) : option NVar :=
match t with
| vterm v => Some v
| _ => None
end.


Fixpoint translateCPS (c : CTerm) : option cps :=
match c with
 | terms.oterm CHalt [bterm [] h] => 
      r <- (translateVal h) ;; 
      ret (Halt_c r)
 | terms.oterm CRet [bterm [] f; bterm [] a] => 
      f <- translateVal f ;;
      a <- translateVal a ;;
      ret (Ret_c f a)
 | terms.oterm CCall [bterm [] fn; bterm [] cont; bterm [] arg] => 
 (** we know that the CPS translation only produces Call_c terms that are variables. see 
    [simpleCPSAA.cps_cvt] and [simpleCPSAA.cps_cvt_apply]. *)
      fn <- getVar fn ;;
      cont <- getVar cont ;;
      arg <- getVar arg ;;
      ret (Call_c fn cont arg)
 | terms.oterm (CMatch ls) ((bterm [] discriminee)::lbt) => 
      let l:= map (fun b: CBTerm => 
                          match b with
                          bterm vars nt => 
                            c <- translateCPS nt ;;
                            ret (vars, c)
                          end)
                  lbt in
      l <- flatten l;;
      discriminee <- translateVal discriminee ;;
      ret (Match_c discriminee (combine ls l))
 | terms.oterm (CProj n) [bterm [] arg, bterm [] cont] => 
      cont <- translateVal cont ;;
      arg <- translateVal arg ;;
      ret (Proj_c arg n cont)
 | _ => None
end
with translateVal (c:CTerm) : option val_c :=
match c with
 | vterm v => ret (if ((varClass v):bool (*== USERVAR*)) then  (Var_c v) else ((KVar_c v)))
 | terms.oterm CLambda [bterm [x; xk] b] =>
      b <- translateCPS b ;; 
      ret (Lam_c x xk b)
 | terms.oterm CKLambda [bterm [xk] b] =>
      b <- translateCPS b ;; 
      ret (Cont_c xk b)
 | terms.oterm  (CDCon dc _) lbt =>
      let l := map (fun b => match b with 
                         bterm _ nt => translateVal nt
                         end) lbt in
      l <- flatten l ;;
      ret (Con_c dc l)
 | terms.oterm (CFix _) lbt =>
      let l:= map (fun b: CBTerm => 
                          match b with
                          bterm vars nt => 
                            c <- translateVal nt ;;
                            ret (hd nvarx vars, c)
                          end)
                  lbt in
      l <- flatten l;;
      ret (Fix_c l)
 | _ => None
end.

(* Move *)
Definition isSome {A:Type} (sop : option A) : Prop  := 
match sop with
| Some s => True
| None => False
end.

Require Import SquiggleEq.tactics.
Require Import SquiggleEq.LibTactics.
Require Import SquiggleEq.list.

Local Opaque varClassP.

Lemma translateVal_val_outer : forall (t:CTerm),
  isSome (translateVal t)
  -> isSome (translateVal (val_outer t)).
Proof using.
  intros ? Hs.
  unfold val_outer.
  simpl. cases_ifn v; destruct (translateVal t); auto.
Qed.
  
Lemma translateVal_cps_cvt_val : forall (t:NTerm),
  is_valueb t = true
  -> isSome (translateVal (cps_cvt_val t))
  -> isSome (translateVal (cps_cvt t)).
Proof using.
  intros ? Heq.
  simpl. rewrite cps_val_outer by assumption.
  unfold cps_cvt_val. apply translateVal_val_outer.
Qed.

Lemma translateVal_cps_cvt_val2 : forall (t:NTerm),
(if (is_valueb t) 
      then (isSome (translateVal (cps_cvt_val t)))
      else (isSome (translateVal (cps_cvt t))))
-> isSome (translateVal (cps_cvt t)).
Proof using.
  intros ?.
  cases_if; auto.
  apply translateVal_cps_cvt_val.
  assumption.
Qed.


Ltac dimpn H :=
  match type of H with
  | ?T1 -> ?T2 => let name := fresh "hyp" in
                  assert (name : T1);[auto| specialize (H name)]
  end.

(* Move  *)
Lemma isSomeBindRet {A B:Type}: forall (v:option A) (f:A->B),
  isSome v 
  -> isSome (x <- v ;; (ret (f x))).
Proof using.
  intros ? ? His.
  simpl. destruct v; auto.
Qed.

Lemma isSomeFlatten {A} : forall (lo : list (option A)),
  (forall a, In a lo -> isSome a)
  -> isSome (flatten lo).
Proof using.
  unfold flatten. intros ? Hin.
  generalize (@nil A).
  induction lo; simpl in *; auto.
  dLin_hyp.
  destruct a; simpl in *; try tauto; auto.
Qed.

Local Opaque freshVars.
Local Opaque varClass.
Local Opaque freshVarsPos.
Local Opaque freshVarsPosAux.
Local Opaque varClass.
Local Opaque varClassP.
Local Opaque contVars.

(* delete *)
Lemma varClassContVar : varClass contVar = false.
Proof using.
  intros.
  unfold contVar.
  pose proof (freshCorrect 1 (Some false) [] []) as Hf.
  simpl in Hf. repnd.
  remember (freshVars 1 (Some false) [] []) as lv.
  dlist_len_name lv v. simpl.
  specialize (Hf _ eq_refl v). simpl in *. auto.
Qed.  


Lemma translateVal_cps_cvt_Some : forall (t:NTerm),
  nt_wf t
  -> if (is_valueb t) 
      then (isSome (translateVal (cps_cvt_val t))) 
      else (isSome (translateVal (cps_cvt t))).
Proof using.
  induction t as [x | o lbt Hind]  using NTerm_better_ind ; intros Hwf;
    [(* var *) simpl; tauto|].
  inverts Hwf as Hbt Hnb.
  destruct o; simpl in *; auto.
(* lambda *)
- dnumvbars  Hnb bt.
  simpl in *.
  unfold var, M.elt in *.
  rewrite @varClassContVar.
  apply isSomeBindRet. 
  apply isSomeBindRet.
  apply translateVal_cps_cvt_val2.
  dLin_hyp.
  apply Hyp0; auto. ntwfauto.

(* fix *)
- setoid_rewrite map_map. unfold compose.
  apply isSomeBindRet.
  apply isSomeFlatten.
  intros p Hin.
  apply in_map_iff in Hin. exrepnd.
  destruct a as [lv nt].
  subst.
  apply isSomeBindRet. simpl. apply translateVal_cps_cvt_val2.
  eapply Hind; eauto.
  ntwfauto.

(* constructor *)
- cases_if; rename H into Hb.
(* constructor : all values*)
  + apply isSomeBindRet.
    rewrite map_map. unfold compose.
    apply isSomeFlatten.
    intros p Hin.
    apply in_map_iff in Hin. exrepnd.
    destruct a as [lv nt].
    subst. simpl.
    rewrite ball_map_true in Hb.
    specialize (Hb _ Hin1). unfold compose in Hb. simpl in Hb.
    specialize (Hind _ _ Hin1). rewrite Hb in Hind.
    apply Hind; eauto with subset. ntwfauto.
(* constructor : not all values*)
  + 
    unfold var, M.elt in *.
    generalize  ((tl (contVars (S (Datatypes.length lbt))))) at 2.
    intros lkvv. simpl.
    pose proof (varsOfClassNil true) as Hvc.
    addContVarsSpec ((S (Datatypes.length lbt))) Hvc kv.
    apply isSomeBindRet. simpl.
    clear Heqlvcvf Hvcnr Hcvdis Hnb Hvc Hb.
    rename H0 into Hlen.
    revert Hlen. revert lvcvf.
    induction lbt; simpl; intros; auto;[|].
    * rewrite map_map. unfold compose.
      clear. simpl. cases_if;
      apply isSomeBindRet;
      apply isSomeBindRet;
      rewrite map_map; unfold compose; simpl;
      apply isSomeFlatten;
      intros ? Hin; apply in_map_iff in Hin;
      exrepnd; subst;
      cases_if; simpl; auto.
    * simpl in *. dlist_len_name lvcvf lvc. 
      simpl.
      destruct a. simpl.
      dLin_hyp.
      dimpn Hyp0;[ntwfauto|]; clear hyp.
      apply translateVal_cps_cvt_val2 in Hyp0.
      unfold var, M.elt in *.
      destruct (translateVal (cps_cvt n)); auto.
      clear Hyp0.
      apply isSomeBindRet.
      apply isSomeBindRet.
      apply_clear IHlbt; auto.
  
(* apply *)
- dnumvbars  Hnb bt. simpl. ntwfauto.
  simpl in *. dLin_hyp. ntwfauto.
  dLin_hyp.
  (dimpn Hyp1; clear hyp).
  (dimpn Hyp2; clear hyp).
  apply translateVal_cps_cvt_val2 in Hyp1.
  apply translateVal_cps_cvt_val2 in Hyp2.
  destruct (translateVal (cps_cvt btnt)); auto.
  destruct (translateVal (cps_cvt btnt0)); auto.

(* proj *)
- dnumvbars  Hnb bt. simpl. ntwfauto.
  simpl in *. dLin_hyp. ntwfauto.
  apply isSomeBindRet.
  apply isSomeBindRet.
  dLin_hyp.
  apply Hyp0 in Hyp. clear Hyp0.
  apply translateVal_cps_cvt_val2. auto.

(* let *)
- dnumvbars  Hnb bt. simpl. ntwfauto.
  simpl in *. dLin_hyp. ntwfauto.
  dLin_hyp.
  (dimpn Hyp1; clear hyp).
  (dimpn Hyp2; clear hyp).
  apply translateVal_cps_cvt_val2 in Hyp1.
  apply translateVal_cps_cvt_val2 in Hyp2.
  apply isSomeBindRet.
  destruct (translateVal (cps_cvt btnt0)); auto.
  apply isSomeBindRet.
  apply isSomeBindRet.
  destruct (translateVal (cps_cvt btnt)); auto.

(* match *)
- dnumvbars  Hnb bt. simpl.
  apply isSomeBindRet.
  simpl in *. dLin_hyp. ntwfauto.
  apply Hyp0 in Hyp. clear Hyp0.
  apply translateVal_cps_cvt_val2 in Hyp.
  destruct (translateVal (cps_cvt btnt)); auto.
  apply isSomeBindRet.
  apply isSomeBindRet.
  apply isSomeBindRet.
  setoid_rewrite map_map. unfold compose.
  apply isSomeFlatten.
  intros ? Hin. apply in_map_iff in Hin.
  exrepnd. subst.
  destruct a0. simpl.
  apply isSomeBindRet.
  apply isSomeBindRet.
  apply translateVal_cps_cvt_val2.
  eapply Hind; eauto. ntwfauto.
Qed.

Require Import L4.expression.
Require Import L4.L4_to_L4a.

Definition L4_to_L5a (e:L4.expression.exp) : option val_c :=
  let l4a := L4.L4_to_L4a.L4_to_L4a e in
  let l5 := simpleCPSAA.cps_cvt l4a in
  translateVal l5.


End Notations.


Require Import L4.L3_to_L4.
Require Import Template.Template.
Require Import Template.Ast.

Section L1_to_L5a.
(* definitions from Greg's email dated July 5th 3:56PM EST *)

Let compile_L1_to_L4 := L3_to_L4.program_exp.
Require Import L4.L4_to_L4a.
Let compile_L1_to_L4a (e : Ast.program) :=
    match compile_L1_to_L4 e with
    | exceptionMonad.Exc s => exceptionMonad.Exc s
    | exceptionMonad.Ret e => exceptionMonad.Ret (L4.L4_to_L4a.translate nil e)
    end.

Let compile_L1_to_cps (e : Ast.program)  :=
    match compile_L1_to_L4a e with
    | exceptionMonad.Exc s => exceptionMonad.Exc s
    | exceptionMonad.Ret e => exceptionMonad.Ret (simpleCPSAA.cps_cvt e)
    end.


Definition compile_L1_to_L5a (e:Ast.program) : exception val_c:=
    match compile_L1_to_cps e with
    | exceptionMonad.Exc s => exceptionMonad.Exc s
    | exceptionMonad.Ret e =>
      match translateVal e with
      | None => exceptionMonad.Exc "error in L5a.translateVal"
      | Some e => exceptionMonad.Ret e
      end
    end.
End L1_to_L5a.

(*
Quote Recursively Definition p0L1 := 0.
Eval compute in compile_L1_to_L5a p0L1.
(*
     = Ret (Cont_c 5%positive (Ret_c (KVar_c 5%positive) (Con_c 0 [])))
     : exception val_c
*)
*)

  




