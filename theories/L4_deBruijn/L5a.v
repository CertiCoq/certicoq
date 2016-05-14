
Require Import SquiggleLazyEq.export.
Require Import SquiggleLazyEq.UsefulTypes.
Require Import L4.simpleCPSAA.
Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
  Coq.Program.Program Coq.micromega.Psatz.

Set Implicit Arguments.
Section VarsOf2Class.

(* see the file SquiggleLazyEq.varImplPeano for an instantiation of NVar *)
Context {NVar} {deqnvar : Deq NVar} {vartype: @VarType NVar bool (* 2 species of vars*) _}.


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
  *)
| Fix_c : list (NVar * cps) -> val_c.

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
 | vterm v => if ((varClass v):bool (*== USERVAR*)) then ret (Var_c v) else (ret (KVar_c v))
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
                            c <- translateCPS nt ;;
                            ret (hd nvarx vars, c)
                          end)
                  lbt in
      l <- flatten l;;
      ret (Fix_c l)
 | _ => None
end.
End VarsOf2Class.
