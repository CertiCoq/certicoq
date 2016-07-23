Add LoadPath "../common" as Common.
Add LoadPath "../L0_Quoted_Coq" as L0.

Require Export Template.Ast.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.

Require Import Common.RandyPrelude.
Require Import Common.AstCommon.
Require Import L0.term.

Open Scope list_scope.
Set Implicit Arguments.

(** Malecha's [program] is inside out **)
Definition cnstr_Cnstr (c: string * term * nat) : Cnstr :=
  mkCnstr (fst (fst c)) (snd c).

Definition ibody_ityp (iib:ident * inductive_body) : ityp :=
  let Ctors := map cnstr_Cnstr (ctors (snd iib))
  in mkItyp (fst iib) Ctors.

Definition ibodies_itypPack (ibs:list (ident * inductive_body)) : itypPack :=
  map ibody_ityp ibs.

(** note the backwards environ, a la template_coq **)
Fixpoint program_mypgm (p:program) (e:environ term) : AstCommon.Program term :=
  match p with
    | PIn t => {| main:= t; env:= e |}
    | PConstr nm t p => program_mypgm p (snoc e (nm ,ecTrm t))
    | PType nm npar ibs p => 
      let Ibs := ibodies_itypPack ibs
      in program_mypgm p (snoc e (nm, ecTyp term npar Ibs))
    | PAxiom nm ty p => program_mypgm p (snoc e (nm, ecAx term))
  end.

Lemma env_hom:
  forall p s ec e,
    env (program_mypgm p ((s, ec) :: e)) =
    (s, ec) :: (env (program_mypgm p e)).
Proof.
  induction p; intros; cbn; try rewrite IHp;try reflexivity.
Qed.

Lemma nil_hom:
  forall p, env (program_mypgm p nil) = nil -> exists (t:term), p = PIn t.
Proof.
  induction p; intros;
  try (cbn in H; unfold unit in H; rewrite env_hom in H; discriminate).
  - exists t. reflexivity.
Qed.

    
(** Check that a named datatype and constructor exist in the environment **)
Definition CrctCnstr (ipkg:itypPack) (inum cnum:nat) : Prop :=
  if (nth_ok inum ipkg defaultItyp)
  then (if nth_ok cnum (itypCnstrs (nth inum ipkg defaultItyp)) defaultCnstr
        then True else False)
  else False.

Notation prop := (tSort sProp).
Inductive Crct : nat -> environ term -> term -> Prop :=
| CrctSrt: forall n srt, Crct n nil (tSort srt)
| CrctWkTrmTrm: forall n p t s nm, Crct n p t -> Crct n p s ->
           fresh nm p -> Crct n ((nm,ecTrm s):::p) t
| CrctWkTrmTyp: forall n p t (s:itypPack) nm, Crct n p t -> CrctTyp n p s ->
           fresh nm p -> forall (m:nat), Crct n ((nm,ecTyp term m s):::p) t
| CrctRel: forall n m p, m < n -> Crct n p prop -> Crct n p (tRel m)
| CrctCast: forall n p t ck ty, Crct n p t -> Crct n p ty ->
                                Crct n p (tCast t ck ty)
| CrctProd: forall n p nm ty bod,
              Crct (S n) p bod -> Crct n p ty -> Crct n p (tProd nm ty bod)
| CrctLam: forall n p nm ty bod,
             Crct (S n) p bod -> Crct n p ty -> Crct n p (tLambda nm ty bod)
| CrctLetIn: forall n p nm dfn ty bod,
         Crct n p dfn -> Crct (S n) p bod -> Crct n p ty -> 
         Crct n p (tLetIn nm dfn ty bod)
              (***
| CrctApp: forall n p fn a args,
             ~ (isApp fn) -> Crct n p fn -> Crct n p a -> Crcts p args ->
             Crct n p (TApp fn a args)
***)
| CrctConst: forall n p pd nm,
               Crct n p prop -> LookupDfn nm (rev p) pd -> Crct n p (tConst nm)
| CrctConstruct: forall n p ipkgNm npars itypk inum cnum,
                   Crct n p prop -> LookupTyp ipkgNm (rev p) npars itypk ->
                   CrctCnstr itypk inum cnum ->
                   Crct n p (tConstruct (mkInd ipkgNm inum) cnum)
                        (****
| CrctCase: forall n p m ty mch brs,
              Crct n p mch -> Crcts p brs -> Crct n p ty -> 
              Crct n p (TCase m ty mch brs)
| CrctFix: forall n p ds m,
             Crct n p prop ->    (** convenient for IH *)
             CrctDs p (n + dlength ds) ds -> Crct n p (TFix ds m)
***)
| CrctInd: forall n p ind, Crct n p prop -> Crct n p (tInd ind)
with CrctTyp: nat -> environ term ->  itypPack -> Prop := 
| CrctTypStart: forall n itp, CrctTyp n nil itp
| CrctTypWk1: forall n p t s nm, CrctTyp n p t -> Crct n p s ->
           fresh nm p -> CrctTyp n ((nm,ecTrm s):::p) t
| CrctTypWk2: forall n p t s nm, CrctTyp n p t -> CrctTyp n p s ->
           fresh nm p -> forall m, CrctTyp n ((nm,ecTyp term m s):::p) t.
Hint Constructors Crct CrctTyp.
Scheme Crct_ind' := Minimality for Crct Sort Prop
  with CrctTyp_ind' := Minimality for CrctTyp Sort Prop.
Combined Scheme CrctCrctTyp_ind' from
         Crct_ind', CrctTyp_ind'.
