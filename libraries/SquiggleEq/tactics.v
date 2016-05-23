(*

  Copyright 2014 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import Coq.Lists.List.
Export List.ListNotations.
Require Import Coq.Program.Tactics.
(*Require Import SfLib.*)
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import Omega.
Require Import eq_rel.
Require Import universe.

(* unlike apply, this is not too eager and does not demand instantiations for all quantifier *)
Ltac apply' H1 H2 :=
  let H3 := fresh in
  (pose proof (H1 H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3) ||
  (pose proof (H1 _ _ _ _ _ _ _ _ _ _ H2) as H3; clear H2; pose proof H3 as H2; clear H3).


(** Taken from SfLib *)

Ltac unsimpl t :=
    let ts := eval simpl in t in
    change ts with t.
    
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Ltac repd :=
   repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
         end.

Ltac exrepd :=
   repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
           | [ H : exists v : _,_  |- _ ] =>
               let name := fresh v in
               destruct H as [name]
           | [ H : { v : _ | _ } |- _ ] =>
               let name := fresh v in
                 destruct H as [name]
           | [ H : { v : _ & _ } |- _ ] =>
               let name := fresh v in
                 destruct H as [name]
           | [ H : { v : _ | _ & _ } |- _ ] =>
               let name := fresh v in
                 destruct H as [name]
         end.

Ltac repnd :=
  repeat match goal with
           | [ H : _ /\ _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
           | [ H : prod _ _ |- _ ] =>
               let name := fresh H in destruct H as [name H]
         end.

Ltac repdors :=
  repeat match goal with
           | [ H : _ \/ _ |- _ ] =>
               let name := fresh H in destruct H as [name | H]
           | [ H : sum _ _ |- _ ] =>
               let name := fresh H in destruct H as [name | H]
         end.


(*
Notation "'texists' x , p" := (sigT (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'texists' x : t , p" := (sigT (fun x:t => p))
  (at level 200, x ident, right associativity,
    format "'[' 'texists' '/ ' x : t , '/ ' p ']'")
  : type_scope.

Notation "'texists('x : t ')' , p" := (sigT (fun x:t => p))
  (at level 200, x ident, right associativity) : type_scope.

Notation "'texists ('x : t ')' , p" := (sigT (fun x:t => p))
  (at level 200, x ident, right associativity) : type_scope.
*)

Tactic Notation "exintro" constr(c) :=
 apply existT with (x:=c).

Tactic Notation "eexintro" :=
 econstructor.

(*
    Lemma tr1 : texists n, n=1.
    Proof. exintro 1. reflexivity.
    Restart. eexintro. eauto.
    Qed.
*)

Ltac iffalse :=
  match goal with
    | [ H : False |- _ ] => destruct H
  end.

Ltac ifvoid :=
  match goal with
    | [ H : void |- _ ] => destruct H
  end.

Ltac provefalse := assert False; try iffalse.
Ltac provevoid := assert void; try ifvoid.

Tactic Notation "complete" tactic(tac) := tac; fail.
Tactic Notation "cauto" tactic(tac) := tac; auto; fail.

(** tries to prove a 'or' concl *)
Ltac cpltLR :=
  complete auto
  || complete (left; auto; cpltLR)
  || complete (right; auto; cpltLR).

Require Import universe.
Ltac sp_step :=
  match goal with
    (* true conclusion *)
    | [ H : ?P |- ?P ] => exact H
    | [ |- True ] => constructor
    | [ |- ?x <-> ?x ] => complete (split; auto)
    | [ |- ?x <=> ?x ] => complete (split; auto)
    | [ |- ?x <=> ?y ] => complete (split; auto)
    | [ |- (?x <=> ?y) <=> ((?x -> ?y) # (?y -> ?x))] => complete (apply tiff_is_prod_implies1)
    | [ |- ((?x -> ?y) # (?y -> ?x)) <=> (?x <=> ?y)] => complete (apply tiff_is_prod_implies2)
    | [ H : ?x = ?y |- ?y = ?x ] => symmetry; assumption
    | [ H1 : ?x = ?y, H2 : ?x = ?z |- ?y = ?z] => rewrite <- H1; assumption

    (* false hypotheses *)
    | [ H : False |- _ ] => destruct H
    | [ H : void |- _ ] => destruct H
    | [ H : true = false |- _ ] => inversion H
    | [ H : false = true |- _ ] => inversion H
    | [ H : Some _ = None |- _ ] => inversion H
    | [ H : None = Some _ |- _ ] => inversion H
    | [ H : [] = _ :: _ |- _ ] => inversion H (* 0/1+ *)
    | [ H : _ :: _ = [] |- _ ] => inversion H (* 1+/0 *)
    | [ H : [_] = _ :: _ :: _ |- _ ] => inversion H (* 1/2+ *)
    | [ H : _ :: _ :: _ = [_] |- _ ] => inversion H (* 2+/1 *)
    | [ H : [_] = _ :: _ :: _ :: _ |- _ ] => inversion H (* 1/3+ *)
    | [ H : _ :: _ :: _ :: _ = [_] |- _ ] => inversion H (* 3+/1 *)
    | [ H : [_;_] = _ :: _ :: _ :: _ |- _ ] => inversion H (* 2/3+ *)
    | [ H : _ :: _ :: _ :: _ = [_;_] |- _ ] => inversion H (* 3+/2 *)
    | [ H : 0 = S _ |- _ ] => inversion H
    | [ H : S _ = 0 |- _ ] => inversion H
    | [ H : ?n < 0 |- _ ] => inversion H || omega
    | [ H : ?x <> ?x |- _ ] => provefalse; apply H; symmetry
    | [ H : not (?x = ?x) |- _ ] => provefalse; apply H; symmetry
    | [ H : notT (?x = ?x) |- _ ] => provefalse; apply H; symmetry
    | [ H1 : not (?x = ?y), H2 : ?y = ?x |- _ ] => provefalse; apply H1; symmetry; assumption
    | [ H1 : notT (?x = ?y), H2 : ?y = ?x |- _ ] => provefalse; apply H1; symmetry; assumption

    (* some simple reasoning on the conclusion *)
    | [ |- _ -> _ ] => intro
    | [ |- ~ _ ] => intro
    | [ |- not _ ] => intro
    | [ |- notT _ ] => intro
    | [ |- _ /\ _ ] => constructor (* not always a good thing to do *)
    | [ |- prod _ _ ] => constructor (* not always a good thing to do *)

    (* some simple reasoning on the hypotheses *)
    | [ H1 : context[not _], H2 : _ |- _ ] => apply H1 in H2; iffalse
    | [ H1 : context[notT _], H2 : _ |- _ ] => apply H1 in H2; iffalse
    | [ H : _ /\ _ |- _ ] => let name := fresh H in destruct H as [name H]
    | [ H : exists (v : _),_  |- _ ] => let name := fresh v in destruct H as [name]
    | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
    | [ H1 : ~ ?P, H2 : ?P |- _ ] => specialize (H1 H2)
    | [ H1 : (?P [+] ?R) -> ?Q, H2 : ?P |- _ ] => specialize (H1 (inl H2))
    | [ H1 : (?R [+] ?P) -> ?Q, H2 : ?P |- _ ] => specialize (H1 (inr H2))
    | [ H : ((?P = ?P) [+] _) -> ?Q |- _ ] => specialize (H (inl eq_refl))
    | [ H : (_ [+] (?P = ?P)) -> ?Q |- _ ] => specialize (H (inr eq_refl))
    | [ H : { v : _ | _ } |- _ ] => let name := fresh v in destruct H as [name]
    | [ H : { v : _ & _ } |- _ ] =>  let name := fresh v in destruct H as [name]
    | [ H : { v : _ | _ & _ } |- _ ] => let name := fresh v in destruct H as [name]
    | [ H : prod _ _ |- _ ] => let name := fresh H in destruct H as [name H]
    | [ H : _ \/ _ |- _ ] => destruct H (* not always a good thing to do *)
    | [ H : sum _ _ |- _ ] => destruct H (* not always a good thing to do *)
    | [ H : sumbool _ _ |- _ ] => destruct H (* not always a good thing to do *)
  end.

Ltac sp :=
   repeat sp_step;
   try assumption;
   try reflexivity;
   try cpltLR.

Ltac allsimpl :=
   repeat match goal with
          | [ H : _ |- _ ] => progress (simpl in H)
          | [ |- _ ] => progress simpl
          end.

Ltac simphyps :=
   repeat match goal with
          | [ H : _ |- _ ] => progress (simpl in H)
          end.

Ltac applyall tac :=
  repeat match goal with
             | [ H : _ |- _] => apply tac in H
         end.

Ltac allunfold op :=
   repeat match goal with
          | [ H : _ |- _ ] => progress (unfold op in H)
          | [ |- _ ] => progress (unfold op)
          end.

Ltac allfold op :=
   repeat match goal with
          | [ H : _ |- _ ] => progress (fold op in H)
          | [ |- _ ] => progress (fold op)
          end.

Ltac allunfolds ops :=
  match ops with
    | [] => auto
    | ?op :: ?ops => (allunfold op; allunfolds ops)
  end.

Ltac allrewrite op :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (rewrite op in H || rewrite op)
          end.

Ltac alltrewrite op :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (trw_h op  H || trw op)
          end.

Ltac alltrewrite_rev op :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (trw_rev_h op  H || trw_rev op)
          end.

Ltac dands :=
  repeat match goal with
           | [ |- _ /\ _ ] => split
           | [ |- prod _ _ ] => split
         end.

Ltac thin H := clear H.

Ltac thin_trivials :=
  repeat match goal with
           | [ H : ?T = ?T |- _ ] => clear H
           | [ H : ?T <-> ?T |- _ ] => clear H
           | [ H : ?T <=> ?T |- _ ] => clear H
           | [ H : ?T -> ?T |- _ ] => clear H
           | [ H1 : ?T, H2 : ?T |- _ ] => clear H2
           | [ H : True |- _ ] => clear H
           | [ H : ~ False |- _ ] => clear H
           | [ H : ! False |- _ ] => clear H
         end.

Ltac GC := thin_trivials.

Ltac parallel x h :=
  match goal with
  | [ H : exists _ : ?P, _ |- exists _ : ?P, _] =>
       (destruct H as [x h]; exists x)
  | [ H : {_ : ?P & _} |- {_ : ?P & _} ] =>
       (destruct H as [x h]; exists x)
  end.

Ltac pnot H :=
  match goal with
    | [ H : ~ ?P |- ~ ?Q ] =>
        (intro q; apply H)
  end.

(*
Ltac lexists l :=
  match l with
  | nil => try (auto ;fail)
  | ?t :: ?ts => (exists t ; lexists ts)
  end.
*)

Lemma iff_symm : forall a b, (a <-> b) <-> (b <-> a).
Proof.
  repeat (sp; split; sp); destruct H; auto.
Qed.

Lemma prod_sym : forall a b, a # b -> b # a.
Proof.
  sp.
Qed.

Lemma sum_sym : forall a b, a [+] b -> b [+] a.
Proof.
  sp.
Qed.

Ltac symm :=
  match goal with
    | [ |- ?a <-> ?b ] => rewrite iff_symm
    | [ |- ?a <=> ?b ] => apply t_iff_sym
    | [ |- ?a # ?b ] => apply prod_sym
    | [ |- ?a [+] ?b ] => apply sum_sym
  end.

Tactic Notation "inv_sub_clear" ident (h) :=
  inversion h; subst; clear h.

 Require Import LibTactics. 

Ltac clear_eq x y :=
  match goal with
    | [ H : x = y |- _ ] => clear H
  end.

Tactic Notation "duplicate" ident(H) "as" simple_intropattern(newname) :=
  let name := fresh newname
  in remember H as name;
  clear_eq name H.

Tactic Notation "duplicate" ident(H) :=
  let name := fresh H
  in remember H as name;
  clear_eq name H.

Tactic Notation "applydup" constr(l) "in" ident(H) :=
  let newH := fresh H in
    remember H as newH; clear_eq newH H; apply l in newH.

Tactic Notation "applydup" constr(l) "in" ident(H) "as" simple_intropattern(newname):=
    remember H as newname; clear_eq newname H; apply l in newname.

Tactic Notation "dup" ident(H) "as" simple_intropattern(newname) :=
       let T := type of H in
         assert T as newname by trivial.

Ltac apply_in_hyp name :=
  match goal with
    | [ H1 : context[ _ -> _], H2 : _  |- _ ] =>
      remember H2 as name;
        clear_eq name H2;
        apply H1 in name
  end.

Ltac apply_hyp :=
  match goal with
    | [ H : context[ _ -> _] |- _ ] =>
      apply H
  end.

Ltac use_iff_l :=
  match goal with
    | [ H : _ <=> _  |- _ ] => apply (tiff_fst H)
  end.

Ltac use_iff_r :=
  match goal with
    | [ H : _ <=> _  |- _ ] => apply (tiff_snd H)
  end.

Ltac use_iff_l_in_hyp :=
  match goal with
    | [ H1 : _ <=> _ , H2 : _ |- _ ] => apply (tiff_fst H1) in H2
  end.

Ltac use_iff_r_in_hyp :=
  match goal with
    | [ H1 : _ <=> _ , H2 : _ |- _ ] => apply (tiff_snd H1) in H2
  end.


(*
Ltac duplicateas H newname :=
  let name := fresh newname
  in remember H as name;
  clears_last.

Ltac duplicate H := duplicateas H H.
*)

Ltac exrepnd :=
   repeat match goal with
           | [ H : _ /\ _ |- _ ] => let name := fresh H in destruct H as [name H]
           | [ H : prod _ _ |- _ ] => let name := fresh H in destruct H as [name H]
           | [ H : exists (v : _),_  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
           | [ H : { v : _ | _ }  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
           | [ H : { v : _ & _ }  |- _ ] =>
               let vname := fresh v in
               let hname := fresh H in
               destruct H as [vname hname]
         end.

Tactic Notation "instlemma" constr(l) "as" simple_intropattern(I)  :=
 remember l as I; clears_last.

Ltac dimp H :=
  match type of H with
    | ?T1 -> ?T2 =>
      let name := fresh "hyp" in
      assert T1 as name; auto; try (apply H in name)
  end.

Ltac d_imp H :=
  match type of H with
    | ?T1 -> ?T2 =>
      let name := fresh "hyp" in
      assert T1 as name;
      auto;
      try (assert T2 by (complete auto); clear name)
  end. (* ; try (apply H in name)*)

Ltac dest_imp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete sp)
        | try (let concl := fresh "hyp" in
                 assert T2 as concl by (complete auto);
               clear hyp;
               clear H;
               rename concl into H)
          ; try (complete sp)
        ]
  end.

Ltac destimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete sp)
        | try (let concl := fresh "hyp" in
                 assert T2 as concl by (complete auto);
               clear hyp;
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.

Ltac autodimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete auto)
        | try (let concl := fresh "hyp" in
                 pose proof (H hyp) as concl;
               clear hyp;
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.

(*
Ltac autodimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete auto)
        | try (let concl := fresh "hyp" in
                 assert T2 as concl by (complete auto);
               clear hyp;
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.
*)

Tactic Notation "sp_iff"  ident(c) :=
  split;
  [ Case_aux c "->"
  | Case_aux c "<-"
  ].

Tactic Notation "split_iff"  ident(c) :=
  split;
  [ Case_aux c "->"
  | Case_aux c "<-"
  ].

Tactic Notation "split_ciff"  ident(c) :=
  split; split;
  [ Case_aux c "->"
  | Case_aux c "<-"
  ].

Tactic Notation "op_cases" ident(H) ident(c) :=
       destruct H;
  [ Case_aux c "some"
  | Case_aux c "none"
  ].

Ltac allapply op :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (apply op in H )
          end.
Tactic Notation "apply_clear" ident(L) "in" ident(H) :=
  apply L in H; clear L.


Tactic Notation "apply_clear" ident(L) :=
  apply L; clear L.

Tactic Notation "applydup_clear" ident(L) "in" ident(H) :=
 let newH := fresh H in remember H as newH; clears_last;
 apply L in newH; clear L.

Tactic Notation "repnud" ident(H) :=
 unfolds_in_base H; repnd.

Tactic Notation "exrepnud" ident(H) :=
 unfolds_in_base H; exrepnd.

Tactic Notation "invertsn" ident(H):=
 inverts H as H.

Tactic Notation "spauto":=
 repeat (auto;split;auto).

Ltac rewrite_term t i :=
  match goal with
      [ H : t = _ |- _ ] => rewrite H in i
    | [ H : _ = t |- _ ] => rewrite <- H in i
  end.

Ltac rterm t :=
  match goal with
      [ H : t = _ |- _ ] => rewrite H
    | [ H : _ = t |- _ ] => rewrite <- H
  end.

Tactic Notation "dorn" ident(H):= destruct H as [H | H].

Tactic Notation "destructr" constr(ob) "as" simple_intropattern(names) :=
 let eqname:=  fresh "Hdeq"  in
  remember ob as eqname; destruct eqname as names.

Tactic Notation "ddestructr" constr(ob) "as" simple_intropattern(names) :=
 let eqname:=  fresh "Hdeq"  in
  remember ob as eqname; destruct eqname as names.

Tactic Notation "destructrn" constr(ob) "as" simple_intropattern(names) simple_intropattern(eq):=
  remember ob as eq; destruct eq as names.

Ltac intron name :=
  let newn:= fresh name in 
    introv newn.

(**intro with names like name1 name2 name3 ....*)
Ltac introns name :=
  repeat(
  let newn:= fresh name in 
    introv newn).

Ltac invertsna hyp  names :=
  inverts hyp as; introns names.

Ltac revert_all :=
repeat(
  let H:= get_last_hyp tt in
  revert H).

Ltac fail_if_not_number n :=
  match n with
  | S ?m => fail_if_not_number m
  | 0 => idtac
end.

Tactic Notation "applysym" constr(L) "in" ident(H):=
  ( (apply L in H) ||  (symmetry in H;apply L in H)).

Ltac try_sym H T:=
  ( (T) ||  (symmetry in H;T)).


Ltac rewrite_once op :=
   match goal with
           | [ H : _ |- _ ] => (rewrite op in H || rewrite op)
          end.

Ltac dpair_eq :=
   match goal with
           | [ H : (_,_)=(_,_) |- _ ] =>
              let Hl := fresh H "l" in
              let Hr := fresh H "r" in
               inverts H as Hl Hr
          end.

Tactic Notation "spc" := sp; try (congruence).

Ltac rename_last Hn :=
  let H := get_last_hyp  tt in
  rename H into Hn.

Ltac cases_ifn Hn :=
  cases_if; clears_last; rename_last Hn.

Lemma hide_hyp :
  forall (P : [univ]),
    P <=> (P # True).
Proof. split; sp.
Qed.

Ltac cases_ifd Hn :=
  match goal with
      [ |- context[if ?d then ?tt else ?ff] ]
      => let Hnt := fresh Hn "t" in
         let Hnf := fresh Hn "f" in
         destruct d as [Hnt | Hnf] end.

Ltac apply_eq f H Hn :=
match goal with
[ H: (?l = ?r) |- _] => assert (f l = f r) as Hn by (f_equal;sp)
end.

Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

Ltac clear_ors :=
  repeat match goal with
           | [ H : _ [+] _ |- _ ] => clear H
         end.

Ltac gen_some x :=
  match goal with
    | [ H : forall v : _, _ |- _ ] => generalize (H x); intro
  end.

Ltac no_duplicate h :=
  let T := type of h in
  match goal with
    | [ H1 : T, H2 : T |- _ ] => fail 1
    | [ H1 : ?B, H2 : ?A |- _ ] => (unify B A;fail 1) (** sometimes rewrite creates evars*)
    | _ => idtac
  end.

Ltac discover_step :=
  match goal with
    | [ H : context[?a <=> ?b] |- _ ] =>
      first [ assert a as name by (complete sp);
              rw H in name;
              no_duplicate name
            | assert b as name by (complete sp);
              rw <- H in name;
              no_duplicate name
            ]

    | [ H : context[?a -> _] |- _ ] =>
      let name := fresh "h" in
      assert a as name by (complete sp);
        apply H in name;
        no_duplicate name

    | [ H : context[_ -> _], H2 : ?c |- _ ] =>
      let name := fresh "h" in
      assert c as name by auto;
        apply H in name;
        no_duplicate name

    | [ H : context[_ <=> _], H2 : ?c |- _ ] =>
      let name := fresh "h" in
      assert c as name by auto;
        rw H in name;
        no_duplicate name

    | [ H : context[_ <=> _], H2 : ?c |- _ ] =>
      let name := fresh "h" in
      assert c as name by auto;
        rw <- H in name;
        no_duplicate name
  end.

Ltac discover := repeat discover_step.

Ltac allapplydup op :=
  repeat match goal with
           | [ H : ?T |- _ ] =>
             let h := fresh "h" in
             assert T as h by auto;
               apply op in h;
               no_duplicate h
          end.

Ltac invs :=
  match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; GC
  end.

Tactic Notation "apph" tactic(tac) :=
  match goal with
    | [ H : context[ _ -> _] |- _ ] => apply H; tac
  end.

Ltac make_and H1 H2 :=
  let Ha := fresh H1 H2 in
  pose proof (H1, H2) as Ha; clear H1; clear H2.

(** From LibTactics.v ... ,move to tactics.v*)
Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" := 
  (@ltac_something _ _).

Lemma ltac_something_eq : forall (e:Type),
  e = (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_hide : forall (e:Type),
  e -> (@ltac_something _ e).
Proof. auto. Qed.

Lemma ltac_something_show : forall (e:Type),
  (@ltac_something _ e) -> e.
Proof. auto. Qed.

Ltac show_hyp H :=
  apply ltac_something_show in H.

Ltac hide_hyp H :=
  apply ltac_something_hide in H.


Ltac show_hyps :=
  repeat match goal with
    H: @ltac_something _ _ |- _ => show_hyp H end.

Ltac dlt Hyp :=
match type of Hyp with
| 0 < _ => fail 1
| S _ < S _ => apply lt_S_n in Hyp
| ?n < S _ => destruct n
end.

Ltac GClte :=
match goal with
[ H : ?n < ?m |- _ ] => fail_if_not_number n; fail_if_not_number m; clear H
|[ H : ?n <= ?m |- _ ] => fail_if_not_number n; fail_if_not_number m; clear H
end.

Ltac clear_dependents x :=
  repeat match goal with
             [ H : context[x] |- _ ] => clear H
         end.

Ltac revert_dependents x :=
  repeat match goal with
             [ H : context[x] |- _ ] => revert H
         end;
  revert x.
Ltac dtiffs2 := repeat match goal with
[ H: forall _ : ?X, _ <=> _ |- _] => 
    let Hl:= fresh H "tl" in
    let Hr:= fresh H "tr" in
    pose proof (fun x:X => tiff_fst (H x)) as Hl;
    pose proof (fun x:X => tiff_snd (H x)) as Hr; hide_hyp H
| [ H: forall (_ : ?X) (_ : ?Y), _ <=> _ |- _] => 
    let Hl:= fresh H "tl" in
    let Hr:= fresh H "tr" in
    pose proof (fun x:X => (fun y:Y => tiff_fst (H x y))) as Hl;
    pose proof (fun x:X => (fun y:Y => tiff_snd (H x y))) as Hr; hide_hyp H
end; show_hyps.


Ltac prove_iff h :=
  let T := type of h in
  match goal with
    | [ |- ?c ] =>
        let e := fresh "e" in
          assert (T <=> c) as e; try (complete (rw <- e; auto))
  end.

Ltac rep_eexists :=
repeat match goal with 
  [ |-  sigT _  ] =>  eexists
  end.

Ltac move_term_to_top t :=
  match reverse goal with
    | H1 : t, H2 : _ |- _ =>
        let h := fresh "h" in
          rename H1 into h;
        assert t as H1 by trivial;
        clear h
  end.
Ltac notNil lv :=
match lv with
| [] => fail 1
| _ => idtac
end.

