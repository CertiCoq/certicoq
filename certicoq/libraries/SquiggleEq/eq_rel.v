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


Require Import universe.


Inductive void : [univ] := .


(* ========= Here is a constuctive iff ======== *)

(*Definition t_iff A B := (A -> B) # (B -> A).*)

Inductive t_iff (A B : [univ]) : [univ] :=
 | t_iff_cons : (A -> B) -> (B -> A) -> t_iff A B.

Notation "x <=> y" := (iff x y) (at level 95, no associativity).

Lemma tiff_trans :
  forall a b c, (a <=> b) -> (b <=> c) -> (a <=> c).
Proof.
  intros a b c i1 i2.
  destruct i1 as [i11 i12].
  destruct i2 as [i21 i22].
  split; intro k.
  apply i11 in k; apply i21 in k; auto.
  apply i22 in k; apply i12 in k; auto.
Qed.

Ltac dtiff :=
  match goal with
      [ H : ?x <=> ?y |- _ ] => destruct H
  end.

Ltac dtiffs := repeat dtiff.

Ltac dprod :=
  match goal with
      [ H : ?x # ?y |- _ ] => destruct H
  end.

Ltac dprods := repeat dprod.

Ltac dsum :=
  match goal with
      [ H : ?x [+] ?y |- _ ] => destruct H
  end.

Ltac dsums := repeat dsums.

Ltac dall :=
  repeat match goal with
           | [ H : ?x <=> ?y |- _ ] => destruct H
           | [ H : ?x # ?y   |- _ ] => destruct H
           | [ H : ?x [+] ?y |- _ ] => destruct H
         end.

Definition tiff_fst :=
  fun {A B : [univ]} (p : A <=> B) => let (x, _) := p in x.

Definition tiff_snd :=
  fun {A B : [univ]} (p : A <=> B) => let (_, y) := p in y.

Lemma tiff_is_prod_implies1 :
  forall A B,
    (A <=> B) <=> ((A -> B) # (B -> A)).
Proof.
  intros; split; intros k; split; intros; destruct k; auto.
Qed.

Lemma tiff_is_prod_implies2 :
  forall A B : [univ],
    ((A -> B) # (B -> A)) <=> (A <=> B).
Proof.
  intros; split; intros k; split; intros; destruct k; auto.
Qed.

Lemma combine_t_iff_proofs_imp :
  forall {A B A' B' : [univ]},
    (A <=> A') -> (B <=> B') -> ((A -> B) <=> (A' -> B')).
Proof.
  intros; dall; constructor; auto.
Qed.

Lemma combine_t_iff_proofs_t_iff :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A <=> B) <=> (A' <=> B')).
Proof.
  intros.
  dall; constructor; intro; dall; constructor; auto.
Qed.

Lemma combine_t_iff_proofs_prod :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A # B) <=> (A' # B')).
Proof.
  intros.
  dall; constructor; intro; dall; auto.
Qed.

Lemma combine_t_iff_proofs_sum :
  forall {A B A' B'},
    (A <=> A')
    -> (B <=> B')
    -> ((A [+] B) <=> (A' [+] B')).
Proof.
  intros.
  dall; constructor; intro; dall; auto.
Qed.

Lemma combine_t_iff_proofs_not :
  forall {A A'},
    (A <=> A')
    -> (!A <=> !A').
Proof.
  intros.
  dall; constructor; repeat intro; auto.
Qed.

Lemma t_iff_refl :
  forall A, A <=> A.
Proof.
  intros; constructor; auto.
Qed.

Lemma t_iff_sym :
  forall {A B}, (A <=> B) -> (B <=> A).
Proof.
  intros.
  dall; constructor; auto.
Qed.

(* this build a proof object of T <=> T[b/a] where p is the proof of a<=>b.
*)
Ltac build_tiff_term T a b p :=
  match T with
    | a => p
    | ?x -> ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_imp l r)
    | ?x <=> ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_t_iff l r)
    | ?x # ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_prod l r)
    | ?x [+] ?y =>
      let l := build_tiff_term x a b p in
      let r := build_tiff_term y a b p in
      constr:(combine_t_iff_proofs_sum l r)
    | !?x =>
      let l := build_tiff_term x a b p in
      constr:(combine_t_iff_proofs_not l)
    | _ => constr:(t_iff_refl T)
  end.

Tactic Notation "thin_last" :=
  match goal with H: ?T |- _ => clear H end.

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

Ltac build_and_rewrite H :=
  let T := type of H in
  match goal with
    | [ |- ?C ] =>
      match T with
        | ?A <=> ?B =>
          let d := build_tiff_term C A B H in
          let name := fresh H in
          remember d as name;
            thin_last;
            apply  name;
            clear name
      end
  end.

Ltac build_and_rewrite_hyp H H2 :=
  let T := type of H in
  let C := type of H2 in
  match T with
    | ?A <=> ?B =>
      let d := build_tiff_term C A B H in
      let name := fresh H in
      remember d as name;
        thin_last;
        apply' (tiff_fst name) H2;
        clear name
  end.

Ltac build_and_rewrite_rev H :=
  let T := type of H in
  match goal with
    | [ |- ?C ] =>
      match T with
        | ?A <=> ?B =>
          let d := build_tiff_term C B A (t_iff_sym H) in
          let name := fresh H in
          remember d as name;
            thin_last;
            apply name;
            clear name
      end
  end.

Ltac build_and_rewrite_hyp_rev H H2 :=
  let T := type of H in
  let C := type of H2 in
  match T with
    | ?A <=> ?B =>
      let d := build_tiff_term C B A (t_iff_sym H) in
      let name := fresh H in
      remember d as name;
        thin_last;
        apply' (tiff_fst name)  H2;
        clear name
  end.

Tactic Notation "trewrite" ident(H) :=
       build_and_rewrite H.


Tactic Notation "trewrite" ident(H) "in" ident (H') :=
       build_and_rewrite_hyp H H'.


Tactic Notation "trewrite" "<-" ident(H) :=
       build_and_rewrite_rev H.


Tactic Notation "trewrite" "<-" ident(H) "in" ident(H') :=
       build_and_rewrite_hyp_rev H H'.




Ltac get_instance_of  T  H Hn :=
  match H with
    | _ =>
     let name:= fresh "Htemp" in 
      (* idtac "trying gio" H;*)
     progress (
        (pose proof (fun h:H => (tiff_fst T) h) as name)||
        (pose proof (fun h:H => (tiff_fst (T _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_fst (T _ _ _ _ _ _ _ _)) h) as name) 
      ); (* idtac "succeded" H; *)
     let H2 := type of name in
         match H2 with
           | ?H -> ?H => fail 1 (* both sides are the same, we won't rewrite anything *)
           | ?H -> ?H2 =>
             clear name;
               assert (H <=> H2) as Hn by (apply T)
         (*; idtac "really succeded" H *)
         end

    | ?Hl <=> ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | ?Hl # ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | ?Hl [+] ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
    | !?Hl => get_instance_of T Hl Hn
    | ?Hl -> ?Hr => get_instance_of T Hl Hn || get_instance_of T Hr Hn
  end.

Ltac get_instance_of_rev  T  H Hn :=
  match H with
    | _ =>
     let name:= fresh "Htemp" in 
      (* idtac "trying gio" H;*)
     progress (
        (pose proof (fun h:H => (tiff_snd T) h) as name)||
        (pose proof (fun h:H => (tiff_snd (T _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _ _ _ _ _)) h) as name) ||
        (pose proof (fun h:H => (tiff_snd (T _ _ _ _ _ _ _ _)) h) as name) 
      ); (* idtac "succeded" H;*)
     let H2 := type of name in
         match H2 with
           | ?H -> ?H => fail 1 (* both sides are the same, we won't rewrite anything *)
           | ?H -> ?H2 =>
             clear name;
               assert (H2 <=> H) as Hn by (apply T)
         (** H2 in LHS; apply does not automatically take care
                    of symmetry *)
         (*; idtac "really succeded" H*)
         end

    | ?Hl <=> ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | ?Hl # ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | ?Hl [+] ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
    | !?Hl => get_instance_of_rev T Hl Hn
    | ?Hl -> ?Hr => get_instance_of_rev T Hl Hn || get_instance_of_rev T Hr Hn
  end.

(** rewrite using a universally quantified t_iff relation T  in the conclusion *)
Ltac trw T :=
  match goal with
      [  |- ?C ] =>
      let name:= fresh "Hget_instance_of_in_concl" in
      get_instance_of T C name; 
        build_and_rewrite name; clear name
  end.

Ltac trw_rev  T :=
  match goal with
      [  |- ?C ] =>
      let name:= fresh "Hget_instance_of_in_concl" in
      get_instance_of_rev T C name;
        build_and_rewrite_rev name ; clear name
  end.


Ltac trw_h T h :=
  let C := type of h in
  let name:= fresh "Hget_instance_of_in_concl" in
  get_instance_of T C name;  
    build_and_rewrite_hyp name h; clear name.


Ltac trw_rev_h T h :=
  let C := type of h in
  let name:= fresh "Hget_instance_of_in_concl" in
  get_instance_of_rev T C name;
    build_and_rewrite_hyp_rev name h; clear name.



(* Some general notation to use the above tactics *)

Tactic Notation "rw" constr(T) :=
  trw T || rewrite T.
Tactic Notation "rw" "<-" constr(T) :=
  trw_rev T || rewrite <- T.
Tactic Notation "rw" constr(T) "in" ident(H) :=
  trw_h T H || rewrite T in H.
Tactic Notation "rw" "<-" constr(T) "in" ident(H) :=
  trw_rev_h T H || rewrite <- T in H.

Tactic Notation "onerw" :=
       match goal with
         | [ H : _ |- _ ] => progress (trw H || rewrite H)
       end.

Tactic Notation "allrw" := repeat onerw.

Tactic Notation "allrw" "<-" :=
  repeat match goal with
           | [ H : _ |- _ ] => progress (trw_rev H || rewrite <- H)
          end.

(*
Tactic Notation "onerw" constr(T) :=
       match goal with
         | [ H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
       end.

Tactic Notation "allrw" constr(T) := repeat (onerw T).
*)

Tactic Notation "onerw" constr(T) :=
       let t := type of T in
       match goal with
         | [ H : _, H' : t |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
         | [ H : t |- _ ] => fail 1
         | [ H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
       end.

Tactic Notation "allrw" constr(T) := repeat (onerw T).

Tactic Notation "rww" ident(T) :=
  let t := type of T in
  repeat match goal with
           | [ H1 : t, H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
         end.

Tactic Notation "allrw" "<-" constr(T) :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (trw_rev_h T H || trw_rev T || rewrite <- T in H || rewrite <- T)
         end.

Tactic Notation "rww" "<-" ident(T) :=
  let t := type of T in
  repeat match goal with
           | [ H1 : t, H : _ |- _ ] =>
             progress (trw_rev_h T H || trw_rev T || rewrite <- T in H || rewrite <- T)
         end.

(* ------------------------ *)



(*
Theorem trw_demo: forall (P Q: nat -> Type),
 (forall n, P n <=> Q n )
  -> ((P 1 * void -> void ) <=> (Q 1 * void -> void )).
Proof.
  intros ? ?  Hiff.
  assert (P 1) by aXdmit.
  trw_h Hiff  X.
  trw Hiff .  apply t_iff_refl.
Qed.

(*
Theorem trw_demo2:
  forall (P Q: nat -> Type),
    (forall n, P n <=> forall m, Q m )
    -> ((P 1 * void -> void ) <=> ((forall m, Q m) * void -> void )).
Proof.
  intros ? ?  Hiff.
  constructor; intros.
  destruct X; auto.
  destruct X; auto.
Qed.
*)

Theorem trw_demo2:
  forall (P Q: nat -> Type),
    (forall n, P n <=> forall m, Q m )
    -> ((P 1 * void -> void ) <=> ((forall m, Q m) * void -> void )).
Proof.
  intros ? ?  Hiff.
  trw Hiff.
  apply t_iff_refl.
Qed.
*)



(**  --- setoid stuff -- delete? *)

Require Import Coq.Setoids.Setoid.

Inductive Cast (t : [univ]) : Prop :=
| cast : t -> Cast t.
Hint Constructors Cast.

Inductive Cast2 (p : Prop) : [univ] :=
| cast2 : p -> Cast2 p.
Hint Constructors Cast2.

Definition c_t_iff : relation [univ] :=
  fun A B : [univ] => Cast (A <=> B).

Notation "x <==> y" := (c_t_iff x y) (at level 95, no associativity).

Definition t_c_iff : relation [univ] :=
  fun A B : [univ] => Cast (A -> B) /\ Cast (B -> A).

Notation "x <~> y" := (t_c_iff x y) (at level 95, no associativity).

Lemma CType_S : Setoid_Theory [univ] c_t_iff.
Proof.
  split.

  repeat constructor; auto.

  unfold Symmetric; intros.
  inversion H; subst.
  dall.
  repeat constructor; auto.

  unfold Transitive; intros.
  inversion H; inversion H0; subst.
  dall.
  repeat constructor; auto.
Qed.

Lemma TypeC_S : Setoid_Theory [univ] t_c_iff.
Proof.
  split.

  repeat constructor; auto.

  unfold Symmetric; intros.
  destruct H.
  inversion H; subst.
  inversion H0; subst.
  repeat constructor; auto.

  unfold Transitive; intros.
  destruct H; destruct H0.
  inversion H; inversion H0; inversion H1; inversion H2; subst.
  repeat constructor; auto.
Qed.

Add Setoid [univ] c_t_iff CType_S as Type_iff_reg.
Add Setoid [univ] t_c_iff TypeC_S as Type_iff_reg2.

Hint Resolve (Seq_refl  [univ] c_t_iff CType_S): setoid.
Hint Resolve (Seq_sym   [univ] c_t_iff CType_S): setoid.
Hint Resolve (Seq_trans [univ] c_t_iff CType_S): setoid.

Hint Resolve (Seq_refl  [univ] t_c_iff TypeC_S): setoid.
Hint Resolve (Seq_sym   [univ] t_c_iff TypeC_S): setoid.
Hint Resolve (Seq_trans [univ] t_c_iff TypeC_S): setoid.

(* ============================================== *)

(*
Lemma test :
  forall a b (*c f*), (a <=> b) -> Cast a. (*.  # { x : c | f x }.*)
Proof.
  intros.
  rewrite X.
Qed.
*)

(** should not be required anymore? *)

Tactic Notation "trewrite" "<-" ident(H) ident(p1) :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_rev name;
    clear name.

Tactic Notation "trewrite" "<-" ident(H) ident(p1) ident(p2) :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_rev name;
    clear name.
Tactic Notation "trewrite" ident(H) ident(p1) :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite name;
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) ident(p2) :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite name;
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) "in" ident (H') :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_hyp name H';
    clear name.

Tactic Notation "trewrite" ident(H) ident(p1) ident(p2) "in" ident (H') :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_hyp name H';
    clear name.
Tactic Notation "trewrite" "<-" ident(H) ident(p1) "in" ident(H') :=
  let name := fresh H in
  generalize (H p1);
    intro name;
    build_and_rewrite_hyp_rev name H';
    clear name.

Tactic Notation "trewrite" "<-" ident(H) ident(p1) ident(p2) "in" ident(H') :=
  let name := fresh H in
  generalize (H p1 p2);
    intro name;
    build_and_rewrite_hyp_rev name H';
    clear name.

Theorem dont_touch_forall :
  forall (P Q : (nat : Set) -> [univ]),
    (forall (n : (nat : Set)), P n <=> (forall (m : (nat : Set)), Q (m+n)))
    -> P (1 : (nat : Set))
    -> forall (m : (nat : Set)), Q (m+1).
Proof.
  intros ? ? Hif Hp1.

  rw Hif in Hp1; trivial.
Qed.

Theorem dont_touch_forall2 :
  forall (P Q : nat -> [univ]),
    (forall n, P n <=> (forall m, Q (m+n)))
    -> P 1
    -> forall m, Q (m+1).
Proof.
  intros ? ?  Hif Hp1.
  trw_rev Hif. trivial.
Qed.

Theorem dont_touch_forall3 :
  forall (P Q: nat -> [univ]),
    (forall n, P n <=> (forall m, Q (m+n)))
    -> (forall m, Q (m+1))
    -> P 1.
Proof.
  intros ? ? Hif Hq .
  trw_rev_h Hif Hq. trivial.
Qed.
