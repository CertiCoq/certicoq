Require Import Coq.Strings.String.
Require Import Coq.Program.Wf.
Require Import Omega.

Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Programming.Injection.
Require Import ExtLib.Data.Char.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Definition showM : Type := 
  forall m, Injection ascii m -> Monoid m -> m.

Class ShowScheme (T : Type) : Type :=
{ show_mon : Monoid T
; show_inj : Injection ascii T
}.

Global Instance ShowScheme_string : ShowScheme string :=
{ show_mon := Monoid_string_append
; show_inj := fun x => String x EmptyString
}.

Global Instance ShowScheme_string_compose : ShowScheme (string -> string) :=
{ show_mon := Monoid_compose string
; show_inj := String 
}.

Definition runShow {T} {M : ShowScheme T} (m : showM) : T :=
  m _ show_inj show_mon.

Class Show T := show : T -> showM.

Definition to_string {T} {M : Show T} (v : T) : string :=
  runShow (show v) ""%string.

Definition empty : showM := 
  fun _ _ m => monoid_unit m.
Definition cat (a b : showM) : showM :=
  fun _ i m => monoid_plus m (a _ i m) (b _ i m).
Global Instance Injection_ascii_showM : Injection ascii showM :=
  fun v => fun _ i _ => i v.

Fixpoint show_exact (s : string) : showM :=
  match s with
    | EmptyString => empty
    | String a s' => cat (inject a) (show_exact s')
  end.

Module ShowNotation.
  Delimit Scope show_scope with show.

  Notation "x << y" := (cat x%show y%show) (at level 100) : show_scope.
  Coercion show_exact : string >-> showM.
  Definition _inject_char : ascii -> showM := inject.
  Coercion _inject_char : ascii >-> showM.
End ShowNotation.

Definition indent (indent : showM) (v : showM) : showM :=
  let nl := Ascii.ascii_of_nat 10 in
    fun _ inj mon => 
      v _ (fun a => if eq_dec a nl
         then monoid_plus mon (inj a) (indent _ inj mon)
         else inj a) mon.

Section hiding_notation.
  Import ShowNotation.
  Local Open Scope show_scope.
  Require Import Ascii.
  Require Import String.

Global Instance unit_Show : Show unit :=
  { show u := "tt"%string }.
Global Instance bool_Show : Show bool :=
  { show b := if b then "true"%string else "false"%string }.
Global Instance ascii_Show : Show ascii :=
  fun a =>  "'"%char << a << "'"%char.
Global Instance string_Show : Show string :=
  { show s := """"%char << s << """"%char }.

Program Fixpoint nat_show (n:nat) {measure n} : showM :=
  if Compare_dec.le_gt_dec n 9 then
    inject (Char.digit2ascii n)
  else
    let n' := NPeano.div n 10 in
    (@nat_show n' _) << (inject (Char.digit2ascii (n - 10 * n'))).
Next Obligation.
  assert (NPeano.div n 10 < n) ; eauto.
  eapply NPeano.Nat.div_lt ; omega.
Defined.
Global Instance nat_Show : Show nat := { show := nat_show }.

Global Instance Show_pos : Show positive :=
  fun x => nat_show (Pos.to_nat x).

Global Instance Show_Z : Show Z :=
  fun x => 
    match x with
      | Z0 => "0"%char
      | Zpos p => show p
      | Zneg p => "-"%char << show p
    end.

Section pair_Show.
  Context {A B} {AS:Show A} {BS:Show B}.
  Global Instance pair_Show : Show (A*B) :=
    { show p :=
        let (a,b) := p in
        "("%char << show a << ","%char << show b << ")"%char
    }.
End pair_Show.

Section sepBy.
  Variable T : Type.
  Context {F : Foldable T showM}.

  Definition sepBy (sep : showM) (ls : T) : showM :=
    match 
      fold (fun s acc =>
        match acc with
          | None => Some s
          | Some x => Some (x << sep << s)
        end) None ls
      with
      | None => empty
      | Some s => s
    end.
End sepBy.

Section sepBy_f.
  Variable T E : Type.
  Context {F : Foldable T E}.
  Variable (f : E -> showM).

  Definition sepBy_f (sep : showM) (ls : T) : showM :=
    match 
      fold (fun s acc =>
        match acc with
          | None => Some (f s)
          | Some x => Some (x << sep << f s)
        end) None ls
      with
      | None => empty
      | Some s => s
    end.
End sepBy_f. 

Definition wrap (before after : showM) (x : showM) : showM :=
  before << x << after.

Section sum_Show.
  Context {A B} {AS:Show A} {BS:Show B}.
  Global Instance sum_Show : Show (A+B) :=
    { show s :=
        let (tag, payload) :=
          match s with
          | inl a => (show_exact "inl"%string, show a)
          | inr b => (show_exact "inr"%string, show b)
          end
        in
        "("%char <<
        tag <<
        " "%char <<
        payload <<
        ")"%char
    }.
End sum_Show.

Section foldable_Show.
  Require Import ExtLib.Structures.Reducible.
  Context {A B} {F : Foldable B A} {BS : Show A}.

  Global Instance foldable_Show : Show B :=
    { show s := sepBy_f show ", "%string s }.

End foldable_Show.

End hiding_notation.

Fixpoint iter_show (ss : list showM) : showM :=
  match ss with
    | nil => empty
    | cons s ss => cat s (iter_show ss)
  end.


(*
Examples:
Eval compute in (runShow (show (42,"foo"%string)) : string).
Eval compute in (runShow (show (inl true : bool+string)) 
*)
