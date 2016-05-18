Adapted  from https://raw.githubusercontent.com/HoTT/HoTT/master/STYLE.md

# Conventions And Style Guide #

## Organization ##

### theories/
This directory hosts all the intermediate/terminal languages, and the translations between them.
There should be one directory named Lxxx for each intermediate/terminal language, where xxx is a natural number.
Such directories can be nested. For example, the intermediate language L2.22.45 should reside in theories/L2/L22/L45

Because we are using version control, it is desirable to remove files and directories that are not in use.
(Should we switch from the current vanilla SVN service to [Cornell's Github service][cisgithub]?)

[cisgithub]: https://github.coecis.cornell.edu/

### theories/....../Lppp/Lxxx/
- There should be a file named term.v containing a `Definition`/`Inductive`/`Let`/`Notation` named `Term`, which is the type of terms in Lxxx. If this file is missing, it means that Lxxx shares the type of terms with Lppp. All directories of the form theories/Lxxx must have a term.v

- The translation from Lxxx to Lyyy should be defined in Lyyy/Lxxx_to_Lyyy.v . Ideally, this file should NOT contain the correctness proof of the translation. That should be in Lyyy/Lxxx_to_Lyyy_correctness.v


### reports/2016April

For each intermediate language, add an entry in reports/2016April explaining its purpose.
If needed, it can refer to a README file for additional details about a language. Such README files should be placed at the root of the directory of the corresponding language.

### theories/_CoqProject
The first line should be:

-R . Certicoq

This means that a definition, say d, in theories/Lxxx/Lyyy/f.v will be accessed in .v files as `Certicoq.Lxxx.Lyyy.f.d`
All imports (`Require Import/Export`) in .v files should be fully qualified, to avoid ambiguities.
For each .v file, there should be an entry in theories/_CoqProject.

### theories/common

### libraries/
move to theories/common? Currently, it is compiled in the namespace "", which is problematic if someone wishes to use our development.


## Naming Conventions ##

### General principles ###

In general, the name of a theorem (or definition, or instance, etc.)
should begin with the property (or structure, or class, or record,
etc.) being proven, and then state the object or construction it is
being proven about.  For instance, `isequiv_idmap` proves `IsEquiv
idmap`, and `equiv_compose` constructs an "Equiv" record by composing
two given equivalences.

In particular, a prefix of `path_` means a theorem that constructs a
path in some type.  For instance, `path_sigma` is a theorem
constructing paths in a sigma-type.

More generally, where applicable the order of parts in a lemma name
should roughly respect their placement in (the syntax tree of) the
goal, from outermost to deepest.  For instance, `path_equiv`
constructs a path in the type `Equiv f g`, while `isequiv_path_equiv`
shows that `path_equiv` is an equivalence.

### Capitalization and spacing ###

Names of types, such as `Unit` and `Equiv` and `IsHProp`, should
generally be capitalized.  Names of functions and definitions should
be lowercase, including the names of types when they appear therein.
Thus, for instance, the theorem that `Unit` is contractible is
`contr_unit : Contr Unit`.

Multiple-word names, especially in lowercase, should generally be
separated with underscores.  We make an exception for names of types
beginning with `is`, such as `IsEquiv` and `IsTrunc`.

### Suffixes ###

A suffix of `D` indicates a dependent version of something ordinarily
non-dependent.  For instance, `ap` applies to non-dependent functions
while `apD` applies to dependent ones.  When possible, the
non-dependent version should be an instantiation of the dependent one
using constant type families, but sometimes they are more different
than this, usually due to the fact that `transport_const` is not the
identity (e.g. `ap` and `apD`).

When there is more than one theorem that seems to merit the same name,
and no obvious concise way to distinguish them, one of them can be
given a prime suffix, e.g. we have `path_sigma` and `path_sigma'`.
Do this with caution.



## Records, Structures, Typeclasses ##

### Typeclasses ###

### When to declare instances ###

When constructing terms in a typeclass record such as `IsEquiv`, `Contr`,
or `IsTrunc`, one has the choice to declare it as an `Instance`, in which
case it is added to the hint database that is searched when Coq tries
to do typeclass instance resolution.  Care must be taken with this, as
indiscriminately adding theorems to this database can easily result in
infinite loops (or at least very long loops).

In general, it seems to be better not to add instances which suggest
an open-ended search.  E.g. the theorem that truncation levels are
closed under equivalence is a bad candidate for an `Instance`, because
when Coq is searching for a proof of `Contr B` this theorem could
cause it to look through all possible types A for an equivalence `A
<~> B` and a proof of `Contr A`.  Results of this sort should be
proven as `Definition`s or `Theorem`s, not as `Instance`s.  If you
need to use a result of this sort in the middle of a proof, use a
tactic like `pose` or `assert` to add a particular instance of its
conclusion to the context; then it will be found by subsequent
typeclass resolution.

If you have determined through trial and error that a particular
result should not be an `Instance` (e.g. when making it an `Instance`,
a tactic in some other proof loops, but changing it to a `Definition`
prevents this), please add a comment to that effect where it is
defined.  This way no one else will come along and helpfully change it
back to an `Instance`.

If a particular fact should not be made an ordinary instance, it can
still be made an "immediate instance", meaning that Coq will use it
automatically to solve a goal *if* its hypotheses are already present
in the context, but will not initiate an instance search for those
hypotheses otherwise.  This avoids infinite instance-search loops.  To
declare a fact as an immediate instance, make it a `Definition` rather
than an `Instance` and then say

```coq
Hint Immediate foo : typeclass_instances.
```

### Local and Global Instances ###

When declaring an `Instance` you should *always* use either the
`Local` or the `Global` keyword.  The former makes the instance local
to the current section, module, or file (although its *definition*
will still be visible globally, it won't be in the instance database
for typeclass resolution outside its containing section, module or
file), while the latter puts it in the instance database globally.
If you write `Instance` without `Local` or `Global`, Coq will
sometimes make it local and sometimes global, so to avoid confusion it
is better to always specify explicitly which you intend.

### Using Typeclasses ###

Try to avoid ever giving a name to variables inhabiting typeclasses.
When introducing such a variable, you can write `intros ?` to put it
in the hypotheses without specifying a name for it.  When using such a
variable, typeclass resolution means you shouldn't even need to refer
to it by name: you can write `_` in tactics such as `refine` and Coq
will find typeclass instances from the context.  Even `exact _` works.
(You can usually also use `typeclasses eauto` or `eauto with
typeclass_instances`, but `exact _` is preferable when it works, as it
is shorter and uses a tactic name the reader is presumably already
familiar with.)

Unfortunately, it is not currently possible to write `_` in a
`refine`d term for an inhabitant of a typeclass and have Coq generate
a subgoal if it can't find an instance; Coq will die if it can't
resolve a typeclass variable from the context.  You have to `assert`
or `pose` such an inhabitant first, or give an explicit term for it.

Note that when you don't give a name to a variable, Coq often names it
`H` or some modification thereof.  For that reason, it's often better
avoid using `H` for your own explicitly named variables, since if you
do and later on someone introduces a new unnamed hypothesis that Coq
names `H`, your name will result in a conflict.  Conversely, we
sometimes give a hypothesis a name that won't be used, to pre-empt
such conflicts, such as `{ua : Univalence}` or `{fs : Funext}`.

One gotcha about typeclass arguments is that they cannot be inferred automatically when preceeded by non-implicit arguments.  So for instance if we write

```coq
Definition foo (A : Type) `{Funext}
```

then the `Funext` argument will not generally be inferrable.  Thus, typeclass arguments should generally come first if possible.  In addition, note that when section variables are generalized at the close of a section, they appear first.  Thus, if anything in a section requires `Funext` or `Univalence`, those hypotheses should go in the `Context` at the top of the section in order that they'll come first in the eventual argument lists.


### Coercions and Existing Instances ###

A "coercion" from `A` to `B` is a function that Coq will insert
silently if given an `A` when it expects a `B`, and which it doesn't
display.  For example, we have declared `equiv_fun` as a coercion from
`A <~> B` to `A -> B`, so that we can use an equivalence as a function
without needing to manually apply the projection `equiv_fun`.
Coercions can make code easier to read and write, but when used
carelessly they can have the opposite effect.

When defining a record, Coq allows you to declare a field as a
coercion by writing its type with `:>` instead of `:`.  Please do
_not_ do this in the core: instead, give an explicit `Coercion`
declaration after defining the record.  There are two reasons for
this.  Firstly, the syntax `:>` is very short and easy to miss when
reading the code, while coercions are important to be aware of.
Secondly, it is potentially confusing because the same syntax `:>`
when defining a typeclass (i.e. a `Class` instead of a `Record`) has a
different meaning: it declares a field as an `Existing Instance`.
Please do not use it in that case either; declare your `Existing
Instance`s explicitly as well.


## Transparency and Opacity ##

If the value of something being defined matters, then you must either
give an explicit term defining it, or construct it with tactics and
end the proof with `Defined.`  But if all that matters is that you
have defined something with a given type, you can construct it with
tactics and end the proof with `Qed.`  The latter makes the term
"opaque" so that it doesn't "compute".

In general, it is okay to contruct something transparent using
tactics; it's often a matter of aesthetics whether an explicit proof
term or a tactic proof is more readable or elegant, and personal
aesthetics may differ.  Consider, for example, the explicit proof term
given for `eckmann_hilton`: some may consider it optimally elegant,
while others would prefer to be able to step through a tactic proof to
understand what is happening step-by-step.

One thing to beware of is explicit `match` terms that require `in` or
`return` annotations, as these are particularly difficult for
newcomers to understand.  Avoiding them is not a hard and fast rule,
but when there is a short proof using tactics that produces an
acceptable proof term, it should probably be preferred.

The important thing is that when defining a transparent term with
tactics, you should restrict yourself to tactics which maintain a high
degree of control over the resulting term; "blast" tactics like
`autorewrite` should be eschewed.  Even plain `rewrite` is usually to
be avoided in this context: although the terms it produces are at
least predictable, they are one big `transport` (under a different
name) whereas a term we would want to reason about ought to be
constructed using smaller pieces like `ap` and `concat` which we can
understand.

Here are some acceptable tactics to use in transparent definitions
(this is probably not an exhaustive list):

- `intros`, `revert`, `generalize`, `generalize dependent`
- `pose`, `assert`, `set`, `cut`
- `transparent assert` (see below)
- `fold`, `unfold`, `simpl`, `cbn`, `hnf`
- `case`, `elim`, `destruct`, `induction`
- `apply`, `eapply`, `assumption`, `eassumption`, `refine`, `exact`
- `reflexivity`, `symmetry`, `transitivity`, `etransitivity`
- `by`, `done`

Conversely, if you want to use `rewrite`, that is fine, but you should
then make the thing you are defining opaque.  If it turns out later
that you need it to be transparent, then you should go back and prove
it without using `rewrite`.

Currently, there are some basic facts in the library, such as the
"adjointify" lemma, which are proven using `rewrite` and hence are at
least partially opaque.  It might be desirable one day to prove these
more explicitly and make them transparent, but so far it has not been
necessary.

Note that it *is* acceptable for the definition of a transparent
theorem to invoke other theorems which are opaque.  For instance,
the "adjointify" lemma itself is actually transparent, but it invokes
an opaque sublemma that computes the triangle identity (using
`rewrite`).  Making the main lemma transparent is necessary so that
the other parts of an equivalence -- the inverse function and
homotopies -- will compute.  Thus, a transparent definition will not
generally be "completely transparent".

It is possible to make subterms of a term opaque by using the
`abstract` tactic, although that requires grouping the entire proof
script to be abstracted into a single command with semicolons,
e.g. `abstract (apply lem1; apply lem2; reflexivity)`.  Note that the
`assert` tactic produces subterms that cannot be inspected by the rest
of the proof script, but they remain transparent in the resulting
proof term (at least if the proof is ended with `Defined.`).

For a transparent subterm, use `refine` or `transparent assert` (the
latter defined in `Basics/Overture`; see "Available tactics", below).


## Formatting ##

### Location of commands

All `Require` commands should be placed at the top of a file.
Ideally, they should be grouped onto lines according to the rough
grouping of files listed under "Organization".  Requires should
generally be followed by all `[Local] Open Scope` commands, and then
by `Generalizable Variables` commands.

The latter two might also occur in Sections later on in the file, but
in that case they should usually come at the beginning of the Section.
The assumptions of a section, such as `Variable` and `Context`, should
also generally come at the beginning of that section.

### Indentation

In general, the bodies of sections and modules should be indented, two
spaces per nested section or module.  This is the default behavior of
ProofGeneral.

However, when enclosing existing code in a new section or module, it
is acceptable to avoid re-indenting it at the same time, to avoid
excessive churn in the diff.  If you wish, you can submit a separate
pull request or commit for the re-indentation, labeled as "only
whitespace changes" so that no one bothers reading the diff carefully.

### Line lengths

Lines of code should be of limited width; try to restrict yourself to
not much more than 70 characters.  Remember that when Coq code is
often edited in split-screen so that the screen width is cut in half,
and that not everyone's screen is as wide as yours.

Text in comments, on the other hand, should not contain hard newlines.
Putting hard newlines in text makes it extremely ugly when viewed in a
window that is narrower than the width to which you filled it.  If
editing in Emacs, turn off `auto-fill-mode` and turn on
`visual-line-mode`; then you'll be able to read comment paragraphs
without scrolling horizontally, no matter how narrow your window is.
Some files contain `(* -*- mode: coq; mode: visual-line -*- *)` at the
top, which does this automatically; feel free to add it to files that
are missing it.

Unfortunately, when viewing source code on Github, these long comment
lines are not wrapped, making them hard to read.  If you use the
Stylish plugin, you can make them wrap by adding the following style:

    @-moz-document domain(github.com) {
        div.line {
            white-space: pre-wrap;
        }
    }

This messes up the line-numbering, though, you'll have to turn it
off in order to link to or comment on a particular line.

### Tactic scripts ###

When writing tactic scripts, `Proof.` and `Defined.` should be given
as individual lines, and the tactic code should be indented.  Within
the tactic script, use newlines as a "logical grouping" construct.
Important tactic invocations, such as a top-level `induction` which
create a branch point in the proof, should generally be on lines by
themselves.  Other lines can contain several short tactic commands
(separated by either periods or semicolons), if they together
implement a single idea or finish off a subgoal.

For long proofs with multiple significant subgoals, use branching
constructs such as bullets and braces to clarify the structure.  See
the section of the Coq Reference Manual entitled "Navigation in the
proof tree".

### Placement of Arguments and types ###

If the entire type of a theorem or definition does not fit on one
line, then it is better to put the result type (the part after the
colon) on an indented line by itself, together with the colon to make
it clear that this is the result type.

```coq
Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q.
```

Of course, if the list of input types does not fit on a line by
itself, it should be broken across lines as well, with later lines
indented, and similarly for the result type.

```coq
Definition pentagon {A : Type} {v w x y z : A}
  (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s.
```

For definitions given with an explicit term, that term should usually
also be on an indented line by itself, together with the := to make it
clear that this is the definition.

```coq
Definition concat_p1 {A : Type} {x y : A} (p : x = y) : p @ 1 = p
  := match p with idpath => 1 end.
```

Of course, if the term is longer than one line, it should be broken
across lines, with later lines indented further.


## Implicit Arguments ##

Do not use `Set Implicit Arguments` in the core.  It makes it
difficult for a newcomer to read the code; use braces `{...}` to
explicitly mark which arguments are implicit.  If necessary, you can
use the `Arguments` command to adjust implicitness of arguments after
a function is defined, but braces are preferable when possible.

Warning: if you want to use `Arguments` to make *all* the arguments of
a function explicit, the obvious-looking syntax `Arguments foo a b`
does not work: you have to write `Arguments foo : clear implicits`
instead.


## Coding Hints ##

### Notations ###

The operation `compose`, notation `g o f`, is simply a notation for
`fun x => g (f x)` rather than a defined constant.  We define `compose
:= (fun g f x => g (f x))` so that typeclass inference can pick up
`isequiv_compose` instances.  This has the unfortunate side-effect
that `simpl`/`cbn` is enough to "unfold" `compose`, and there's no way
to prevent this.  We could additionally define `g o f := (fun x => g
(f x))` to change this, but this would result in identically looking
goals which are really different.  We consider it poor style to use
`compose` as a partially applied constant, such as `compose g`; we
take the point of view that `fun f => g o f` is more readable anyway.

### Unfolding definitions ###

When a definition has to be unfolded repeatedly in the middle of
proofs, you can say `Local Arguments name / .`, which tells `simpl`
and related tactics to automatically unfold `name`.  In particular,
this allows the tactic `simpl rewrite` (defined in `Tactics`) to apply
theorems containing `name` to goals in which it has been unfolded.  It
seems better not to make these declarations globally, however.

It may not always be obvious which definition this needs to be applied
to; sometimes the unification failure happens in an implicit argument
that is not directly visible in the output.  One way to discover where
the problem lies is to turn on printing of all implicit arguments with
`Set Printing All`; another is to use `Set Debug Tactic Unification`
and inspect the output to see where `rewrite` is failing to unify.

### Finding theorems ###

The naming conventions mentioned above often help to guess the name of
a theorem.  However, it still may happen that you expect that a
theorem should exist but don't know what it is called.  One approach
to finding it is to guess what file it should live in and look there;
for instance, theorems about sigma-types are often in `Types/Sigma.v`,
and so on.

Another approach is to use Coq's command `SearchAbout` to display all
the theorems that relate to a particular definition.  This has the
[disadvantage](https://coq.inria.fr/bugs/show_bug.cgi?id=3904) that it
doesn't "look through" definitions and notations.  For instance,
`IsHProp` is a `Notation` for `IsTrunc -1`, but `SearchAbout IsHProp`
won't show you theorems about `IsTrunc`.  So if you can't find
something at first using `SearchAbout`, think about ways that your
desired theorem might be generalized and search for those instead.

Generalizing from a particular truncation level (like `IsHProp`) to
all truncation levels is a good example.  Another one that it's
important to be aware of is a generalization from truncation
(`IsTrunc` and `Trunc`) to all reflective subuniverses or modalities;
many many theorems about truncation are actually proven more generally
in the latter situations.  (To obtain those theorems for the special
case of truncation, you'll generally need to `Import TrM`.)

### Simpl nomatch ###

If a theorem or definition is defined by `destruct` or `match` (as
many operations on paths are), and if its value needs to be reasoned
about in tactic proofs, then it is helpful to declare its arguments as
`Arguments foo ... : simpl nomatch`.  This instructs `simpl` and
related tactics never to simplify it if doing so would result in a
`match` that doesn't reduce, which is usually what you want.


## Contributing to Certicoq ##

### Commit messages ###

Please try to keep commit messages clear and informative.  We don’t
currently have a specific preferred convention, but the answers
[here][commits1] and [here][commits2] (not just the top answers!) give
excellent, if varied, advice.  That said, this is a minor point.  Good
code with bad commit messages is much better than the reverse!

Some good examples, showing what kind of change was made (additions,
updates, fixes), and what material it was on:

- "adapt to the new version of coqtop by disabling the native compiler"
- "Resolved universe inconsistency in Freudenthal."
- "epis are surjective"

Some bad examples:

- "further progess"  Progress in what files?
- "Bug in [Equivalences.v]."  Was the bug fixed, or just noticed and
  flagged in comments, or what?
- "asdfjkl"

[commits1]: http://stackoverflow.com/questions/43598/suggestions-for-a-good-commit-message-format-guideline

[commits2]: http://stackoverflow.com/questions/3580013/should-i-use-past-or-present-tense-in-git-commit-messages

