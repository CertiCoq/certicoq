The CertiCoq project
====================

AUTHORS
-------

At its initial prerelease, this software is copyright (c) 2018 by
Abhishek Anand, Andrew Appel, Greg Morrisett, Zoe Paraskevopoulou, Randy
Pollack, Olivier Savary Belanger, and Matthieu Sozeau.

LICENSE
-------

The authors intend to open-source license this software during the first
quarter of 2018.  Until that time: Throughout 2018, you are free to
download, examine, install, and use this software for academic or
research purposes.


INSTALLATION INSTRUCTIONS
=========================

  To install the compiler, you need OCaml, Coq.8.7.1 along with the
ExtLib, Template-Coq and squiggle-eq packages.  One way to get
everything is using [`opam`](http://opam.ocaml.org) (current version: `1.2.2`):

  To add the official Coq repositories, you need to declare the
repositories:

# opam repo add coq-released https://coq.inria.fr/opam/released
# opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

  Optionally, add the `extra-dev` repository, which contains packages
for development versions (e.g. `git` branches) and is relatively
unstable.  It might be needed to compile non-released versions of
CertiCoq. Beware `opam` will usually select packages from there as they
have the most permissive dependencies, which might not always be what
you want.

# opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

Setting up a switch with OCaml
------------------------------

  Note that supported OCaml version are `4.02.3` to `4.05.0`, avoid
`4.06.0` which sometimes produces dynamic linking errors. In `opam 1.*`,
use `opam config var ocaml-version` to confirm you have a compatible
compiler. If not, you should create a fresh new switch with a specific
compiler, using:

# opam switch -A 4.05.0 coq87
# eval `opam config env`

  This will install the `4.05.0` compiler in a new switch named `coq87`
and put you in the right environment.

Installing Coq
--------------

  To install coq in a fresh switch and pin it to a specific version so
that `opam` doesn't try to upgrade it:

# opam install coq.8.7.1
# opam pin add coq 8.7.1

  Alternatively, if you can you want to update a pinned Coq:

# opam pin remove coq
# opam pin add coq 8.7.1

  After this you should have `coqc --version` give you the right version
number.

Installing dependencies
-----------------------

Then to install CertiCoq's dependencies:

# opam install coq-template-coq coq-ext-lib coq-squiggle-eq.1.0.3 coq-paramcoq

  The package is known to build with `coq-template-coq.2.0~beta`,
`coq-ext-lib.0.9.7`, `coq-squiggle-eq.1.0.3` and `coq-paramcoq.1.0.5`.

If you have already installed some package manually, you can choose the
`--fake` keyword for `opam` to assume that it is installed, e.g.:

# opam install --fake coq

Installing from source
----------------------
Alternatively, you can install Coq from source or download a binary from:

	https://coq.inria.fr/coq-87

and install the packages from source:

	https://github.com/coq-ext-lib/coq-ext-lib
	https://github.com/gmalecha/template-coq (branch: coq-8.7)
	https://github.com/aa755/SquiggleEq
	https://github.com/aa755/paramcoq (branch: v8.7)


Updating dependencies:
----------------------

When the above repositories are updated, you may need to update your installation.
If you chose opam, you can do

# opam update
# opam upgrade coq-template-coq coq-ext-lib coq-squiggle-eq 


Building the compiler:
----------------------
  At `certicoq/`, run:

# make -j4 -k

  This will build the compiler and its proofs.

To build the OCaml version of the compiler and the
`CertiCoq Compile` plugin, in `theories/`, run:

# sh make_plugin.sh

Troubleshooting:
----------------------

If the above fails, try the following

0) update the dependencies, as explained above

1) "make clean" at certicoq/ and then try to build again. Try "make cleanCoqc" as well.

2) Ensure that your working copy is EXACTLY the same as the contents of SVN repo. Unversioned files and directories should also be removed because they can 
interfere with how Coq resolves imports and how Makefile tracks dependences (via coqdep).

If you are using a git client to access the SVN repo, "git reset HEAD --hard; git clean -xf" ensures that the working copy exactly matches the state of the repository.

If you use the SVN client, there should be something similar:
http://stackoverflow.com/questions/239340/automatically-remove-subversion-unversioned-files
http://stackoverflow.com/questions/6204572/is-there-a-subversion-command-to-reset-the-working-copy

3) Is your file system case-insensitive? Please consider using a linux VM. Or,  try making all Require Imports/Exports fully qualified,
so that Coq doesn't import the wrong file because its name differes only in capitalization.
There is tool to help with that:
https://github.com/JasonGross/coq-tools/


If errors remain AFTER step 2, please send an email to the certicoq mailing list.
Until step 2, others cannot be sure about the state of the working copy of your machine, so their help may not be applicable.

