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

  To install the compiler, you need OCaml, Coq.8.9.1 along with the
ExtLib, MetaCoq (which requires Equations), squiggle-eq and paramcoq
packages.  One way to get everything is using
[`opam`](http://opam.ocaml.org) (current version: `2.0.4`):

  To add the official Coq repositories, you need to declare the
repositories:

    # opam repo add coq-released https://coq.inria.fr/opam/released
    # opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

  One can also **optionally** add the `extra-dev` repository, which contains packages
for development versions (e.g. `git` branches) and is relatively
unstable.  It might be needed to compile non-released versions of
CertiCoq. Beware `opam` will usually select packages from there as they
have the most permissive dependencies, which might not always be what
you want.

    # opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

Setting up a switch with OCaml
------------------------------

  Note that supported OCaml version are `4.06.1` and upwards, avoid
`4.06.0` which sometimes produces dynamic linking errors. In `opam 1.*`,
use `opam config var ocaml-version` to confirm you have a compatible
compiler. If not, you should create a fresh new switch with a specific
compiler, using:

    # opam switch -A 4.07.1 coq89
    # eval `opam config env`

  This will install the `4.07.1` compiler in a new switch named `coq89`
and put you in the right environment (check with `ocamlc --version`).

Installing Coq
--------------

  To install coq in a fresh switch:

    # opam install coq.8.9.1

  *Recommended* To pin Coq to a specific version so that `opam` doesn't 
  try to upgrade it in this switch, use:

    # opam pin add coq 8.9.1

  Alternatively, if you can you want to update a pinned version of Coq:

    # opam pin remove coq
    # opam pin add coq 8.9.1

  After this you should have `coqc --version` give you the right version
number.

Git submodules of dependencies:
-------------------------------

For development versions, we are using git submodules instead of opam
packages to keep in sync with upstream. To work with submodules, follow
these steps. At the first checkout of a branch using submodules, you
should do:

    # git submodule init

  this should tell you that it registered e.g. the MetaCoq module.

    # make submodules

  This will fetch the appropriate branch from the submodule (e.g. MetaCoq) in the 
appropriate directory in submodules and (re)make and (re)install submodules in 
their order of dependencies.

  When one modifies a submodule (e.g. MetaCoq) (by adding commits for
example), all users of the branch have to do *by themselves* a:

    # make submodules

Which will perform a `git submodule update` and rebuild and reinstall all submodules
from scratch.

  *Not recommended* and **at your own risk**, you can use:

    # git submodule update
    # ./make_submodules.sh noclean

  This reperforms installation of the submodules **without** cleaning the previous
compilation state of each submodule. It can be useful if the update does not require
a full rebuild of the module. 

Keeping opam up-to-date
-----------------------

When the above opam repositories are updated, you may need to update your installation.

    # opam update

If the dependencies are already installed then you can skip the following section and just do:

    # opam upgrade coq-metacoq coq-ext-lib coq-paramcoq coq-squiggle-eq 

Installing dependencies through opam
------------------------------------

FIXME: **currently not working**, we need a synchronized release of upstream packages (notably
  metacoq) and certicoq.

To install CertiCoq's dependencies in the current `opam` switch:

    # opam install coq-equations coq-metacoq coq-ext-lib coq-squiggle-eq.dev coq-paramcoq

The package is known to build with `coq-template-coq.2.1~beta3`,
`coq-ext-lib.0.9.8`, `coq-squiggle-eq.1.0.4` and `coq-paramcoq.1.0.8`.

If you have already installed some package manually, you can choose the
`--fake` keyword for `opam` to assume that it is installed, e.g.:

    # opam install --fake coq

Installing from source
----------------------
Alternatively, you can install Coq from source or download a binary from:

	https://github.com/coq/coq/releases/tag/V8.9.1

and install the packages from source:

	https://github.com/coq-ext-lib/coq-ext-lib
	https://github.com/MetaCoq/metacoq (branch: coq-8.9)
	https://github.com/aa755/SquiggleEq  (branch: vcoq87)
	https://github.com/aa755/paramcoq (branch: v8.8)


Choose the architecture:
----------------------
By default, Certicoq will be built for x86_64. 
However, it can be configured for x86_32 by:
1) In theory/_CoqProject, replace the line
   	   compcert/x86_64/Archi.v	
   by
	  compcert/x86_32/Archi.v	




Building the compiler:
----------------------
  At `certicoq/`, run:

    # make -j4 -k

  This will build the compiler and its proofs.


    # sh make_plugin.sh

To install Certicoq, do the following. This steps the above build steps.

    # make install

To test the installation, go to 'certicoq/benchmark' and run
   # make all

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

