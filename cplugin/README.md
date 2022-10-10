CertiCoq compiler plugin
========================

This directory contains the sources of a plugin for running the
extracted CertiCoq compiler on arbitrary Coq definitions. 
It uses the Template-Coq reifier to the extracted Template-Coq Ast
to build an ML representation of the term which is then directly
fed to the extracted version of the compiler.

Usage
=====

The plugin provides a single command:

```
CertiCoq Compile ref.
```

Where `ref` must be the name of a Coq definition.  The extracted
compiler relies on the `Compiler.allInstances.compile_template_Codegen` and
`Compiler.allInstances.printProg` functions. It will compile the
definition and output the program to file `fullref.c` where fullref is
the fully qualified name of the reference `ref`, in the current working
directory. The resulting code can then be compiled with `gcc` or
`compcert` using the runtime support in `Runtime`.

Installation
============

To build the plugin, first make the CertiCoq project (including
`Extraction/extraction.v`). Then, in the directory above:

``sh make_plugin.sh all`` 

This will copy the extract the implementation to this directory and
compile the plugin. The plugin can then be loaded using `Require Import
CertiCoq` within a `Coq` toplevel having the includes `-R
theories/plugin` and `-I theories/plugin` (as e.g. in the toplevel
`_CoqProject` for running `benchmarks/test_plugin.v`).

In case of trouble building the plugin, it is recommended to try first:

`make -f Makefile.plugin clean` 

Before running `make_plugin.sh`

Adding phases
=============

To ensure proper linking of the extracted code, when one adds a phase to
the compiler, one must add the corresponding .ml and .mli files to
`../_PluginProject` (beware the first letter is always lowercase to
comply with `OCaml` tools) and the module name to `certicoq_plugin.mllib`,
at the right level according to module dependencies. Then `make -f
Makefile.plugin clean && make -f Makefile.plugin all` to rebuild the
dependencies and the plugin.
