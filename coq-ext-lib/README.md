coq-ext-lib
===========

A collection of theories and plugins that may be useful in other Coq developments.

Ideas
-----
- Use modules for controlling namespaces.
- Avoid functors in favor of type classes since type classes are more flexible
  b/c they are first-class.
- Notations should be hidden by modules that are explicitly opened.
  - This avoids clashes between precedence. 
  - TB: Actually, this does not completely avoid clashes, if we have to open two modules at the same time (for instance, I often need to open Equality, to get dependent destruction, which conflicts with the rest of my development)
  - TB: I like the idea of having to prefix operations by the name of the module (e.g., DList.fold, DList.map, DList.T), and yet to benefit from the support of notations, without opening this module. I implement that by having a module DList that contains the operations, inside the file DList. The notations leave in the file DList, and I do Require Import DList everywhere...
- Avoid the use of the 'core' hint database.
- Avoid the use of dependent functions, e.g. dependendent decidable equality,
  in favor of their boolen counter-parts. Use type-classes to expose the proofs.
- 

File Structure
--------------
* plugins/
  - Base directory to the provided plugins
* theories/
  - Base directory to the provided theories

