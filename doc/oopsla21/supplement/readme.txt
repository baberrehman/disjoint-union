This folder contains supplementry material associated with
the paper Union Types with Disjoint Switches.

Each folder contains Coq files for a variant of
our calculus. Organization of folders is:

|------------------|----------------------------------------------|--------------------------|
|  Folder          |   Systam                                     | Reference in paper       |
|------------------|----------------------------------------------|--------------------------|
|union             | Union calculus                               | Discussed in section 3   |
|------------------|----------------------------------------------|--------------------------|
|union-inter       | Union calculus with intersection types       | Discussed in section 4   |
|------------------|----------------------------------------------|--------------------------|
|general-subtyping | An extension with generalized subtyping rule | Discussed in section 5.1 |
|------------------|----------------------------------------------|--------------------------|
|distributivity    | An extension with distributive subtyping     | Discussed in section 5.2 |
|------------------|----------------------------------------------|--------------------------|


Organization within each folder is as follows:

======
union
======
syntax.v contains syntax of the respective calculus and disjointness properties.
typing.v contains semantics and properties related to type-safety.
1) typing.v depends upon syntax.v.


===========
union-inter
===========
syntax.v contains syntax of the respective calculus and disjointness properties.
typing.v contains semantics and properties related to type-safety.
1) typing.v depends upon syntax.v.


=================
general-subtyping
=================
syntax.v contains syntax of the respective calculus and disjointness properties.
typing.v contains semantics and properties related to type-safety.
1) typing.v depends upon syntax.v.


==============
distributivity
==============
equivalence.v contains distributive subtyping.
syntax.v contains syntax of the respective calculus and disjointness properties.
typing.v contains semantics and properties related to type-safety.
1) syntax.v depends upon equivalence.v.
2) typing.v depends upon syntax.v and equivalence.v.
3) equivalence.v depends upon LibTactics.v.


============
Dependencies
============


Coq Version:
-----------
We tested all the Coq files using Coq version 8.10.0. Please use same version for the sake
of consistency. We recommend installing Coq using the opam package installer. Coq TLC
library is also required to compile the code. TLC library can also be installed using the
opam package installer. Refer to this link for more information and installation
steps: https://coq.inria.fr/opam-using.html


External Library:
----------------
TLC library is required to run the files.
