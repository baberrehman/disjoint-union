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


Each folder further has two files, namely syntax.v and typing.v.

------
syntax.v:
------
This file defines syntax of the calculus and disjointness properties

-------
typing.v:
-------
This file contains semantics and properties related to type-safety.
typing.v depends upon syntax.v.


------------
Dependencies
------------


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
