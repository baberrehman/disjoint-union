This folder contains supplementry material associated with
the paper Union Types with Disjoint Switches.

Each folder contains Coq files for a variant of
our calculus. Organization of folders is:

|------------------|------------------------------------------------|--------------------------|
|  Folder          |   Systam                                       | Reference in paper       |
|------------------|------------------------------------------------|--------------------------|
|union             | Union calculus                                 | Discussed in section 3   |
|------------------|------------------------------------------------|--------------------------|
|union-inter       | Union calculus with intersection types         | Discussed in section 4   |
|------------------|------------------------------------------------|--------------------------|
|general-subtyping | Union calculus with generalized subtyping rule | Discussed in section 5.1 |
|------------------|------------------------------------------------|--------------------------|
|distributivity    | Union calculus with distributive subtyping     | Discussed in section 5.2 |
|------------------|------------------------------------------------|--------------------------|


Each folder further has two files, namely syntax.v and typing.v.

------
syntax:
------
This file defines syntax of the calculus and disjointness properties

-------
typing:
-------
This file contains semantics and properties related to type-safety.
typing.v depends upon syntax.v.

------------
Dependencies
------------


Coq Version:
-----------
We used Coq version 8.10.0 in our development


External Library:
----------------
TLC library is required to run the files.
