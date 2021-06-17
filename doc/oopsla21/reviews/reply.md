We thank the reviewers for their insightful and constructive comments.

# Overview

In the general overview of the reply we wish to mainly address the
concerns by Reviewer A and B regarding relevance. We also discuss
various other concerns in the detailed reply. We will incorporate the
reviewers' helpful suggestions in our revision.

## Relevance and Contributions

First, we would like to emphasize the relevance of union types. In
particular, some form of union types has been implemented in many
major programming languages such as Scala 3, TypeScript, Flow or
Julia. We believe this is already providing some evidence of the
practical relevance of union types.

We have also conducted a set of small google queries on stackoverflow
to investigate the extent to which programmers are using union types, and comparing
union types with some other language features under heavy development
in the community. The results are given below.

```
Google query                                | number of results
---------------------------------------------------------------
"union type" site:stackoverflow.com         | 6990
"intersection type" site:stackoverflow.com  | 746
"gradual typing" site:stackoverflow.com     | 144
"dependent type" site:stackoverflow.com     | 2760
```

Somewhat to our surprise union types actually have the largest number
of results. From a quick look at the first 20 pages, most questions
are done by TypeScript programmers. We view these results mostly as
evidence that union types are being used in practice to a significant
extent (at least in TypeScript), not as a direct comparison of
absolute relevance between language features.

Second, our work, based on disjoint switches, contributes an alternative
approach in the general design space of union types that is different
from the approaches to union types in TypeScript or Flow. As described
in the paper, such an approach can be an easier to reason alternative to certain
forms of overloading; and be used for dealing with failure in
various way. One of the most interesting and distinctive application
of disjoint switches is their application to dealing with Null values,
and this would be a useful takeaway of interest for mainstream
programmers.

The Ceylon approach to null values has not gone unnoticed to a more
general programmers audience (e.g., [1]). Disjointness plays a central
role here. In Ceylon, unless specified otherwise, objects cannot have
the null value.  For an object to have the null value it must be
declared to be nullable, e.g., `Integer?`, which can be considered as
syntactic sugar for the union type `Integer | Null`. Disjointness
plays a crucial role in Ceylon's approach as we need to ensure that
values of the Null type are disjoint to values of other objects. The
problem of null is ofcourse a very well-known in mainstream languages.
We think a takeaway of the paper for mainstream programmers is that
union types, disjointness and disjoint switches allow a clean and
simple way to ensure that code that may contain null values checks for
that possibility. Furthermore, there are other applications as briefly
illustrated in the paper.

Although the focus of our paper is not on the applications, but rather
on the formalization of the semantics, we are happy to include more
discussion about relevance in the revision. We will add a simple
extension to our calculi (basically a Unit type with the single value
null) to illustrate this particular application of union types and
disjoint switches further in the paper.

# Changes

We plan todo the following changes to the revision:

1) Add a Unit type to the calculi (with a single value null) and
illustrate the approach to Nullable/Optional types in more detail.

2) Be clearer that while tags are not needed in source expressions,
type annotations are needed at runtime and they play a similar role
to tags there.

3) Clarify that the calculi with intersection types can introduce
non-trivial values with intersection types.

4) Include more discussion about distributivity and algorithmic
subtyping for the calculus in Section 5.2.

5) Add related work on union types.

6) Clarify various confusions and issues with notation pointed
out by the reviewers.

# Detailed Reply

## Review A

### The problem that this paper solves (Question 1)

This paper is focused on the design of elimination forms for union
types. In particular the paper investigates novel elimination forms
based on disjointness of branches. Such elimination forms have not, as
far as we know, been formally studied in the PL theory literature.
We believe such forms are important, as emphasized above.

Technically, we are interested in a solution that enjoys:

a) Type-soundness; b) determinism; c) exclusivity of branches in
switch expressions.

Furthermore, the central notion that is needed for c) to hold is
disjointness. One of the contributions of the paper is also formal
definitions for disjointness (both declarative and algorithmic).
Therefore additional properties that we are interested on are:

d) soundness/completeness of disjointness

We have lemmas in the paper for all the properties above. And we have
fully mechanized the proofs in Coq for those desirable properties.


### Tags and type-directed elimination (Question 2)

We believe there are two different aspects that can be used to
classify union types:

1) Are tags needed to build expressions in the language with union
types?

2) Is some extra information present at runtime (a tag or type) to
help indentifying the origin of the value?

The discussion on tagged vs untagged in the paper is in the sense of
1). Our source expressions do not need tags to build expressions that have union
types, as illustrated in Section 2.

The fact that tags are not present in source expressions creates
quite different challenges for the design of languages, compared to
traditional tagged sum types. In particular, as we explain in both the
Introduction and Section 2, we have to deal with complications that
arise from subtyping and types that can overlap on branches. Language
designs with tagged sum types, do not have such problems. 

While we have a paragraph in Section 2 called "The role of type
annotations in the dynamic semantics" (line 417),
we will make it more clear during revision that our
semantics requires type annotations to be present at runtime. We
believe this is a reasonable approach (and is adopted by many
approaches), as it provides significant flexibility, while ensuring
type safety.

The following table provides an overview of different approaches to
union types:

```
                                  |   C/C++ | Sum types   | Union Types in this paper (and much RW)
-------------------------------------------------------------------------------------------------
Tags for introduction of unions   |   No    | Yes         |     No
-------------------------------------------------------------------------------------------------
Tags or Types present at runtime  |   No    | Yes (Tags)  |     Yes (Types)
```

### Presentation of Two Systems (and Question 3)

There a few reasons for presenting two systems separately:

1) In PL theory papers it is usual to identify minimal calculi with
the essence of the feature. Intersection types are an interesting
feature that often comes paired up with union types, but they can be
viewed as being orthogonal/complementary. Some languages, for example Julia,
support union types but not intersection types (at least as far as we
know). Therefore, the designers of such languages may be interested in
calculi that have disjoint switches but not necessarely intersections.

2) One important point of our work is to establish the relationship to
the line of work on disjoint intersection types. Again, in PL theory
there are many papers that explore the design of new features
but in way that establish a relationship (in this case via duality) to
other more well-studied language features. The formulation of
disjointness in Section 3 is the direct dual of the notion of
disjointness for intersection types from past work. In the system with
union types only, the notion of disjointness can be
viewed as a direct dual to notions that exist in calculi with disjoint
intersection types. If we discarded the calculus in Section 3 and the
first notion of disjointness this connection would not be direct or
obvious.

### Clarification

We thank the reviewer for all the questions regarding the
presentation. We would improve our presentation during revision. We
would like to clarify the following confusions:

> L 429: Is there a difference between A \/ B and A|B ?

There is no difference between `A \/ B` and `A | B`. As we have
explained in L159, in the code examples we write `A | B` since it is a
common notations in many programming languages, while `A \/ B` is more
commonly used in calculi with union types.

> There are two kinds of values: annotated values and unannotated
> lambda expressions ($\lambda x. e$)." This is not consistent with
> Figure 1.

We believe that the description is consistent with Fig 1. In
particular, values are defined in Fig 1 as `v ::= w | \x. e`, where
`w` are _annotated values_ and `\x. e` are unannotated lambda
expressions.

> Figure 2 shows no rule for typing something of the form $\lambda
> x.e : A \to B$.

We would like to point out that our rules can type expressions like
`\x. e: A -> B`. In particular, it is standard in bidirectional type
systems that typing an annotated expression like `e : A` is done by
checking `e` against `A`, and then we can use `Typ-abs` to type-check
the lambda. A concrete example using our rules is:

```
 Typ-var --------------------
          x: Int |- x => Int   Int <: Int
 Typ-sub ----------------------------------
          x: Int |- x <= Int
 Typ-abs ----------------------------------------
          . |- \x. x <= Int -> Int
 Typ-ann --------------------------------------------
          . |- \x. x : Int -> Int => Int -> Int
```

> L 698: $e \Leftrightarrow A$ is not a judgement of Figure 2.

We want to clarify that `e <=> A` is part of a judgment in Figure 2,
as shown in the box of Figure 2. More formally, Figure 1 has given the
following definition, and the corresponding text is in L477-478.

```
<=>  ::=   => | <=
```


## Review B

### Empty types and empty sets

We would like to clarify that by empty types we mean types that have
no values inhabiting them. For instance the Bottom type is
uninhabited. Our LOS definition in Fig 5, provides a way to find a
class of empty types. In essence, we have that:

if |A| = {} then A is an empty type.

So the relationship is the above: if the LOS of a type A is the empty
set, then A is an empty type. We exploit such observation in Section
5.1.

Note that our notation |A| means the LOS of A.


## Review C

### Closed expressions of an intersection type

We would like to point out that there are (non-trivial) values of an
intersection type. For example, we can write overloaded functions
where the match construct can serve the purpose of introducing
intersections:

```
\x . switch x {
         (y : Int) => y+1
         (z : Bool) => if z then 1 else 0
     } : (Int \/ Bool) -> Int : (Int ->  Int) /\ (Bool -> Int)
```

It is also worthwhile noting that, more generally, in calculi with union
and intersection types, elimination/introduction constructs for
union/intersection types can often be dually used to serve as the
introduction/elimination construct for intersection/union types.
For instance, Dunfield [2] notes that her merge operator (which is
primarely presented as a way to introduce values with intersection types)
can also be viewed/used as an elimination form for union types
(see the discussion in the last paragraph of page 7 in the reference
that we provide). 

It would also be possible to extend our system by the following
conventional typing rule to accept more terms of an intersection type
like `\x. x : (Int -> Int) & (Bool -> Bool)`. Although such extension
would be orthogonal to the main contributions of this work.

```
T |- e <= A     T |- e <= B
---------------------------
T |- e <= A & B
```


## Review D

### Declarative specification of λu

We believe that it is simpler to illustrate the key idea by presenting
the declarative specification. In subtyping relations with
distributivity laws, presenting an algorithmic system which eliminates
transitivity is non-trivial, as it cannot be simply dropped.
In our Coq formalization we do have a sound, complete and decidable
algorithmic formulation of the subtyping relation. This is not,
however, a contribution of our work. There are a few algorithms in
previous work that could be employed.

We would be happy to include more discussion about subtyping
distributivity, and the algorithmic system in the revision.

### Related Work

We thank the reviewer for pointing out additional related work on union
types for OO languages. We will incorporate them in the revision.


## Reference

[1] https://blog.jooq.org/2016/03/15/ceylon-might-just-be-the-only-language-that-got-nulls-right/

[2] Jana Dunfield, Elaborating Intersection and Union Types, JFP 2014
(available at https://research.cs.queensu.ca/home/jana/papers/intcomp-jfp/Dunfield14_elaboration.pdf)
