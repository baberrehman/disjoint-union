We thank the reviewers for their insightful and constructive comments. We will
incorporate the reviewers' helpful suggestions in our revision.

## General

## Relevance/Importance of the problem

Reviewers A and B have concerns regarding the relevance/importance of
this work. Importance is indeed one of the 4 typical criteria employed
to evaluate research papers. Here is what OOPSLA states regarding
importance in its paper selection criteria:

*Importance: The paper contributes to the advancement of knowledge
in the field. We also welcome papers that diverge from the dominant
trajectory of the field.*

(From: https://2021.splashcon.org/track/splash-2021-oopsla#Call-for-Papers)

We believe that it is useful to answer two questions here:

1) Are union types relevant in practice?  (Reviewer B questions the
relevance of union types in general, are programmers using them,
etc.)

2) Is the particular approach presented here with disjoint switches
relevant?

Regarding 1) we believe that the fact that many major programming
languages such as Scala 3, TypeScript, Flow or Julia all implement
some form of union types is already providing some evidence of the
practical relevance of union types.

We have also conducted a set of small google queries to investigate
the extent of programmers are using union types, and comparing union types
with some other features.  We performed the following google queries,
and got the following results (in our machine):

```
Google query                                | number of results
---------------------------------------------------------------
"union type" site:stackoverflow.com         | 6990
"intersection type" site:stackoverflow.com  | 746
"gradual typing" site:stackoverflow.com     | 144
"dependent type" site:stackoverflow.com     | 2760
```

The queries search on stackoverflow questions that mention some
programming language features that are not yet available in mainstream
languages like Java or C\#, but are available in some other widely
used languages (and are also hot topics in PL research at the
moment). Somewhat to our surprise union types actually have the
largest number of results. From a quick look at the first 20 pages,
most questions are done by TypeScript programmers. We believe that
this provides some evidence that union types are being used in practice to a
significant extent (at least in TypeScript).

Regarding 2) We first wish to point out part of what the call for papers
states regarding importance:

"We also welcome papers that diverge from the dominant trajectory of the field."

Our approach, based on disjointness, does indeed diverge in some ways
from the approaches to union types that are taken in TypeScript or
Flow, which can be viewed as the more dominant approaches to union
types. In our paper, we make some arguments as to why an approach with
disjoint switches is worth considering. For example, they can be an
easier to reason alternative to certain forms of overloading; or they
can be used for dealing with failure in various way. Reviewer B
concretely asks about takeaways, and for positive evidence why the
constructs in our paper are useful. We believe that the most
interesting and distinctive application of disjoint switch is their
application to dealing with Null values, and this would be
a useful takeaway of interest for mainstream programmers.

Such application relies of disjointness and cannot be emulated by
union types a la TypeScript (for example). In Ceylon, unless
specified otherwise, objects cannot have the null value. For an
object to have the null value it must be declared to be nullable. For
example:

```Integer x = null;```

is a type-error in Ceylon. If we wish to have objects that are null,
we have to use optional types. With optional types, the following is allowed:

```Integer? x = null;```

An optional type `Integer?` is just syntactic sugar for the
union type `Integer|Null`. The eliminators of union types then
become relevant to use such union types, since to use a value
of type `Integer|Null` we must check whether we get null or an integer.

As the reviewer may imagine, optional types and eliminators
for those optional types are quite pervasibly used in Ceylon.
Thus everytime we use null, we are using union types in Ceylon.

## Review A

### The problem we solve and Question 1)

This paper is focused on the problem of elimination forms for union
types. In particular the paper investigates elimination forms based
on disjointness of branches. Such elimination forms have not, as far
as we know, been formally studied in the PL theory literature. The
technical properties that a solution should have are:

a) Type-soundness;
b) determinism;
c) exclusivity of branches in switch expressions.

We have lemmas in the paper for the 3 properties above. For c)
the relevant lemma is Lemma 3.10. Furthermore, the central
notion that is needed for c) to hold is disjointness.
One of the contributions of the paper is also formal definitions
for disjointness (both declarative and algorithmic). Therefore
2 additional properties that we are interested on are:

d) soundness/completeness of disjointness

(we also have proofs for d)).

### Tags and type-directed elimination and Question 2)

There are two different aspects that can be used to classify union types:

1) Are tags needed to build expressions in the language with union types?

2) Is some extra information present at runtime (a tag or type) to help
indentifying the origin of the value?

We are talking about tagged vs untagged in the sense of 1). Our source
expressions do not need tags to build expressions that have union types.
We illustrate this with examples in Section 2. For instance:

FILL ME

Our semantics does indeed require type annotations
to be present at runtime, we will clarify this.

```
                                  |   C/C++ | Sum types   | Union Types in this paper (and much RW)
-------------------------------------------------------------------------------------------------
Tags for introduction of unions   |   No    | Yes         |     No
-------------------------------------------------------------------------------------------------
Tags or Types present at runtime  |   No    | Yes (Tags)  |     Yes (Type annotations)
```

### Two systems; Why not just use the more powerful
  one? and Question 3)

There a few reasons for presenting two systems separately:

1) In PL theory papers it is usual to identify minimal calculi with
the essence of the feature. Intersection types are an interesting
feature that usually comes paired up with union types, but they can be
viewed as orthogonal/complementary. Some languages, for example
Julia, support union types but not intersection types (at least as far
as we know). Therefore, the designers of such languages may be
interested in calculi that have disjoint switches but not necessarely
intersections.

2) One important point of our work is to establish the relationship to
the line of work on disjoint intersection types. Again, in PL theory
there are many papers where people explore the design of new features
but in way that establish a relationship (in this case via duality) to
other more well-studied language features.

The formulation of disjointness in Section 3 is the direct dual of the notion
of disjointness for intersection types from past work. The system with
union types, disjoint switches and the notion of disjointness can be viewed
as duals to notions that exist in calculi with dijoint intersection types.
If we discarded the calculus in Section 3 and the first notion of disjointness
this connection would not so direct or obvious.

### Clarification

We thank the reviewer for all the questions regarding the presentation. We would
improve our presentation during revision. We would like to clarify the following
confusions:

> L 429: Is there a difference between A \/ B and A|B ?

There is no difference between `A \/ B` and `A | B`. As we have explained in
L159, in the code examples we write `A | B` since it is a common notations in
many programming languages, while `A \/ B` is more commonly used in formalism
of union calculi.

> There are two kinds of values: annotated values and unannotated lambda
> expressions ($\lambda x. e$)." This is not consistent with Figure 1.

We would like to clarify that the description is consistent with Fig 1. In
particular, values are defined in Fig 1 as `v ::= w | \x. e`, where `w` is
_annotated values_ and _\x. e_ are unannotated lambda expressions.

> Figure 2 shows no rule for typing something of the form $\lambda x.e : A \to
> B$.

We would like to point out that our rules can type expressions like `\x. e: A -> B`.
In particular, it is standard in bidirectional type systems that typing an
annotated expression like `e : A` is done by checking `e` against `A`, and then
we can use `Typ-abs` to type-check the lambda. A concrete example using our rules is:

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

We want to clarify that `e <=> A` is part of a judgment in Figure 2, as shown in
the box of Figure 2. More formally, Figure 1 has given the following definition,
and the corresponding text is in L477-478.

```
<=>  ::=   => | <=
```


### Minor

NINGNING: I don't think we need to answer all of them. But if we do, put this
part at the end of the reply.

- L 211: "Without overloaded functions the construct would not be very
useful."  The example would be better if it showed an overloading.

We do not show the definition of `show`, but the point is that show would be
on overloaded function with two implementations. For instance, we could have:

function show (x: String) = x
function show (x: Int) = show(x/10) ++ [ digit2Char(x%10) ]


- L 535: Now we have types in bold face, and yet more colons (again in
bold face).  Do these mean something different?

No, the bold face is just highlighting the examples, and the colon is a punctiation mark
in this case.

- L 634: "A dually annotated lambda value..."  Is "dually annotated"
something new?

No, it just means "A lambda value with 2 type annotations".


## Review B

### Importance

NINGNING: actualy, I think we should have a `## Motivation` or maybe (`##
Contributions`) at the very top of the reply before individual answers to each
reviewer. In that part we should try to answer `the research problem` from
review A and also the `importantce of this area` from review B

## not sure

- I realize that “why” is not the focus of this paper. It is a “what and
how” paper. However, that makes it premature. Are you able to refer to
positive evidence (maybe in Ceylon) as to why it is vital to have
these constructs.

## Empty types and empty sets

We would like to clarify that by empty types we mean types that have no values
inhabiting them. For instance the Bottom type is uninhabited. Our LOS definition
in Fig 5, provides a way to find a class of empty types. In essence, we have
that:

if   |A| = {}   then A is an empty type.

So the relationship is the above: if the LOS of a type A is the
empty set, then A is an empty type. We exploit such observation in
Section 5.1.

Note that our notation |A| means the LOS of A.


## Review C

### Closed expressions of an intersection type

We would like to point out that there are some values of an intersection
type. For example, we can write overloaded functions where the match construct
can serve the purpose of introducing intersections:

```
\x . switch x {
         (y : Int) => y+1
         (z : Bool) => if z then 1 else 0
     } : (Int \/ Bool) -> Int : (Int ->  Int) /\ (Bool -> Int)
```

It would also be possible to extend our system by the conventional typing rule

```
T |- e <= A     T |- e <= B
---------------------------
T |- e <= A & B
```

to accept more terms of an intersection type

```
\x. x : (Int -> Int) & (Bool -> Bool)
```

But it does not really change the expressiveness, since the typing rule of
function application requires the function to have an arrow type.



## Review D

- p.9 l.397
"Disjointness in the presence of intersection types"
The given reason is debatable: in many type systems all types which
are not inhabited are equivalent to the bottom type, therefore Int ∧
Bool should be equivalent to ⊥

We agree that this depends on what systems you are considering,
and we get back to this matter later on in the paper.
In particular, one of the extensions that we consider,
in Section 5.1, will indeed make `Int /\ Bool` equivalent to Bottom.

- "(2) Additionally, the assumption ..."
This is a weak motivation; in the calculus of Oliveira et al. also Int and Bool are inhabited by
1,,True

Similarly to the previous answer, we want to emphasize that in the
paper we have also formalized a variant where Int /\ Bool are
equivalent to bottom. See Section 5.1.

- p.19 sect.5.2 Subtyping Distributivity is a non-trivial extension
which would deserve more comments, examples and explanations.

For the final version we will dedicate more space to distributivity, with more
examples and a discussion about the algorithmic aspects.

- Sect.6 Related Work
I suggest to mention also the following papers which dea with union types for oo languages

Thank you for the suggestions. We will look into the papers.


- Why does sect.5.2 present a declarative version for λu ?

The rules for the declarative version of subtyping are much simpler than
the algorithmic formulation. In subtyping relations with distributivity laws,
transitivity elimination is non-trivial (we cannot simply drop the transitivity rule).

Our Coq formalization comes with a formalization of a sound and complete algorithm
as well (which is not a contribution of our paper, but rather from a paper
that has just been conditionaly accepted at ICFP). But there are also a few
other algorithms in previous that could be employed.

In short, because the declarative rules are simpler, and the algorithmic formulation
that we use in Coq is not a contribution of this paper, we just present the declarative
formulation.

However, for the revision of the paper we will talk more about the algorithmic
formulation.
