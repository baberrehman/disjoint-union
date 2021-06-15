We thank the reviewers for their insightful and constructive comments. We will
incorporate the reviewers' helpful suggestions in our revision.

## Review A

### The research problem

This paper is focused on the problem of elimination forms
for union types.

- Type-soundness
- determinism
- exclusivity of branches

### Tags and type-directed elimination

Two different aspects to understand union types:

1) Are tags needed to build expressions in the language with union types?

2) Is some extra information present at runtime (a tag or type) to help
indentifying the origin of the value?

We are talking about tagged vs untagged in the sense of 1). Our source
expressions do not need tags to build expressions that have union types.
We illustrate this with examples ...

Our semantics does indeed require types to be present at runtime, we will clarify this.

```
                                  |   C/C++ | Sum types   | Union Types in this paper (and much RW)
-------------------------------------------------------------------------------------------------
Tags for introduction of unions   |   No    | Yes         |     No
-------------------------------------------------------------------------------------------------
Tags or Types present at runtime  |   No    | Yes (Tags)  |     Yes (Type annotations)
```

### Two systems

There are several reasons for presenting two systems separately:

1) In PL Theory papers it is quite usual to identify minimal calculi with the
essence of the feature. Intersection types are an interesting feature that usually comes
paired up with union types, but they can be viewed as orthogonal/complementary.
Some languages, for example Julia, support union types
but not intersection types (at least as far as we know). Therefore, the designers
of such languages may be interested in calculi that have disjoint switches but not necessarely
intersections.

2) One important point of our work is to establish the relationship to the line
of work on disjoint intersection types. Again, in PL theory there are many papers
where people explore the design of new features but in way that establish a
relationship (in this case via duality) to other more well-studied language features.

The formulation of disjointness in Section 3 is the direct dual of the notion
of disjointness for intersection types from past work, and the system with
union types, disjoint switches and the notion of disjointness can be viewed
as duals to notions that exist in calculi with dijoint intersection types.
If we discarded the calculus in Section 3 and the first notion of disjointness
this connection would not so direct or obvious.

(From Ningning: TODO integrate ideas)
I think the replies to the last two weakness points can be something like:

tagged unions are sum types, so you have limited finite possibilities
of a switch of a particular type, while using type-directed we inspect
a value’s runtime type to make the choices. We use “tags” in a strict
way as used in the literature, so type-directed elimination is not
using “tags”. But of course some information is needed during runtime
to really “pick” a specific branch, whether it’s type or something
else

11:52

As unions are usually treated as a dual to intersections, a natural
method to disjoint union is to follow disjoint intersections. We
explore the design space, identify the problems, and make design
decisions, which is in general useful to this line of research

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
we can use `Typ-abs` to type-check the lambda. Specifically,

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

No, it is included by w in the definition of values.



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

We would like to point out that there is closed expressions of an intersection
type. In the first calculus in Section 4, such expressions are admitably
trivial, but they do exist. For example:

```
\x . x+1 : Int -> Int : (Int -> Int) /\ (Int -> Top)
```

For the calculus with distributive subtyping in Section 5.2
we can build more interesting expressions with intersection types.
For example, we can write overloaded functions that have intersection types,
and where the match construct can serve the purpose of introducing intersections:

```
\x . switch x {
         (y : Int) => y+1
         (z : Bool) => if z then 1 else 0
     } : (Int \/ Bool) -> Int : (Int ->  Int) /\ (Bool -> Int)
```

TODO: Study adding

```
T |- e <= A     T |- e <= B
---------------------------
T |- e <= A & B
```

(From Ningning) So we should argue:
- it’s not difficult to do. We have (maybe TODO) added this rule and all our metatheories still hold
- it’s supplementary to our main contributions, i.e., having this rule or not does not change the contributions of this paper


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
