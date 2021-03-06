OOPSLA 2021 Paper #34 Reviews and Comments
===========================================================================
Paper #34 Union Types with Disjoint Switches


Review #34A
===========================================================================

Overall merit
-------------
1. Reject

Review confidence
-----------------
3. High

Paper summary
-------------
The paper presents a version of the simply-typed lambda calculus with
support for untagged union types.  The type system guarantees that in
any eliminator for a union type, the branches are disjoint and
exhaustive-- that is, at run-time, any particular value belongs to one
and only one of the alternatives.

The paper spends a lot of time surveying alternative approaches to
this task; the presented design is based on that found in the Ceylon
programming language.

The paper presents a type system and operational semantics for a
system they call $\lambda_u$.  Safety, preservation, and disjointness
of alternatives are proved. Exhaustiveness follows from the fact that
all unions are binary.

The paper then goes on to present another system which extends
$\lambda_u$ with intersection types.  This requires a different
definition of disjointness, which is a conservative extension of the
first.

Strengths and Weaknesses
------------------------
STRENGTHS:

* The theorems are claimed to have been formalized in Coq.

WEAKNESSES:

* The paper does not make a strong argument for the relevance of its
  problem. 

* The paper does not present a clear statement of its goals, or what
  properties a proposed solution should have.

* The formalism is badly presented; I am not sure whether the
  definitions even make sense as written.

* The paper makes a big distinction between tagged and untagged
  unions, yet the operational semantics of the paper uses "dynamic
  types."  How are these different from tagged unions?

* The paper presents two systems, one that supports intersection
  types, and one that does not.  Why not just use the more powerful
  one?

Comments for author
-------------------
I clearly do not understand what this paper is driving at.  The
comments below represent my best efforts to understand its goals.  I
hope that they at least make my misunderstandings evident to the
authors.

L 169 "Eliminating tagged union types".   I read this as meaning
"here's how you change the language so you don't have to use tagged
union types any more.".   It would be clearer to write "Elimination
forms for tagged union types."  The same ambiguity occurs many times
in the paper.

L 184 "Type-directed elimination of union types" => "Type-directed
elimination forms for union types."

L 210: "according to the different representations of x" => "according
to the different _values_ of x" ?

L 211: "Without overloaded functions the construct would not be very
useful."  The example would be better if it showed an overloading.

L 246-278.  Section 2.2 is getting very long at this point.  Please
get to the point!  Probably some of the material on the preceding page
could also be cut.

Page 7.  Also digressive, except for the diagram at the bottom, which
is key:  it shows an example of a complex system of union types.
Similar diagrams are very helpful in understanding the Julia language,
which probably should be investigated.

L 362-363: "with the help of annotated values."  Aren't these just
tags, which were so deprecated in Section 2.1?

L 407: Definition 2.2 is much clearer than Definition 2.1:  it depends
only on the definition of the basic ("ordinary") values of the
language, rather than on some construct like "bottom-like".

L 429: Is there a difference between A \/ B and A|B ?

L 442: "We opted to...".  Was there any reason for this beyond making
the proofs easier?

L 464: "Values and prevalues".   The paragraph then talks about
"annotated values" and "unannotated values".  Figure 1 talks about
PValues and AValues.  Please be consistent.

"There are two kinds of values: annotated values and
unannotated lambda expressions ($\lambda x. e$)."  This is not
consistent with Figure 1, which lists PValues (which I assume are the
same as Prevalues or unannotated values) that include $i$ (presumably
integers) and things of the form $\lambda x.e : A \to B$.

On the other hand, Figure 2 shows no rule for typing something of the
form $\lambda x.e : A \to B$.  There seems to be some unremediable
confusion here.

L 471: It is difficult to parse $\lambda x.e : A \to B : C \to D$.
(Also in other places, like [Step-Beta]).  Better notation for for
AValue might help.

L 535: Now we have types in bold face, and yet more colons (again in
bold face).  Do these mean something different?

L 634: "A dually annotated lambda value..."  Is "dually annotated"
something new?

L 698: $e \Leftrightarrow A$ is not a judgement of Figure 2.  If you
mean both $\Leftarrow$ and $\Rightarrow$, then say so.  Same issue in
Lemma 4.5

Questions for authors’ response
---------------------------------
1.  What is the problem the paper is trying to solve?  What properties should a solution to that problem have?

2.  How are "dynamic types" different from the tags in tagged unions?

3.  What is the point of including Definition 2.1 and the material
that depends on it, rather than proceeding directly to Definition 2.2
and its consequences?



Review #34B
===========================================================================

Overall merit
-------------
3. Weak accept

Review confidence
-----------------
2. Medium

Paper summary
-------------
At a high level, the paper discusses a
known extension to languages – union types - which is not often
included or well-implemented, re-justifies it, and presents a formal
proof of the extension in lambda calculus.

Union types are inherently complicated because the semantics are
uncertain. The paper does a good job of explaining the problems. It
promotes the Ceylon language (an extension of Java) which employs the
switch construct for union types, enabling overlaps to be statically
rejected. An advantage is that union types can stand in for method
overloading, making for more compact, but still correct, code. They
can also be used for nullable types which are finding their way into
an extension to Scala 3.

Strengths and Weaknesses
------------------------

The first nine pages of the paper are a review of Ceylon’s approach to
union types. The following eleven present a calculus for union types
covering typing, operational semantics and disjointedness. The whole
paper is well written (except see below) and supported by the
literature. The first part of the paper is sound, and is interesting
for a person who works with imperative programming languages. I did
not review the calculus sections.

Comments for author
-------------------

My concern about the paper is its importance. For those interested in
a) details of emerging features of new languages and/or b) proofs in
lambda calculus, the paper serves as an interesting read. But there
are no takeaways. Apart from admiration of good work, what can the
reader take to build on? As a language designer or implementer, I
would like to whether this avenue of work is WORTH it. It has been
lying fallow for quite a long time, and has now been resuscitated by a
few small groups. Some evidence is required in order to support its
value. Are there large systems that have been rewritten with union
types and shown speedup? Is there a trial (even of students) that
shows that union types are easier to write and understand than
overloaded methods? What is the contribution of this work to computer
science at large?

Minor points

- The abstract has several grammar errors (missing articles
  mainly). Please go over it carefully.

- I was confused by the claim in the abstract regarding empty
  types. The text of the paper refers only to the empty set. Where do
  the two converge?

Questions for authors’ response
---------------------------------
I realize that “why” is not the focus of this paper. It is a “what and
how” paper. However, that makes it premature. Are you able to refer to
positive evidence (maybe in Ceylon) as to why it is vital to have
these constructs.



Review #34C
===========================================================================

Overall merit
-------------
2. Weak reject

Review confidence
-----------------
3. High

Paper summary
-------------
The Ceylon language provides union types, whose elimination form
provides case analysis on the run-time types of values.  One notable
feature is that the guard of each branch in a case expression has to
be _disjoint_ with each other, so the order of branches doesn't affect
the semantics of a program.

This paper provides a theoretical foundation for such union types by
studying typed lambda calculi with _disjoint union types_.  The key
finding in this paper is how disjointness of two types should be
defined.  The first definition, which is given as the dual notion of
disjointness in the context of disjoint intersection types (studied by
Oliveira et al.), works for a calculus with function types, union
types, top and bottom types, and subtyping.  However, when the
calculus is extended with intersection types, the definition of
disjointness has to be refined.  The paper shows usual type soundness
(namely, type preservation and progress) and that, despite that the
semantics of case expression allows choosing one of the matching
branches nondeterministically, the semantics is really deterministic,
showing soundness of the disjointness.  The paper also studies
algorithmic formulation of disjointness.

Strengths and Weaknesses
------------------------
Strengths:

* Solid foundation for disjoint union types, which can be an
  interesting point in the design space of programming language with
  the notion of union types.

* The paper is well written, with gentle introduction to the subject
  matter and clear description of the formal development.

* Proofs have been formalized using Coq.

Weaknesses:

* The extension to intersection types looks a bit incomplete.

Comments for author
-------------------
The paper provides a solid foundation for disjoint union types.  I'm
not sure (yet) if disjoint case analysis will be a mainstream language
feature (we probably need more work to learn pros and cons) but
appreciate theoretical investigations of new ideas.  The approach
taken here, namely starting with the dual of disjointness in disjoint
intersection types, is very reasonable and it is nice to see it works.

The paper is overall clearly written and fairly accessible.  I
appreciate the style of writing with carefully chosen example to
understand newly introduced notions.  I didn't run the Coq proof
script but, as far as I understand, the theoretical results are
plausible.

My main concern, however, is in the extension to intersection types.
The refined disjointness is reasonable but the formal calculus looks a
bit incomplete in that it appears to me that it's impossible to
construct a (closed) value of an intersection type.  For example, I'd
expect $\lambda x.x$ could be given type $(Int \to Int) \land (Bool
\to Bool)$ but I have no idea how to derive this type.  So, I don't
see real use of intersection types in this caluclus.

Questions for authors’ response
---------------------------------
* Is there a closed expression of an intersection type?



Review #34D
===========================================================================

Overall merit
-------------
4. Accept

Review confidence
-----------------
3. High

Paper summary
-------------

This work presents a fully mechanised formalization of a calculus of
union types supporting disjoint switches as defined in the Java-like
language Ceylon. Several extensions are considered including
intersection types, a more general rule for bottom types as supported
in Ceylon, and subtyping distributivity. Several interesting
properties are proved including type soundness, and soundness and
completeness of disjointness algorithms

Strengths and Weaknesses
------------------------
PROS
- nice formalization fully mechanised

CONS
- subtyping distributivity should deserve more space in the paper

Comments for author
-------------------

p.1 l.39

"The idea is that a function that takes an argument with a union type
acts similarly to an overloaded function"

This does not allow accurate types for overloaded functions with
different return types; for more accurate typing intersection types
are needed (authors clarify this only later in the paper, anyway I
suggest to add a first comment here)

p.1 l.41

"an integer is returned upon successful computation of the result; and
a string (an error message) is returned if an error happens."

This is not a very principled way to deal with errors, I would prefer
an example based on optional types (which, in the end, are disjoint
union types)

p.5 l.198 
"union type A ∨ B that supports only one branch"
this is not very clear, some more explanation would be useful

p.5 l.240
"so the second branch will never get evaluated!"

some approaches prevent this with a static error similarly as what
happens in Java with catch clauses to handle exceptions

p.6 l.263
"implicit upcasting (e.g., by subtyping)"
I would prefer the term 'static resolution of overloading' 

p.6 l.276
"In such case, we have an ambiguity"

It would worth mentioning that languages as Java and C# statically
reject this example

p.6 l.292
"do not have to exactly match with the types of x" the sentence is a bit ambiguous
since anyway both Integer and Float match Integer|Float
Maybe authors mean "to coincide with"

p.7 l.308
"and the other where the second argument is an integer"

it should be pointed out that the example works because the two
functions return the same type

p.7 l.337
"To illustrate the subtle difference, the diagram on the right presents part of"
usually subtyping arrows have the opposite direction


p.8 l.345
"We can easily encode the safediv function in Section 2.2 in Ceylon:"
optional types would be a better solution (see my previous comment)

p.8 l.367
"Since we were not aware
of previous definitions of disjointness for subtyping relations"
see the suggested references in my comments to the related work

p.8 l.370
"top-like types"
terms as top-like and bottom-like types are a bit misleading: ⊤ and ⊤
∧ ⊤ are two different type expressions denoting the same type (as
happens for expressions and values as 0 and 0*0)

p.9 l.397
"Disjointness in the presence of intersection types"
The given reason is debatable: in many type systems all types which
are not inhabited are equivalent to the bottom type, therefore Int ∧
Bool should be equivalent to ⊥

p.9 l.413
"Since the lowest ordinary subtypes of any type is a
finite set" this applies to nominal types but not to structural types

p.9 l.419
 "there are two different notions: static types and dynamic types."
this concept is shared by all statically typed languages

p.10 l.444
"This considerably simplifies the metatheory,"
I am not conviced about "considerably", the dynamic semantics is more complex, see my following comments

p.10 l.488
"The subtyping relation for λu is reflexive and transitive."
I would specify that the claims have been proved in Coq (applies also to other sentences
in the paper)

p.11, Fig.1
I would point out that rules S-ORB and S-ORC may be incomplete for some type systems

p.14 l.667-675
"Beta value is a function which takes value v [...]"
This paragraph should be clarified with two examples of reduction, for instance
example on p.9 l.434 and the example shown here

p.15 l.705
"This property is not obvious as many
operational semantics rules distinguish between pre-values, values and annotated values."
This is why I have complained about the fact that keeping track of static types makes the dynamic semantics more complex

p.16 l.781
"have a subtype Int ∧ Bool, which is not bottom-like."
Again, in many type systems Int ∧ Bool is equivalent to the bottom type

p.17 l.802
"(2) Additionally, the assumption ..."
This is a weak motivation; in the calculus of Oliveira et al. also Int and Bool are inhabited by
1,,True

p.17 l.828
"(3) A = Int ∧ Bool, B = Int ∨ Bool : There is no ordinary type that is a subtype of both"
this is counter-intuitive and breaks propositional logics where P∧Q is expected to imply
P ∨ Q

p.18 l.859
" Note that LOS is defined as a structurally recursive function and therefore its
decidability is immediate."
This is so because the calculus does not support recursive types

p.19  sect.5.2
Subtyping Distributivity is a non-trivial extension which would deserve more comments, examples and explanations. 

Sect.6 Related Work
I suggest to mention also the following papers which dea with union types for oo languages

Avik Chaudhuri, Panagiotis Vekris, Sam Goldman, Marshall Roch, Gabriel Levi: Fast and precise type checking for JavaScript 

Davide Ancona, Andrea Corradi:
Semantic subtyping for imperative object-oriented languages

Davide Ancona, Andrea Corradi:
Sound and Complete Subtyping between Coinductive Types for Object-Oriented Languages

Ornela Dardha, Daniele Gorla, Daniele Varacca:
Semantic Subtyping for Objects and Classes

Timothy Jones, David J. Pearce:
A Mechanical Soundness Proof for Subtyping Over Recursive Types

Benjamin Chung, Francesco Zappa Nardelli, Jan Vitek:
Julia's Efficient Algorithm for Subtyping Unions and Covariant Tuples (Pearl)

Francesco Zappa Nardelli, Julia Belyakova, Artem Pelenitsyn, Benjamin Chung, Jeff Bezanson, Jan Vitek:
Julia subtyping: a rational reconstruction

Typos
=====

p.18 l.856  
Ordinary subtypes of ⊤ -> Lowest ordinary subtypes of ⊤

p.22 l.1047
In the code example Integer should be Int

p.23 l.1093
Union *and intersection* types also provide

Questions for authors’ response
---------------------------------
Why does sect.5.2 present a declarative version for λu ?
