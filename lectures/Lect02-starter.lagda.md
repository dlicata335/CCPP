
# Propositions as types

In logic, a proposition is something you can prove (e.g. "every number
is even or odd", "the length of append is the sum of the lengths of the
two input lists", "3² = 9").  

In this class, we will discuss an idea that was developed by Brouwer,
Heyting, Kolmogorov, Curry, Howard, Martin-Loef and others in the 1900s.
It's sometimes called the BHK interpretation of logic, or the
Curry-Howard Correspondence.

The idea is **a proposition is the type of its proofs**.  That is, we can
think of logical propositions as types, and proofs of propositions as
programs that have those types.

First, we'll assume some basic ("atomic") propositions P,Q,R, and S.
Think of these as unknown propositions that we don't know anything
about, so they could be instantiated with any proposition you want.
These will be the "base case" from which we generate other propositions.

```
module Lect02-starter (P Q R S T : Set) (x : P) (y : Q) where

```

# And

Suppose A and B are propositions.  Then there is another propsoition A ∧
B ("A and B").  What does the proposition A ∧ B mean?  One answer is a
truth table: when A and B are both true, A ∧ B is true, and otherwise
when one of A and B are false, A ∧ B is false.

Today, we'll provide a different explanation:

* To understand A ∧ B is true is to understand A is true and to understand B is true.
* If you understand A ∧ B is true, you understand A is true.
* If you understand A ∧ B is true, you understand B is true.

You might reasonably object that this doesn't explain much, because to
explain "and" we used a prior notion of "and" when we said "to
understand A" and "to understand B". We're assuming you know how to
understand multiple things.

Next, we take the point of view that a proof of a proposition is
evidence that makes you understand why that proposition is true.

So: 
* A proof of A ∧ B is true is a proof of A together with a proof of B.
* If you have a proof of A ∧ B, you can make a proof of A.
* If you have a proof of A ∧ B, you can make a proof of B.

Let's think about these last two.  If you have a proof of A ∧ B, then
you have both evidence that will convince someone that A is true, and
evidence that will convince someone that B is true, so you can make a
proof that A is true just by forgetting some of that evidence (the proof
of B).  Similarly forgetting the other part of the evidence gives a
proof of B.

Next, we will represent the data of a proof of A ∧ B as a type.

Remember that a type has **values** (how you make elements of that type)
and **operations** (what you can do with elements of that type).  The
values of A ∧ B are supposed to consist of proofs of A together with
proofs of B.  The operations say that given a proof of A ∧ B, we can get
out a proof of A and also get out a proof of B.  So this sounds like the
pair/tuple type A * B in SML/OCaml where a value of a pair type A * B is
  a tuple (a,b) where a:A and b:B.

We need to define this type in Agda. We'll talk about general record
definitions later; for now, just ignore the definition itself, and we'll
talk about its consequences below.
```
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      first : A
      second : B
  open _×_ public
```

Let's suppose we have proofs of the unknown propositions P and Q called
x and y respectively.

Here are some examples of what we can do with the pair type.
```
  proof-of-P-and-Q : P × Q
  proof-of-P-and-Q = {!!}

  proof-of-P-and-P : P × P
  proof-of-P-and-P = {!!}

  proof-of-P-and-P-and-Q : (P × P) × Q
  proof-of-P-and-P-and-Q = {!!}

```

As you can see, to prove P × Q, we give a proof of P (namely x) and a proof of Q (namely y).

Now that we have such proofs, we can use them:

```
  another-proof-of-P : P
  another-proof-of-P = {!!}

  yet-another-proof-of-P : P
  yet-another-proof-of-P = {!!}
```

From a logical perspective, we don't usually think about "which proof of
a proposition" we've given.  But since these are programs, we can **run
the proofs** and see what they do!  Unsurprisingly, we have that
first(a,b) ≡ a and and second(a,b) ≡ b, so both evaluate to x.

# Truth

Let's tell the same story about the always true proposition ⊤.  To
understand ⊤ is true is easy --- it is!  So a proof of ⊤ doesn't need to
supply any data.  In programming terms, this corresponds to a "tuple
with no elements", which we can write like this:

```
  record Unit : Set where
    constructor <>
```

Here's a proof of ⊤:
```
  proof-of-⊤ : Unit
  proof-of-⊤ = {!!}
```

Since there is no data in the unit type, there is nothing you can get out of it.  

We can combine this with ∧; here's a proof of (⊤ ∧ ⊤):
```
  proof-of-⊤∧⊤ : Unit × Unit
  proof-of-⊤∧⊤ = {!!}
```

# Implicaton

Here's where things really get going.

Logically, to prove an implication A ⊃ B (A implies B, or if A then B),
you assume you have a proof of A, and construct a proof of B.

What type does that sound like?  We represent A ⊃ B by the function type
A → B, because to make a function of type A → B, you assume a variable
of type A, and construct a program of type B. The input of type A
represents a proof of A, and the output of type B is the constructed
proof of B.

The operation on function types, function application, says that a
function f : A → B can be applied to an argument x : A to make f(x) : B.
Read logically, this is a rule called *modus ponens*, which says that
from A ⊃ B and A you can deduce B.

Here are some examples.  First, we can prove that R implies R:
```
  identity : R → R
  identity z = {!!}
```

Next, we can prove that R implies Q (remember that we assumed y:Q up above)
```
  constant : R → Q
  constant _ = {!!}
```

Here are Some examples using both implication and conjunction.

First, we prove (R ∧ S) ⊃ (S ∧ R).  Compare the program exchange with
  the following proof: We want to show (R ∧ S) implies (S ∧ R).  So
  assume R ∧ S [this is the variable p].  We need to show S ∧ R, which
  we can do by showing S and R separately [this is the ,]. For the proof
  of S, since we know R ∧ S, we know S [second p].  For the proof of R,
  since we know R ∧ S, we know R [first p].  
```
  -- (R ∧ S) ⊃ (S ∧ R)
  exchange : (R × S) → (S × R)
  exchange p = {!!}
```

Here are a few other examples:
```
  -- R ⊃ (R ∧ R)
  duplicate : R → (R × R)
  duplicate x = {!!}

  -- R ⊃ ⊤ 
  drop : R → Unit
  drop x = {!!}
```

When proving logical statements like this, it's very common to use
higher-order functions (functions that take functions as input; remember
map from COMP212?) to assume an implication.  For example, this says
that implication is transitive:

```
  -- if R ⊃ S and S ⊃ T then R ⊃ T
  compose : (R → S) → (S → T) → (R → T)
  compose f g x = {!!}
```

# Or

Having done conjunction (and) and implication the remaining
propositional logic connective is disjunction (or).

For two propositions A and B, there is a proposition A ∨ B, which is
true when either A is true or B is true.  Thus, to convince you of A ∨
B, I either need to give you a proof of A, or I need to give you a proof
of B.

What can you deduce from knowing or assuming A ∨ B?  Well, you don't if
A is true or B is true, so you need to do a *proof by cases*: if you can
prove some proposition C from A, and you can also prove the same C from
B, then C follows from A ∨ B.

To represent this by a type, we can say that the proposition A ∨ B is
represented by the type Either A B, which is a datatype with two
constructors, one that carries a proof of A, and the other that carries
a proof of B.

```
  data Either (A : Set) (B : Set) : Set where
    Inl : A → Either A B -- pronounced "in left"
    Inr : B → Either A B -- pronounced "in right"
```

As an example of using the constructors, we can prove that R ⊃ (R ∨ S) like this:
```
  example : R → Either R S
  example z = Inl z
```
(While we didn't talk about Either A B in COMP 212, you probably saw the
specific instance 'a option := Either 'a Unit, with constructors SOME :=
Inl and NONE := Inr <>.  You certainly saw Either Unit Unit,
i.e. booleans, with constructors true := Inl <> and false := Inr <>.).

How do we represent a proof by cases?  As a function that
pattern-matches on the possible options.

For example, consider the following proof that (R ∨ S) ⊃ (S ∨ R): Assume
R ∨ S.  We proceed by cases:
* In the first case, we assume R is true.  In this case, S ∨ R is true.
* In the second case, we assume S is true.  In this case, S ∨ R is true.
Here is how this looks as a function:
```
  commute∨ : Either R S → Either S R
  commute∨ = ?
```

Here's an example showing that disjunction and conjunction distribute: 
```
  -- (R ∨ (S ∧ T)) ⊃ (R ∨ S) ∧ (R ∨ T)
  distrib∨∧ : Either R (S × T) → (Either R S) × (Either R T)
  distrib∨∧ = {!!}

  -- ( (R ∨ S) ∧ (R ∨ T) ) ⊃ (R ∨ (S ∧ T)) 
  undistrib∨∧ : ((Either R S) × (Either R T)) → Either R (S × T) 
  undistrib∨∧ = {!!}

  -- (R ∧ (S ∨ R)) ⊃ (R ∧ S) ∨ (R ∧ T)
  distrib∧∨ : R × (Either S T) → (Either (R × S) (R × T))
  distrib∧∨ = {!!}

  -- ((R ∧ S) ∨ (R ∧ T)) ⊃ (R ∧ (S ∨ R)) 
  undistrib∧∨ : (Either (R × S) (R × T)) → R × (Either S T)  
  undistrib∧∨ = {!!}
```

# Falsehood

Just as Unit was the nullary analog of ×, we can make the nullary analog
of Either.  Either is a datatype with two constructors, so here we have
a datatype with zero constructors:

```
  data Void : Set where
```

This represents the false proposition ⊥, because Void is a type with no
values, so ⊥ is a proposition with no proofs.

If we assume falsehood, we can conclude anything by a proof with no
cases: ``` example⊥ : Void → R example⊥ () ``` In Agda, write () for the
input that has no values, and then leave off the right-hand side.

# Negation

In other treatments of propositional logic, you probably saw negation (¬
A), which is true when A is false.  We can encode this by A ⊃ ⊥ (A
implies false), or the type A → Void.

However, this behaves a little different than you may be used to.  For example,
with truth table semantics, A and ¬ (¬ A) are the same.  
Here, we can prove that A implies ¬ ¬ A.  

```
  double-negation-introduction : R → ((R → Void) → Void)
  double-negation-introduction x f = {!!}
```

But we can't prove the converse:
```
  double-negation-elimination : ((R → Void) → Void) → R
  double-negation-elimination h = {!!}
```

double-negation-elimination is the principle of "proof by
contradiction": to prove R, we assume not R (i.e. R ⊃ ⊥), and derive a
contradiction.

The reason is that this principle is not *constructive*, i.e. we cannot
exhibit direct evidence for A from a proof by contradiction.  It is
possible to add proof by contradiction to the propositions-as-types
logic, but it's not a basic feature.  

# Summary

Today we've seen that we can represent proofs in propositional logic by programs of a particular type.
The correspondence is
* Conjunction A ∧ B is represented by the tuple type A × B.
* Implication A ⊃ B is represented by the function type A → B.
* Disjunction A ∨ B is represented by the choice type Either A B.
* Truth ⊤ is represented by the one-element type unit.
* Falsehood ⊥ is represented by the empty type void.

Next time, we will see how this extends to quantifiers ∀ and ∃.  
