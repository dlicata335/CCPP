# Propositions as types

Last time, we saw the propositions as types correspondence for conjunction (and), implication (if-then), and truth.
Today we will extend this to disjunction, and then learn some Agda basics.

```
module Lect03-starter (P Q R S T : Set) where
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      first : A
      second : B
  open _×_ public

  record Unit : Set where
    constructor <>
```

# Disjunction/Or

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
  example = {!!}
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
  commute∨ = {!!}
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
cases:
```
  example⊥ : Void → R
  example⊥ ()
```
In Agda, write () for the
input that has no values, and then leave off the right-hand side.

# Summary

We've seen that we can represent proofs in propositional logic by programs of a particular type.
The correspondence is
* Conjunction A ∧ B is represented by the tuple type A × B.
* Implication A ⊃ B is represented by the function type A → B.
* Disjunction A ∨ B is represented by the choice type Either A B.
* Truth ⊤ is represented by the one-element type unit.
* Falsehood ⊥ is represented by the empty type void.

# Agda Basics

## Agda commands

The main way to interact with Agda is to leave **holes** in your file.  To type a hole, you can type {!  !}
and then put the cursor in between the {! and the !}.  

For VSCode, see the full list [here][https://github.com/banacorn/agda-mode-vscode].

In general, to instruct Agda to do something, you hold the Control key
while pressing c, and then you hold the Control key while pressing some
other key. We'll write C-<key> to mean "hold Control while pressing
key".  For example, we'll write C-c C-l to mean hold control while
pressing c, then hold control while pressing the l key.

For today we'll need the following commands. 
* C-c C-l, or type >Agda: Load in the command bar [VSCode], or M-x agda2-load [emacs].  This loads the
  current file into Agda.  You will see the types of the holes at the
  bottom. Whenever you edit the file outside of a hole (e.g. adding a function's argument, or adding a new function declaration), you will use this to load the 

* When you're in a hole: C-c C-, or type >Agda: Goal type and context
  (simplified) [VSCode], or M-x agda2-goal-and-context [emacs].  This
  shows you what assumptions you have (the context) and what you're
  trying to prove (the goal).

* When you're in a hole: C-c C-. or type >Agda: Goal type, context, and
  inferred type (simplified) [VSCode], or M-x
  agda2-goal-and-context-and-inferred [emacs].  This shows you what
  assumptions you have (the context) and what you're trying to prove
  (the goal), as well as the type of the program in the hole (what you
  currently have).

* When you're in a hole: C-c C-r or type >Agda: Refine [VScode] or M-x
  agda2-refine [emacs].  This fills the hole with the program that
  you've typed inside the hole.

* When you're in a hole: C-c C-c or type >Agda: Case [VSCode] or M-x
  agda2-make-case [emacs].  Edit the file to pattern-match on the
  variable in the hole, or it will ask you which variable to case on if
  there is nothing in the hole.

## Unicode

Agda accepts Unicode input, not just ASCII.  We'll often use Unicode
math symbols.  To type the logical symbols used in the comments today:
* ⊃ is written \sup
* ∧ is written \wedge
* ∨ is written \vee
* ⊤ is written \top
* ⊥ is written \bot

To type the Agda types
* → is written \to
* × is written ×

## Problems

For each of the following, translate the logical proposition to a type
in the first line, and then prove the proposition by writing a program
of that type in the second line.

## Warm-ups

```
  -- (R ∧ S) ⊃ S
  mysecond : {!!}
  mysecond = {!!}

  -- R ⊃ (R ∨ R)
  duplicate∨ : {!!}
  duplicate∨ = {!!}

  -- R ⊃ (R ∨ R)
  -- give a different proof that the previous task
  duplicate∨2 : {!!}
  duplicate∨2 = {!!}

  -- (R ∨ R) ⊃ R
  collapse : {!!}
  collapse = {!!}
```

## Distributivity of ∨ and ∧

```
  -- (R ∨ (S ∧ T)) ⊃ (R ∨ S) ∧ (R ∨ T)
  distrib∨∧ : {!!}
  distrib∨∧ = {!!}

  -- ( (R ∨ S) ∧ (R ∨ T) ) ⊃ (R ∨ (S ∧ T)) 
  undistrib∨∧ : {!!}
  undistrib∨∧ = {!!}

  -- (R ∧ (S ∨ T)) ⊃ (R ∧ S) ∨ (R ∧ T)
  distrib∧∨ : {!!}
  distrib∧∨ = {!!}

  -- ((R ∧ S) ∨ (R ∧ T)) ⊃ (R ∧ (S ∨ T)) 
  undistrib∧∨ : {!!} 
  undistrib∧∨ = {!!}
```

## Transitivity of implication

Note: you can write an anonymous function (remember fn x => e from SML
or fun x => e in OCaml?) as (\ x → e).  For example, these are the same:

```
  pair : P → (Q → P × Q)
  pair p q = (p , q)

  pair2 : P → (Q → P × Q)
  pair2 p = \ q → (p , q)
```

```
  -- (R ⊃ S) ⊃ (S ⊃ T) ⊃ (R ⊃ T)
  ⊃transitive : {!!} 
  ⊃transitive = {!!}
```

## Distributivity of ⊃ and ∨ 

Try to prove the following and see which one is true and which one is false:

```
  -- ((P ⊃ Q) ∨ (P ⊃ R)) ⊃ (P ⊃ (Q ∨ R)) 
  distrib⊃∨ : {!!}
  distrib⊃∨ = {!!}

  -- (P ⊃ (Q ∨ R)) ⊃ ((P ⊃ Q) ∨ (P ⊃ R)) 
  distrib⊃∨2 : {!!}
  distrib⊃∨2 = {!!}
```

For the one that is false, think about why the type representing the
proofs is not constructable (hint: think about what it means if P,Q,R
are non-propositional types like int, string, bool, etc.).  

## Negation

In other treatments of propositional logic, you probably saw negation (¬
A), which is true when A is false.  We can encode this by the
implication A ⊃ ⊥ (i.e. A implies false), which under propositions as
types is A → Void.

However, this behaves a little different than you may be used to.  For example,
with truth table semantics, A and ¬ (¬ A) are the same.  
Under propositions as types, which of the following can you prove? 

```
  ¬ : Set → Set
  ¬ A = (A → Void)

  double-negation-introduction : R → ¬ (¬ R)
  double-negation-introduction = {!!}

  double-negation-elimination : (¬ (¬ R)) → R
  double-negation-elimination = {!!}
```

Above, you should have distrib⊃∨2 is not provable.  However, you can
prove the following with a double negation.  You might want to name a
couple of lemmas as separate top-level definitions as you do the proof,
since we haven't talked about how to do case analysis except by a named,
top-level pattern-matching function.
```
  -- (P ⊃ (Q ∨ R)) ⊃ ¬ (¬ ((P ⊃ Q) ∨ (P ⊃ R)))
  distrib⊃∨2-doublenegated : (P → (Either Q R)) → ¬ (¬ (Either (P → Q) (P → R)) )
  distrib⊃∨2-doublenegated = {!!}
```

Next week, we will see how the propositions as types principle extends to
quantifiers ∀ and ∃.

