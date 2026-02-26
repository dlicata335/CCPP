# Propositions as types

Last time, we saw the propositions as types correspondence for conjunction (and), implication (if-then), and truth.
Today we will extend this to disjunction, and then learn some Agda basics.

```
module Lect03 (P Q R S T : Set) where
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
  commute∨ (Inl r) = Inr r
  commute∨ (Inr s) = Inl s
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
  mysecond : (R × S) → S
  mysecond p = second p

  -- R ⊃ (R ∨ R)
  duplicate∨ : R → (Either R R)
  duplicate∨ x = Inl x

  -- R ⊃ (R ∨ R)
  -- give a different proof that the previous task
  duplicate∨2 : R → (Either R R)
  duplicate∨2 x = Inr x

  -- (R ∨ R) ⊃ R
  collapse : Either R R → R
  collapse (Inl x) = x
  collapse (Inr x) = x
```

We didn't get to the rest of the lab problems in class, so they are moved to Homework 01.

Next week, we will see how the propositions as types princple extends to
quantifiers ∀ and ∃.

