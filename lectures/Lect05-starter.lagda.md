
In this class, you will practice recursion and induction.  

```
module Lect05-starter where
  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  -- pairs
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      first : A
      second : B
  open _×_ public

  record Unit : Set where
    constructor <>

  data Void : Set where

  abort : ∀ {C : Set} → Void → C
  abort ()
```

# Some examples from Lecture 4.

Type them in with me.

```
  double : Nat → Nat
  double = {!!}

  mutual
    Even : Nat → Set
    Even = {!!}
  
    Odd : Nat → Set
    Odd = {!!}

  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity = {!!}

  test = parity 9
```

You can do C-c C-n (>Agda: Compute Normal Form) to run tests.  For
example, do C-c C-n, then type test, and then type enter, and you should
see whether 9 is even or odd (Inl <> means even, Inr <> means odd).

# Curried functions

One way to represent a multi-input function is by making the function
take a pair of inputs:

```
  plus : Nat × Nat → Nat
  plus (Z , y) = y
  plus (1+ x , y) = 1+ (plus (x , y)) 
```

However, the idomatic way to do multi-input functions in Agda is using
  "curried" functions (named after a mathematician named Haskell Curry)
  instead:
```
  plus-curried : Nat → Nat → Nat
  plus-curried Z y = y
  plus-curried (1+ x) y = 1+ (plus-curried x y)
```

If you want, you can see this as notation for a 2-input function:

* To write a 2-input function's type, you write A → B → C, which means
  that A and B are inputs and C is the output.

* To use f : A → B → C, you write f x y, with the x and y as the
  inputs. If x and y are complicated expressions, write f (e1) (e2) to
  group the inputs appropriately. For example
  plus-curried (plus-curried 1 2) (plus-curried 3 4)
  is the same as
  plus( plus(1,2) , plus(3,4)).  

Formally, a Curried function type is a right-associated nesting of the
function type, i.e. Nat → Nat → Nat means Nat → (Nat → Nat).  So you can
also **partially apply** a function to specify one input but not the
other.  For example, (plus 3) : Nat → Nat is the function that adds 3 to its input.  

## Problem 1

The following propositions are analogous to some of the homework
problems, but they are curried here, whereas the homework problems are
uncurried.  Prove these versions:
```
  module Logic (P Q R S T : Set) where
    -- R ⊃ (S ∨ T) ⊃ ((R ∧ S) ∨ (R ∧ T))
    distrib∧∨-curried : R → (Either S T) → (Either (R × S) (R × T))
    distrib∧∨-curried = {!!}

    -- P ⊃ Q ⊃ R ⊃ (P ∧ (Q ∧ R)), which means P ⊃ (Q ⊃ (R ⊃ (P ∧ (Q ∧ R))))
    make-pair : P → Q → R → (P × (Q × R)) 
    make-pair = {!!}
```

# Less than or equal to

The type n ≤ m is supposed to represent proofs that n is less than or
equal to m, analogously to how Even n and Odd n represent proofs that n
is even or odd.  Define n ≤ m as a function that computes a type (Set)
by recursion on n and m.

```
  _≤_ : Nat → Nat → Set
  n ≤ m = {!!}
```

Prove that ≤ is reflexive, i.e. every number is less than or equal to itself.

```
  ≤-refl : (x : Nat) → x ≤ x 
  ≤-refl x = {!!}
```

Prove that ≤ is transitive, i.e. if x ≤ y and y ≤ z then x ≤ z.

```
  ≤-trans : (x y z : Nat) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z p q = {!!}
```

Prove the following theorem about the double function, which says that
doubling a number only makes it bigger.  You will need to state and
prove a lemma about ≤ (try doing the proof of the theorem and see what
you need to know).

```
  double-≤ : (x : Nat) → x ≤ double x
  double-≤ x = {!!}
```

# More logic puzzles.

```
  module Puzzles (P Q R S T : Set) where
```

In this problem, you will get some practice with anonymous functions,
which you might remember as fn x => e in SML or OCaml.  An anonymous
function is a function without a name.  In Agda, anonymous functions are
written λ x → e, where x is the variable for the function's input, and e
is the body of the function.  For example, λ x → 1+ (double (1+ x)) is
the function that sends x to 1 + 2*(x+1).
```
    anon : Nat → Nat
    anon = λ x → 1+ (double (1+ x))
```

One place where anonymous functions are used is when constructing a
value of a type that includes a function type nested inside of another
type constructor like × or Either.  For example, on the homework, you
are proving ((P ⊃ Q) ∧ (P ⊃ R)) ⊃ (P ⊃ (Q ∧ R)).  What if we do the
converse?

```
    -- (P ⊃ (Q ∧ R)) ⊃ ((P ⊃ Q) ∧ (P ⊃ R))
    distrib⊃∧2 : (P → (Q × R)) → ( (P → Q) × (P → R) )
    distrib⊃∧2 f = ( (λ p → first (f p)) , (λ p → second (f p)) )
```

We need to output two functions together in a pair, so it is natural to
write them as anonymous functions.  We also could write them as named
local helper functions.

```
    -- (P ⊃ (Q ∧ R)) ⊃ ((P ⊃ Q) ∧ (P ⊃ R))
    distrib⊃∧2-again : (P → (Q × R)) → ( (P → Q) × (P → R) )
    distrib⊃∧2-again f = ( first-function , second-function ) where
      first-function : P → Q
      first-function p = first (f p)
      
      second-function : P → R
      second-function p = second (f p)
```

## Problem 1

Prove the following proposition under propositions as types:
```
    -- ((P ∨ Q) ⊃ R) ⊃ ( (P ⊃ R) ∧ (Q ⊃ R))
    distrib⊃∨1 : {!!}
    distrib⊃∨1 = {!!}
```

## Problem 2

Translate the type (P → (Either Q R)) → (Either (P → Q) (P → R)) to a proposition.  Think about whether
that proposition should be provable, using whatever intuitions you have
from previous mathematical experience.

Next, think about whether you can write a function of this type.  Does
it makes sense for a function of this type to exist if P,Q,R are
datatypes like Nat, String, List.  You can try to fill in a proof here:

```
    distrib⊃∨2 : (P → (Either Q R)) → (Either (P → Q) (P → R)) 
    distrib⊃∨2 = {!!}
```

Prove the following modified version: 
```
    ¬ : Set → Set
    ¬ A = A → Void

    distrib⊃∨2' : (P → (Either Q R)) → ¬ (¬ (Either (P → Q) (P → R)) )
    distrib⊃∨2' = {!!}
```

What does this all mean about the propositions as types principle?  
