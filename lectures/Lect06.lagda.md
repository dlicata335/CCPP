```
module Lect06 where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  data Either (A B : Set) : Set where
    Inl : (x : A) → Either A B
    Inr : (y : B) → Either A B

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

  -- existential quantifier
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field   
      first : A
      second : B first
  open Σ public
  infixr 10 _,_

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B

  -- lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  infixr 99 _::_ 

  -- end library code

  -- ----------------------------------------------------------------------
  -- code from lecture/HW

  double : Nat → Nat
  double Z = Z
  double (1+ n) = 1+ (1+ (double n))

  Equals : Nat → Nat → Set
  Equals Z Z = Unit
  Equals Z (1+ n) = Void
  Equals (1+ n) Z = Void
  Equals (1+ n) (1+ m) = Equals n m

  mutual
    Even : Nat → Set
    Even Z = Unit
    Even (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd Z = Void
    Odd (1+ n) = Even n

  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity Z = Inl <> -- type checks because Even 0 = Unit
  parity (1+ n) = swap (parity n) where
    swap : Either (Even n) (Odd n) → Either (Odd n) (Even n)
    swap (Inl nIsEven) = Inr nIsEven
    swap (Inr nIsOdd) = Inl nIsOdd
  
  -- HW problem
  postulate
    refl : (n : Nat) → Equals n n
    sym : (n m : Nat) → Equals n m → Equals m n
```

# Lists
  
Lists are defined by a datatype with two constructors, [] and ::.  
E.g. the list [1,2,3] would be written  
1 :: (2 :: (3 :: []))  
or 1 :: 2 :: 3 :: []  

Here's a function defined by recursion on a list:

```
  addone : List Nat → List Nat
  addone [] = []
  addone (x :: xs) = 1+ x :: addone xs
```

# Linear Search 

First, we define booleans and options as special cases of Either:

```
  Bool : Set
  Bool = Either Unit Unit
  
  True False : Bool
  True = Inl <>
  False = Inr <>

  not : Bool → Bool
  not (Inl <>) = False
  not (Inr <>) = True

  Maybe : Set → Set
  Maybe A = Either A Unit

  Some : ∀ {A} → A → Maybe A
  Some x = Inl x

  None : ∀ {A} → Maybe A
  None = Inr <>

```

The linear search algorithm finds an element in a list/array by looping
over the entire data structure until it finds one.  Here, we will linear
search for an even number in a list of numbers.  Here's a standard
implementation:

```
  is-even : Nat -> Bool
  is-even Z = True
  is-even (1+ n) = not (is-even n) 

  find-even : List Nat → Maybe Nat
  find-even [] = None
  find-even (x :: xs) = case (is-even x) where
    case : Bool → Maybe Nat
    case (Inl <>) = Some x
    case (Inr <>) = find-even xs
```

What kind of bugs might we make in this code?

```
  module Buggy where
```

First, the function might fail to return an even number, e.g. by
flipping the true and false cases:

```
    find-even1-bug : List Nat → Maybe Nat
    find-even1-bug [] = None
    find-even1-bug (x :: xs) = case (is-even x) where
      case : Bool → Maybe Nat
      case (Inl <>) = find-even1-bug xs
      case (Inr <>) = Some x
```

Next, the function might return an even number, but not one that is in
the list:
```
    find-even2-bug : List Nat → Maybe Nat
    find-even2-bug [] = None
    find-even2-bug (x :: xs) = case (is-even x) where
      case : Bool → Maybe Nat
      case (Inl <>) = Some x
      case (Inr <>) = Some 2
```

Third, the function might fail to return an even number when there is in
fact one in the list:

```
    find-even3-bug : List Nat → Maybe Nat
    find-even3-bug [] = None
    find-even3-bug (x :: xs) = find-even3-bug xs
```

In what follows, we will refine the type of find-even to make these bugs
impossible.

# Verifying result is even 

To do this, we'll use our first example of an existential type.
∃ x : Nat. P[x] is written Σ[ x ∈ Nat ] P[x].  Values are pairs of an n
such that P[n] is true.  Use first and second or pattern-matching to get
out the witness/proof.

Using this, we define a type of even numbers as a pair of a number with
a proof that it is even:

```
  EvenNumber : Set
  EvenNumber = Σ[ x ∈ Nat ] Even x

  two : EvenNumber
  two = (2 , <>)

  three : EvenNumber
  three = (3 , {!impossible!})
```

Here's a first attempt: 

```
  find-even1 : List Nat → Maybe EvenNumber
  find-even1 [] = None
  find-even1 (x :: xs) = case (is-even x) where
    case : Bool → Maybe EvenNumber
    case (Inl <>) = Some (x , {!didn't remember enough!})
    case (Inr <>) = find-even1 xs
```

Unfortunately, casing on is-even doesn't give us enough information.  In
princple, knowing that (is-even x) is equal to the true boolean should
tell us that the proposition Even x is true.  We could prove this, but
instead we can just use the more informative parity function in place of
is-even to get the information we want:

```
  find-even1' : List Nat → Maybe EvenNumber
  find-even1' [] = None
  find-even1' (x :: xs) = case (parity x) where
    case : Either (Even x) (Odd x) → Maybe EvenNumber
    case (Inl e) = Some (x , e)
    case (Inr o) = find-even1 xs
```

Now, if we try to make the same bug as in find-even1 above, we can't
finish the code, because we can't prove that x is even in the odd case:

```
  find-even1-nobug : List Nat → Maybe EvenNumber
  find-even1-nobug [] = None
  find-even1-nobug (x :: xs) = case (parity x) where
    case : Either (Even x) (Odd x) → Maybe EvenNumber
    case (Inl e) = find-even1-nobug xs
    case (Inr o) = Some (x , {! this is false!})
```

# Also verifying membership

Next, we'll try to fix the bug from find-even2-bug above.  

The predicate In n l means that the number n is in the list l.
Informally:  
* n is not in []  
* n is in x :: xs iff n = x or n is in xs  

```
  In : Nat → List Nat → Set
  In n [] = Void
  In n (x :: xs) = Either (Equals n x) (In n xs)
```

This time, we can define "an even number that is in the list l" as the
following extended subset type:

```
  EvenNumberIn : List Nat → Set
  EvenNumberIn l = Σ[ x ∈ Nat ] ((Even x) × (In x l))
```

Now we can start to write a more precisely typed version of find-even:

```
  find-even2 : (l : List Nat) → Maybe (EvenNumberIn l)
  find-even2 [] = None
  find-even2 (x :: xs) = case (parity x) where
    case : Either (Even x) (Odd x) → Maybe (EvenNumberIn (x :: xs))
    case (Inl e) = Some (x , e , Inl (refl x))
    case (Inr o) = {! (find-even2 xs) !}
```

We'll finish the Inr case next time.  

If we try to make the bug from find-even2-bug above, we get stuck and can't
finish the proof:

```
  find-even2-nobug : (l : List Nat) → Maybe (EvenNumberIn l)
  find-even2-nobug [] = None
  find-even2-nobug (x :: xs) = case (parity x) where
    case : Either (Even x) (Odd x) → Maybe (EvenNumberIn (x :: xs))
    case (Inl e) = Some (x , e , Inl (refl x))
    case (Inr o) = Some (2 , <> , {! don't know this!})
```


