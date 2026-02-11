
```
module Lect07-starter where

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
  EvenNumber = {!!}

  two : EvenNumber
  two = {!!}

  three : EvenNumber
  three = {!!}
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
  find-even1' = {!!}
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
  In n l = {!!}
```

This time, we can define "an even number that is in the list l" as the
following extended subset type:

```
  EvenNumberIn : List Nat → Set
  EvenNumberIn l = {!!}
```

Here's a lemma that we will need below:

```
  in-:: : (x : Nat) (xs : List Nat) → EvenNumberIn xs → EvenNumberIn (x :: xs)
  in-:: = {!!}
```

Now we can write a more precisely typed version of find-even:

```
  find-even2 : (l : List Nat) → Maybe (EvenNumberIn l)
  find-even2 l = {!!}
```

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

What is find-even2 computing?  Run these by doing C-c C-n (>Agda:
Normalize) and think about it.

```
  find-even2-test0 = find-even2 (2 :: (3 :: (4 :: [])))
  find-even2-test1 = find-even2 (1 :: (2 :: (3 :: (4 :: []))))
  find-even2-test2 = find-even2 (7 :: (1 :: (2 :: (3 :: (4 :: [])))))
  find-even2-test3 = find-even2 (9 :: (7 :: (1 :: (2 :: (3 :: (4 :: []))))))
  find-even2-test4 = find-even2 (11 :: (13 :: (9 :: (7 :: (1 :: (2 :: (3 :: (4 :: []))))))))
```

A proof of In x l is a weird way of writing the *position* of x in l,
where Inr (Inr (Inr ... (Inl _))) means that it is in position k where k
is the number of Inr's (indexing starting with 0).

# Also verifying correctness of the false case

The final piece is to check that the function doesn't miss any even
numbers and return None when there is an even number in the list. To do
this, we define a predicate meaning that every number in the list is
odd:

```
  AllOdd : List Nat → Set
  AllOdd = {!!}
```

```
  find-even3 : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
  find-even3 l = {!!}
```

Logically, this type corresponds to the statement, "for every list l,
either there is an even number in l, or all of the numbers in l are
odd".  Computatonally, linear search is one program that proves this
theorem.

# Extrinsic verifcation

The above is an example of what is called "intrinsic verification": the
code and the proof are the same function, with a fancy type.

We can also check the same specification using "extrinsic verification",
where you separately prove a property of an existing piece of code.  

To simplify one aspect of the proof, we'll rewrite find-even so that it
uses parity in place of the boolean-valued is-even:

```
  is-even' : Nat -> Bool
  is-even' n with parity n
  ... | Inl _ = True
  ... | Inr _ = False

  find-even' : List Nat → Maybe Nat
  find-even' [] = None
  find-even' (x :: xs) = case (is-even' x) where
    case : Bool → Maybe Nat
    case (Inl <>) = Inl x
    case (Inr <>) = find-even' xs
```

To state the specifications, we need equality for Maybe Nat:

```
  EqualM : Maybe Nat → Maybe Nat → Set
  EqualM (Inl x) (Inl y) = Equals x y
  EqualM (Inl x) (Inr y) = Void
  EqualM (Inr x) (Inl y) = Void
  EqualM (Inr x) (Inr y) = Unit
```

This lemma says that Even-ness respects equality (more on this idea
soon):

```
  transport-Even : (x y : Nat) → Even x → Equals x y → Even y
  transport-Even Z Z e eq = <>
  transport-Even (1+ (1+ x)) (1+ (1+ y)) e eq = transport-Even x y e eq
```

First, we can prove that if find-even returns Some(y) then that y is
even and in the list.  'with' is a new Agda syntax.  Here, it is used to
case on parity x in the proof, in a way that causes the corresponding
case on parity x in the code for find-even' to run.

You can use C-u C-c C-, to see the original goal and then think through what Agda did in each case.  

```
  findeven-even : (l : List Nat) (y : Nat)
                → EqualM (find-even' l) (Some y)
                → Even y
  findeven-even [] y issome = {!!}
  findeven-even (x :: xs) y issome with parity x
  ... | Inl e = {!!}
  ... | Inr o = {!!}
```

Next, we can prove that if find-even' returns Some, then the number it
returns is in the list l:

```
  findeven-in : (l : List Nat) (y : Nat)
              → EqualM (find-even' l) (Some y)
              → In y l
  findeven-in (x :: xs) y eq with parity x
  ... | Inl e = {!!}
  ... | Inr o = {!!}
```

Next, we can prove that if there is some even number in the list, then
find-even returns an even number in the list:

```
  complete' : (l : List Nat) (y : Nat)
           → (Even y)
           → (In y l)
           → Σ[ n ∈ Nat ] EqualM (find-even' l) (Some n)
  complete' = {!!}

```

This can be summarized as follows:

```
  findeven-sound : (l : List Nat)
                 → (Σ[ y ∈ Nat ] EqualM (find-even' l) (Some y))
                 → (Σ[ y ∈ Nat ] ((Even y) × (In y l)))
  findeven-sound l (y , eq) = (y , findeven-even l y eq , findeven-in l y eq)

  findeven-complete : (l : List Nat)
                 → (Σ[ y ∈ Nat ] ((Even y) × (In y l)))
                 → (Σ[ y ∈ Nat ] EqualM (find-even' l) (Some y))
  findeven-complete l (y , even , inlist) = complete' l y even inlist 
```

I.e. find-even' l returns Some exactly when there is some odd number in l.  

This fully characterizes the behavior of find-even' because you can prove that  
¬ (Σ[ y ∈ Nat ] EqualM (find-even' l) (Some y)) is the same as EqualM (find-even' l) None  
and that ¬ (Σ[ y ∈ Nat ] ((Even y) × (In y l))) is the same as AllOdd l
so the contrapositives of these tell you that EqualM (find-even' l) None iff AllOdd l.  
