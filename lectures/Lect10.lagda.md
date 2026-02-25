
In this class, we will learn about an Agda feature called 'magic with'
that we haven't talked about yet.  'with' is a nicer way to write the
where case helper functions that we have seen many times so far.  

```
module Lect10 where

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

  refl : (n : Nat) → Equals n n
  refl Z = <>
  refl (1+ n) = refl n

  sym : (n m : Nat) → Equals n m → Equals m n
  sym Z Z e = <>
  sym (1+ n) (1+ m) e = sym n m e

  data Bool : Set where
    True : Bool
    False : Bool

  {-# BUILTIN BOOL  Bool  #-}
  {-# BUILTIN TRUE  True  #-}
  {-# BUILTIN FALSE False #-}

  postulate {- Agda Primitive -}
    Char : Set

  {-# BUILTIN CHAR Char #-}

  primitive
    primCharToNat : Char → Nat
    primCharEquality : Char → Char → Bool

  postulate
    EqualsChar : Char → Char → Set
    refl-char : (x : Char) → EqualsChar x x
    J-char' : (d : Char)
           → (P : (c : Char) → EqualsChar c d → Set)
           → P d (refl-char d)
           → (c : Char) (eq : EqualsChar c d) → P c eq
    EqualsChar-prop : (c d : Char) (p q : EqualsChar c d)
                    → (P : EqualsChar c d → Set)
                    → P p → P q

  equalChar : (x y : Char) → Either (EqualsChar x y) (EqualsChar x y → Void)
  equalChar x y with primCharEquality x y
  ... | True = Inl equalChar-true where
    postulate equalChar-true : _
  ... | False = Inr equalChar-false where
    postulate equalChar-false : _

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  data _==_ {A : Set} (a : A) : A → Set where
    Refl : a == a
```

# With

Remember the parity function from a few weeks ago.  

```
  module UsingHelper where
    parity : (n : Nat) -> Either (Even n) (Odd n)
    parity Z = Inl <> 
    parity (1+ n) = swap (parity n) where
      swap : Either (Even n) (Odd n) → Either (Even (1+ n)) (Odd (1+ n))
      swap (Inl nIsEven) = Inr nIsEven
      swap (Inr nIsOdd) = Inl nIsOdd
```

Here is how we can rewrite it using the new keyword 'with': 

```
  module ParityWithWith where
    parity : (n : Nat) -> Either (Even n) (Odd n)
    parity Z = Inl <> 
    parity (1+ n) with (parity n) 
    ...              | (Inl nIsEven) = Inr nIsEven
    ...              | (Inr nIsOdd) = Inl nIsOdd
```

The idea is that the case after the vertical bar represent the two cases
for the helper function swap.  

The ... is used frequently, but officially it is syntax for repeating
the same pattern that was before the | as in the line that started the
with: 

```
  module ParityWith2 where 
    parity : (n : Nat) -> Either (Even n) (Odd n)
    parity Z = Inl <> 
    parity (1+ n) with (parity n) 
    parity (1+ n)    | (Inl nIsEven) = Inr nIsEven
    parity (1+ n)    | (Inr nIsOdd) = Inl nIsOdd

```

The reason for this extended syntax is that sometimes the patterns will
change in each line of the with, which is allowed just when the pattern
in the with tells you more information about the original clause.  We
will see examples of this later on.

In general, Agda expands a with to a helper function like above, except
the helper function is parameterized by all of the variables in scope.

```
  module ParityHelper2 where
    parity3 : (n : Nat) -> Either (Even n) (Odd n)
    parity3 Z = Inl <> 
    parity3 (1+ n) = swap n (parity3 n) where
      swap : (n : Nat) → Either (Even n) (Odd n) → Either (Even (1+ n)) (Odd (1+ n))
      swap n (Inl nIsEven) = Inr nIsEven
      swap n (Inr nIsOdd) = Inl nIsOdd
```

Note that, when you're developing a with interactively, you can put a
variable for the thing being case-analyzed in a with like this:

```
  module ParityWith3 where 
    parity : (n : Nat) -> Either (Even n) (Odd n)
    parity Z = Inl <> 
    parity (1+ n) with (parity n) 
    parity (1+ n)    | p = {!!}
```

Then you can case-split p using C-c C-c as usual.  

```
  open ParityWith2
```

## Multiple withs

Recall the linear search algorithm from a couple of weeks ago:

```
  In : Nat → List Nat → Set
  In n [] = Void
  In n (x :: xs) = Either (Equals n x) (In n xs)

  EvenNumberIn : List Nat → Set
  EvenNumberIn l = Σ[ x ∈ Nat ] ((Even x) × (In x l))

  AllOdd : List Nat → Set
  AllOdd [] = Unit
  AllOdd (x :: xs) = (Odd x) × (AllOdd xs)

  in-:: : (x : Nat) (xs : List Nat) → EvenNumberIn xs → EvenNumberIn (x :: xs)
  in-:: x xs inxs = first inxs , first (second inxs) , Inr (second (second inxs))

  module FindEvenHelper where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even [] = Inr <>
    find-even (x :: xs) = case (parity x) where
      case : Either (Even x) (Odd x) → Either (EvenNumberIn (x :: xs)) (AllOdd (x :: xs))
      case (Inl e) = Inl (x , e , Inl (refl x))
      case (Inr o) = case2 (find-even xs) where
        case2 : Either (EvenNumberIn xs) (AllOdd xs)
              → Either (EvenNumberIn (x :: xs)) (AllOdd (x :: xs))
        case2 (Inl inxs) = Inl (in-:: x xs inxs)
        case2 (Inr xsodd) = Inr (o , xsodd)
```

Here is one way to rewrite this using a with: 

```
  module FindEvenWith where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even [] = Inr <>
    find-even (x :: xs) with (parity x)
    ...                     | (Inl e)                   = Inl (x , e , Inl (refl x))
    ...                     | (Inr o) with (find-even xs) 
    ...                                  |  (Inl inxs)  = Inl (in-:: x xs inxs)
    ...                                  |  (Inr xsodd) = Inr (o , xsodd)
```

We could also do a two-armed with that matches on both parity and the recursive call at once: 

```
  module FindEvenWith2 where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even [] = Inr <>
    find-even (x :: xs) with (parity x) | (find-even xs) 
    ...                     | (Inl e)    | _                = Inl (x , e , Inl (refl x))
    ...                     | (Inr o)    | (Inl inxs)       = Inl (in-:: x xs inxs)
    ...                     | (Inr o)    | (Inr xsodd)      = Inr (o , xsodd)
```

Agda expands this to the following helper function: 

```
  module FindEvenHelper2 where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even [] = Inr <>
    find-even (x :: xs) = case x xs (parity x) (find-even xs) where
      case : (x : Nat) (xs : List Nat) → Either (Even x) (Odd x) → Either (EvenNumberIn xs) (AllOdd xs) → Either (EvenNumberIn (x :: xs)) (AllOdd (x :: xs))
      case x xs (Inl e) _ = Inl (x , e , Inl (refl x))
      case x xs (Inr o) (Inl inxs) = Inl (in-:: x xs inxs)
      case x xs (Inr o) (Inr xsodd) = Inr (o , xsodd)
```


## Extrinsic Verification; Why 'with' is 'magic'

The above examples show how to do "intrinsic verification" of linear
search, where the type of the function itself tells you some correctness
properties about it.

Another place where 'with' often gets used is in "extrinsic
verification", which means proving a property of a function after the
function itself has been defined.

For example, suppose we started with a regular old implementation of find-even: 

```
  find-even : List Nat → Maybe Nat
  find-even [] = None
  find-even (x :: xs) with (parity x) 
  ...                    | (Inl _) = Some x
  ...                    | (Inr _) = find-even xs
```

Now, we want to keep that code the same but separately prove that it does the right thing.  

First, we define a relation Succeeds m n which means that m is Some(n): 

```
  Succeeds : Maybe Nat → Nat → Set
  Succeeds (Some x) y = Equals x y
  Succeeds (None) y = Void

  transport-Even : (x y : Nat) → Equals x y → Even x → Even y
  transport-Even Z Z eq e = <>
  transport-Even (1+ (1+ x)) (1+ (1+ y)) eq e = transport-Even x y eq e
```

Now, we want to prove that if find-even l succeeds with n, then n is
even and in l:

```
  find-even-success1 : (l : List Nat) (n : Nat)
                    → Succeeds (find-even l)  n
                    → Even n × In n l
  find-even-success1 (x :: xs) n ret = {!find-even (x::xs) is stuck on parity x!}
```

However, the type of 'ret' is stuck on whether parity x returns Inl or Inr.
Agda displays this as  
  ret : Succeeds (find-even (x :: xs) | parity x) n  
The | means that the 'with' in find-even is stuck on parity x.
We can unstick this by doing the same with in the proof: 


```
  find-even-success2 : (l : List Nat) (n : Nat)
                    → Succeeds (find-even l)  n
                    → Even n × In n l
  find-even-success2 (x :: xs) n ret with parity x
  ...                                   | Inl e = {!!} 
  ...                                   | Inr o = {!!} 
```
In the Inl e case, we now have
ret : Succeeds (find-even (x :: xs) | Inl e) n  
which then reduces to Equals x n.

In the Inr o case, we now have
ret : Succeeds (find-even (x :: xs) | Inr o) n
which then reduces to Succeeds (find-even xs) n.

This is because, when you do a 'with', Agda replaces all occurences of
the scrutinee of the 'with' (parity x in this example) in the context
and in the goal with the patterns for the 'with' in each case.

We can finish the proof as follows: 

```
  find-even-success : (l : List Nat) (n : Nat)
                    → Succeeds (find-even l)  n
                    → Even n × In n l
  find-even-success (x :: xs) n ret with parity x
  ...                                  | Inl e = transport-Even x n ret e  , Inl (sym x n ret )
  ...                                  | Inr o = first rec , Inr (second rec) where
    rec = find-even-success xs n ret
```

Note that the [] case is left off because Succeeds (find-even []) n is
Void, so ret has type Void in this case, and Agda allows you to leave
off clauses with a pattern variable of type Void.  

Similarly, we can show that find-even l returns None implies every number in l is odd: 

```
  IsNone : Maybe Nat → Set
  IsNone (Some x) = Void
  IsNone (None) = Unit

  find-even-failure : (l : List Nat) 
                    → IsNone (find-even l)
                    → AllOdd l
  find-even-failure [] f = <>
  find-even-failure (x :: xs) f with parity x
  find-even-failure (x :: xs) ()   | Inl e
  find-even-failure (x :: xs) f    | Inr o = o , find-even-failure xs f 
```
