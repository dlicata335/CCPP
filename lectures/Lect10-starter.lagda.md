
In this class, we will learn about an Agda feature called 'magic with'
that we haven't talked about yet.  'with' is a nicer way to write the
where case helper functions that we have seen many times so far.  

```
module Lect10-starter where

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
    parity n = {!!}
```

The idea is that the case after the vertical bar represent the two cases
for the helper function swap.  

The ... is used frequently, but officially it is syntax for repeating
the same pattern that was before the | as in the line that started the
with: 

```
  module ParityWith2 where 
    parity : (n : Nat) -> Either (Even n) (Odd n)
    parity n = {!!}

  open ParityWith2
```

The reason for this extended syntax is that sometimes the patterns will
change in each line of the with, which is allowed just when the pattern
in the with tells you more information about the original clause.  We
will see examples of this later on.


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
        case2 : Either (EvenNumberIn xs) (AllOdd xs) → Either (EvenNumberIn (x :: xs)) (AllOdd (x :: xs))
        case2 (Inl inxs) = Inl (in-:: x xs inxs)
        case2 (Inr xsodd) = Inr (o , xsodd)
```

Here is one way to rewrite this using a with: 

```
  module FindEvenWith where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even n = {!!}
```

We could also do a two-armed with that matches on both parity and the recursive call at once: 

```
  module FindEvenWith2 where
    find-even : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
    find-even n = {!!}
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
  Succeeds = {!!}
```

Now, we want to prove that if find-even l succeeds with n, then n is
even and in l:

```
  find-even-success : (l : List Nat) (n : Nat)
                    → Succeeds (find-even l)  n
                    → Even n × In n l
  find-even-success l n ret = {!!}
```

Similarly, we can show that find-even l returns None implies every number in l is odd: 

```
  IsNone : Maybe Nat → Set
  IsNone = {!!}

  find-even-failure : (l : List Nat) 
                    → IsNone (find-even l)
                    → AllOdd l
  find-even-failure l isnone = {!!}
```

# Regular Expression Matching

Now that we know about 'with', let's redo the regular expression matcher from last week:  

```
  EqualsList : List Char → List Char → Set
  EqualsList [] [] = Unit
  EqualsList [] (x :: l2) = Void
  EqualsList (x :: l1) [] = Void
  EqualsList (x :: l1) (y :: l2) = EqualsChar x y × EqualsList l1 l2

  refl-list : (l : List Char) → EqualsList l l
  refl-list [] = <>
  refl-list (x :: xs) = refl-char x , refl-list xs

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  data RegExp : Set where
    Lit : Char → RegExp
    Wild : RegExp
    _·_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \cdot 
    _∨_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \vee

  infixr 2 _·_
  infixr 3 _∨_

  example : RegExp
  example = Wild · ( (Lit '.' · Lit 'c' · Lit 'o' · Lit 'm') ∨ (Lit '.' · Lit 'e' · Lit 'd' · Lit 'u'))

  Splitting : List Char → Set
  Splitting s = Σ[ f ∈ List Char ] Σ[ b ∈ List Char ] EqualsList s (append f b)

  front : (l : List Char) → Splitting l → List Char
  front l (f , _ , _) = f

  back : (l : List Char) → Splitting l → List Char
  back l (_ , b , _) = b

  _∈L_ : List Char → RegExp → Set
  s ∈L (Lit c) = EqualsList s (c :: [])
  s ∈L Wild = Unit
  s ∈L (r1 ∨ r2) = Either (s ∈L r1) (s ∈L r2) 
  s ∈L (r1 · r2) = Σ[ sp ∈ Splitting s ] (( (front s sp) ∈L r1) × ( (back s sp) ∈L r2 ))

  Decision : Set → Set
  Decision A = Either A (A → Void)

  decide-list-equality1 : (l : List Char) (x : Char) → Decision (EqualsList l (x :: [])) 
  decide-list-equality1 [] x = Inr (λ v → v)
  decide-list-equality1 (y :: []) x with (equalChar y x)
  ... | (Inl p) = Inl (p , <>)
  ... | (Inr p) = Inr (λ (eq , _) → p eq)
  decide-list-equality1 (y :: y1 :: l) x = Inr second

  addx : (l : List Char) (x : Char)
         (sp : Splitting l)
       → Splitting (x :: l)
  addx l x (f , b , appendfb) = x :: f , b , refl-char x , appendfb

  addx-all : (l : List Char) (x : Char)
           → List(Splitting l)
           → List(Splitting (x :: l))
  addx-all l x [] = []
  addx-all l x (sp :: splits) = addx l x sp :: addx-all l x splits

  split : (l : List Char) → List (Splitting l)
  split [] = ([] , [] , <>) :: []
  split (x :: xs) = (([] , x :: xs , refl-list (x :: xs))) ::
                    addx-all xs x (split xs)

  test-split = split ('a' :: 'b' :: 'c' :: [])

  mutual
    match : (r : RegExp) (s : List Char) → Maybe (s ∈L r)
    match r s = {!!}
    
  test1 = match example ('w' :: 'e' :: 's' :: 'l' :: 'e' :: 'y' :: 'a' :: 'n' :: '.' :: 'e' :: 'd' :: 'u' :: [])

  test2 = match example ('.' :: 'e' :: 'd' :: 'u' :: '.' :: 'e' :: 'd' :: 'u' :: [])

```

## Extrinsic proof of completeness

Using 'with', we can extrinsically prove that when the matcher returns
None, the string is not in the language of the regexp:

```
  NoMatch : {A : Set} → Maybe A → Set
  NoMatch (Some x) = Void
  NoMatch None = Unit

  InSp : {l : List Char} (s : Splitting l) (sps : List (Splitting l)) → Set
  InSp s [] = Void
  InSp s (sp :: sps) = Either (s == sp) (InSp s sps)

  match-none : (r : RegExp) (s : List Char) → NoMatch (match r s) → s ∈L r → Void
  match-none r s no sinr = {!!}
```



