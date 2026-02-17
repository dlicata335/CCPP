

```
module Lect08-starter where

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
  infixr 10 _×_

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
    _::_ : (x : A) (xs : List A) → List A

  infixr 99 _::_ 

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

  {---------------  THE CODE  ---------------}

  data RegExp : Set where
    Lit : Char → RegExp
    Wild : RegExp
    _·_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \cdot 
    _∨_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \vee

  infixr 2 _·_
  infixr 3 _∨_
```

# Definition of regular languages

```
  EqualsList : List Char → List Char → Set
  EqualsList l1 l2 = {!!}

  refl-list : (l : List Char) → EqualsList l l
  refl-list l = {!!}

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  Splitting : List Char → Set
  Splitting l = {!!}

  front : (l : List Char) → Splitting l → List Char
  front = {!!}

  back : (l : List Char) → Splitting l → List Char
  back = {!!}

  _∈L_ : List Char → RegExp → Set
  s ∈L r = {!!}
```

# Sound brute-force matcher

```
  split : (l : List Char) → List (Splitting l)
  split l = {!!}

  test = split ('a' :: 'b' :: 'c' :: [])

  match : (r : RegExp) (s : List Char) → Maybe (s ∈L r)
  match r s = {!!}
  
  example : RegExp
  example = Wild · ( (Lit '.' · Lit 'c' · Lit 'o' · Lit 'm') ∨ (Lit '.' · Lit 'e' · Lit 'd' · Lit 'u'))

  test1 = match example ('w' :: 'e' :: 's' :: 'l' :: 'e' :: 'y' :: 'a' :: 'n' :: '.' :: 'e' :: 'd' :: 'u' :: [])

  test2 = match example ('.' :: 'e' :: 'd' :: 'u' :: '.' :: 'e' :: 'd' :: 'u' :: [])
```

# Sound and complete brute-force matcher 

```
  All : (A : Set)
        (P : A → Set)
        (l : List (A))
      → Set
  All A P l = {!!}

  module SplitExhaustive where

    split-exhaustive : (l : List Char)
                      → (P : (sp : Splitting l) → Set)
                      → All _ P (split l)
                      → ((sp : Splitting l) → P sp)
    split-exhaustive = {!!}

  Decision : Set → Set
  Decision A = Either A (A → Void)

  decide-list : (A : Set) (P : A → Set)
              → ((x : A) → Decision (P x))
              → (l : List A) → Either (Σ[ x ∈ A ] P x {- × In x l -}) (All A (\ x → P x → Void) l)
  decide-list A P decide-one l = {!!}

  match2 : (r : RegExp) (s : List Char) → Decision (s ∈L r) 
  match2 r s = {!!}
  
  test3 = match2 example ('w' :: 'e' :: 's' :: 'l' :: 'e' :: 'y' :: 'a' :: 'n' :: '.' :: 'e' :: 'd' :: 'u' :: [])
```
