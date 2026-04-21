```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Lect22-starter where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  _+_ : Nat → Nat → Nat
  Z + m = m
  (1+ n) + m = 1+ (n + m)

  infixr 10 _+_

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
  {-# BUILTIN LIST List #-}

  map : {A B : Set} (f : A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

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

  data Equals (A : Set) : (a : A) → A → Set where
    Refl : (a : A) → Equals A a a

  sym : {A : Set} {n m : A} → Equals A n m → Equals A m n 
  sym (Refl n) = Refl n
  
  trans : {A : Set} {x y z : A} → Equals A x y → Equals A y z → Equals A x z 
  trans (Refl x) eq2 = eq2

  cong : {A B : Set} (f : A → B) {x y : A} → Equals A x y → Equals B (f x) (f y)
  cong f (Refl x) = Refl (f x)

  {-# BUILTIN EQUALITY Equals #-}

  primitive
    primEraseEquality : ∀ {A : Set} {x y : A} → Equals _ x y → Equals _ x y

  equalChar : (x y : Char) → Either (Equals Char x y) (Equals Char x y → Void)
  equalChar x y with primCharEquality x y
  ... | True = Inl (primEraseEquality equalChar-true) where
    postulate equalChar-true : _
  ... | False = Inr equalChar-false where
    postulate equalChar-false : _

  ¬ : Set → Set
  ¬ A = (A → Void)

  Decision : Set → Set
  Decision A = Either A (¬ A)

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  postulate
    String : Set
  {-# BUILTIN STRING  String #-}

  primitive
    primStringToList   : String → List Char
    primStringFromList : List Char → String

  explode : String → List Char
  explode = primStringToList

  implode : List Char → String
  implode = primStringFromList

  decide= : (n m : Nat) → Decision (Equals _ n m)
  decide= Z Z = Inl (Refl _)
  decide= (1+ n) Z = Inr (\ ())
  decide= Z (1+ m) = Inr (\ ())
  decide= (1+ n) (1+ m) with decide= n m
  ... | Inl (Refl _) = Inl (Refl _)
  ... | Inr no = Inr no2 where
      no2 : Equals _ (1+ n) (1+ m) → Void
      no2 (Refl _) = no (Refl _)

  plus-cong : {n n' m m' : Nat} → Equals _ n n' → Equals _ m m' → Equals _ (n + m) (n' + m')
  plus-cong (Refl a) (Refl a₁) = Refl _
  
  plus-rh-Z : (n : Nat) → Equals _ n (n + Z)
  plus-rh-Z Z = Refl _
  plus-rh-Z (1+ n) = cong 1+ (plus-rh-Z n)
  
  plus-rh-S : (n m : Nat) → Equals Nat (1+ (n + m)) (n + (1+ m))
  plus-rh-S Z _ = Refl _
  plus-rh-S (1+ n) m = cong 1+ (plus-rh-S n m)
  
  plus-comm : (n m : Nat) → Equals Nat (n + m) (m + n)
  plus-comm Z _ = plus-rh-Z _
  plus-comm (1+ n) m = trans (cong 1+ (plus-comm n m)) (plus-rh-S m n)

  plus-assoc : (n m p : Nat) → Equals Nat (n + m + p) ((n + m) + p)
  plus-assoc Z m p = Refl _
  plus-assoc (1+ n) m p = cong 1+ (plus-assoc n m p)
```

# Motivating Example

```
  goal : (x y z w : Nat) → Equals _ (x + z + y + w) ((y + x) + (z + w))
  goal x y z w = {!!}  
```

