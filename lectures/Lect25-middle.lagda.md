```
{-# OPTIONS --without-K #-}

module Lect25-middle where

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
```

# Basic Definitions

```
  Type = Set

  data Path (A : Type) : (a : A) → A → Type where
    id : {a : A} → Path A a a

  inverse : {A : Type} {a b : A} → Path A a b → Path A b a
  inverse id = id

  compose : {A : Type} {a b c : A} → Path A a b → Path A b c → Path A a c
  compose id q = q

  cancel : {A : Type} {a b : A} (p : Path A a b) → Path (Path A a a) (compose p (inverse p)) id
  cancel id = id

  cancel2 : {A : Type} {a b : A} (p : Path A a b) → Path (Path A b b) (compose (inverse p) p) id
  cancel2 id = id

  assoc : {A : Type} {a b c d : A} (p : Path A a b) (q : Path A b c) (r : Path A c d)
        → Path (Path A a d) (compose p (compose q r)) (compose (compose p q) r)
  assoc id q r = id

  inverse-compose : {A : Type} {a b c : A}
                  (p : Path A a b) (q : Path A b c)
                  → Path (Path A c a) (inverse (compose p q )) (compose (inverse q) (inverse p))
  inverse-compose id id = id

  inverse-inverse : {A : Type} {a b : A} (p : Path A a b) → Path (Path A a b) (inverse (inverse p)) p
  inverse-inverse id = id

  cong : {A B : Type} {a b : A} (f : A → B)
       → Path A a b
       → Path B (f a) (f b)
  cong f id = id

  all-refl : {A : Set} {a : A} (p : Path A a a) → Path (Path A a a) p id
  all-refl p = {!p!}
```

# Circle example

```
  module Circle where 
    postulate
      Circle : Type
      north : Circle
      south : Circle
      east : Path Circle north south
      west : Path Circle north south
    
    clockwise : Path Circle north north
    clockwise = compose east (inverse west)
    
    counterclockwise : Path Circle north north
    counterclockwise = compose west (inverse east)
    
    example : Path (Path Circle north north) (compose clockwise (inverse clockwise)) id
    example = cancel clockwise
    
    example2 : Path (Path Circle north north) (compose clockwise counterclockwise) id
    example2 = compose (cong (compose clockwise)
                             (compose (cong (\ h → compose h (inverse east)) (inverse (inverse-inverse west)))
                                      (inverse (inverse-compose east (inverse west)))))
               example
```

# Disc example

```
  module Disc where
    postulate
      Disc : Type
      north : Disc
      south : Disc
      east : Path Disc north south
      west : Path Disc north south
      surface : Path (Path Disc north south) east west

    clockwise : Path Disc north north
    clockwise = compose east (inverse west)

    filled : Path (Path Disc north north) clockwise id
    filled = compose (cong (\ h → (compose h (inverse west))) surface ) (cancel west)
```

# Homotopy levels

```
  IsAProp : Type → Type
  IsAProp A = (x y : A) → Path A x y

  IsASet : Type → Type
  IsASet A = (x y : A) → IsAProp (Path A x y)

  -- e.g. the circle, or the torus
  IsA1Type : Type → Type
  IsA1Type A = (x y : A) → IsASet (Path A x y)
```

## Propositions
```
  unit-prop : IsAProp Unit
  unit-prop x y = id

  void-prop : IsAProp Void
  void-prop x ()

  cong-, : {A B : Type} {a a' : A} {b b' : B}
         → (Path A a a' × Path B b b')
         → Path (A × B) (a , b) (a' , b')
  cong-, (id , id) = id

  and-prop : {A B : Type} → IsAProp A → IsAProp B → IsAProp (A × B)
  and-prop propA propB (x , y) (x' , y') = cong-, (propA x x' , propB y y')

  either-Prop : {A B : Type} →  IsAProp A → IsAProp B → IsAProp (Either A B)
  either-Prop propA propB (Inl x) (Inl x₁) = cong Inl (propA _ _)
  either-Prop propA propB (Inl x) (Inr y) = {!bad!}
  either-Prop propA propB (Inr y) (Inl x) = {!!}
  either-Prop propA propB (Inr y) (Inr y₁) = cong Inr (propB _ _)
```

## Sets
```
  module BoolSet where
    EqualsBool : Bool → Bool → Set
    EqualsBool True True = Unit
    EqualsBool True False = Void
    EqualsBool False True = Void
    EqualsBool False False = Unit
  
    decode : (b1 b2 : Bool) → EqualsBool b1 b2 → Path Bool b1 b2
    decode True True _ = id
    decode False False _ = id
  
    encode : (b1 b2 : Bool) → Path Bool b1 b2 → EqualsBool b1 b2
    encode True True id = <>
    encode False False id = <>
  
    roundtrip : (b1 b2 : Bool) (p : Path Bool b1 b2) → Path (Path Bool b1 b2) (decode _ _ (encode _ _ p)) p
    roundtrip True _ id = id
    roundtrip False _ id = id
    
    loop-ident-bool : (p : Path Bool True True) → Path (Path Bool True True) id p
    loop-ident-bool p = roundtrip _ _ p
  
    loop-ident-bool2 : (p : Path Bool False False) → Path (Path Bool False False) id p
    loop-ident-bool2 p = roundtrip _ _ p
  
    bool-set : IsASet Bool
    bool-set True .True id q = loop-ident-bool q
    bool-set False .False id q = loop-ident-bool2 q
```

### Exercise: show that Nat is a Set 

```
  module NatSet where
    EqualsNat : Nat → Nat → Set
    EqualsNat Z Z = Unit
    EqualsNat Z (1+ y) = Void
    EqualsNat (1+ x) Z = Void
    EqualsNat (1+ x) (1+ y) = EqualsNat x y

    EqualsNat-refl : (x : Nat) → EqualsNat x x
    EqualsNat-refl Z = <>
    EqualsNat-refl (1+ x) = EqualsNat-refl x

    decode : (x y : Nat) → EqualsNat x y → Path Nat x y
    decode = {!!}

    encode : (x y : Nat) → Path Nat x y → EqualsNat x y
    encode x y p = {!!}

    decode-diag : (x : Nat) (q : EqualsNat x x) → Path (Path Nat x x) (decode x x q) id
    decode-diag = {!!}
  
    roundtrip : (x y : Nat) (p : Path Nat x y) → Path (Path Nat x y) (decode _ _ (encode _ _ p)) p
    roundtrip x y p = {!!}
 
    nat-set : IsASet Nat
    nat-set = {!!}
```

### Exercise: show that A × B is a Set when A and B are

```
  retract-Prop : {A B : Type}
               → (to : B → A)
               → (from : A → B)
               → (roundtrip : (x : B) → Path B (from (to x)) x)
               → IsAProp A
               → IsAProp B
  retract-Prop = {!!}

  and-set : {A B : Type} → IsASet A → IsASet B → IsASet (A × B)
  and-set sA sB = {!!}
```
