```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Lect23-starter where

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
  goal x y z w = trans (plus-cong (Refl x)
                       (trans (plus-assoc z y w) (plus-cong (plus-comm z y) (Refl _))))
                       ((trans (plus-assoc x (y + z) w)
                               (trans (plus-cong (plus-assoc x y z) (Refl _))
                                      (trans ((sym (plus-assoc (x + y) z w)))
                                        (plus-cong (plus-comm x y) (Refl _) ))) ))
```

# Syntax for problems 

```
  data Syntax : Set where
      Var1 : Syntax
      Var2 : Syntax
      Var3 : Syntax
      Var4 : Syntax
      Const : Nat → Syntax
      Plus : Syntax → Syntax → Syntax

  Environment : Set
  Environment = Nat × Nat × Nat × Nat

  evaluate : Syntax → Environment → Nat
  evaluate Var1 (v1 , v2 , v3 , v4) = v1
  evaluate Var2 (v1 , v2 , v3 , v4) = v2
  evaluate Var3 (v1 , v2 , v3 , v4) = v3
  evaluate Var4 (v1 , v2 , v3 , v4) = v4
  evaluate (Const n) _ = n
  evaluate (Plus t1 t2) v = evaluate t1 v + evaluate t2 v

  example-evaluate : (x y z w : Nat) → Equals _ ((y + x) + (z + w)) (evaluate (Plus (Plus Var2 Var1) (Plus Var3 Var4)) (x , y , z , w))
  example-evaluate x y z w = Refl _
```

# Solver 

```
  Coefficients : Set
  Coefficients = Nat × Nat × Nat × Nat × Nat

  add-coeff : Coefficients → Coefficients → Coefficients
  add-coeff (a1 , b1 , c1 , d1 , e1) (a2 , b2 , c2 , d2 , e2) =
    ((a1 + a2) , (b1 + b2) , (c1 + c2) , (d1 + d2) , (e1 + e2)     )

  normalize : Syntax → Coefficients
  normalize Var1 = (1 , 0 , 0 , 0 , 0)
  normalize Var2 = (0 , 1 , 0 , 0 , 0)
  normalize Var3 = (0 , 0 , 1 , 0 , 0)
  normalize Var4 = (0 , 0 , 0 , 1 , 0)
  normalize (Const x) = ( 0 , 0 , 0 , 0 , x)
  normalize (Plus s1 s2) = add-coeff (normalize s1) (normalize s2)
```

# Correctness of the solver

Write a function that "reifies" the coefficients as syntax, so that a
vector (a,b,c,d,e) is converted in some standardized way to syntax for
ax + by + cz + dw + e.

Eventually, you will need to prove that the reification of the
normalization of some syntax is equal (under evaluation) to the original
syntax, but do this after the rest of the lab.  

```
  reify-coeff : Coefficients → Syntax
  reify-coeff = {!!}

  normalize-ok : (t : Syntax) (v : Environment) → Equals _ (evaluate t v) (evaluate (reify-coeff (normalize t)) v)
  normalize-ok = {!DO THIS AFTER the rest of the lab below!}
```

Write a function that tests equality of coefficients (use decide= from above):

```
  equal-coeff : (c d : Coefficients) → Maybe (Equals _ c d)
  equal-coeff c d = {!!}
```

Tie it all together into a solver that checks if the evaluation of two
pieces of syntax are equal by testing if the corresponding coefficients
are equal:

```
  cong-eval-reify : {c d : Coefficients} (v : Environment) → Equals _ c d → Equals _ (evaluate (reify-coeff c) v) (evaluate (reify-coeff d) v)
  cong-eval-reify v (Refl _) = Refl _
    
  solver : (n m : Syntax) (v : Environment) → Maybe (Equals _ (evaluate n v) (evaluate m v) )
  solver n m v = {!!}
```

# Examples of using the solver 

After you've written the solver, but before you've finished the
normalize-ok proof, you should be able to fill the first two goals and
see that the third is Void:

```
  IsSome : {A : Set} → Maybe A → Set
  IsSome (Some x) = Unit
  IsSome None = Void

  use : {A : Set} (x : Maybe A) → IsSome x → A
  use (Some x) p = x

  goal2 : (x y z w : Nat) → Equals _ (x + z + y + w) ((y + x) + (z + w))
  goal2 x y z w = use (solver (Plus Var1 (Plus Var2 (Plus Var3 Var4)))
                              (Plus (Plus Var3 Var1) (Plus Var2 Var4))
                              ((x , z , y , w)))
                              {!<>!}

  goal3 : (x y : Nat) → Equals _ (x + y + x + 3) ((x + 1) + x + 2 + y)
  goal3 x y = use (solver (Plus Var1 (Plus Var2 (Plus Var1 (Const 3))))
                          (Plus (Plus Var1 (Const 1)) (Plus Var1 (Plus (Const 2) (Var2))))
                          ((x , y , 0 , 0)))
                          {!<>!}

  goal4 : (x y : Nat) → Equals _ (x + y + x + 3) ((x + 1) + x + x + y)
  goal4 x y = use (solver (Plus Var1 (Plus Var2 (Plus Var1 (Const 3))))
                          (Plus (Plus Var1 (Const 1)) (Plus Var1 (Plus Var1 (Var2))))
                          ((x , y , 0 , 0)))
                          {!not true!}
```
