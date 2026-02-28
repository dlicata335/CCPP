
In this lecture, we will introduce a general equality type.  


```
module Lect11 where

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

  mutual
    Even : Nat → Set
    Even Z = Unit
    Even (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd Z = Void
    Odd (1+ n) = Even n

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

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  double : Nat → Nat
  double Z = Z
  double (1+ n) = 1+ (1+ (double n))

  _+_ : Nat → Nat → Nat
  _+_ Z m = m
  _+_ (1+ n) m = 1+ (_+_ n m)
  
  -- end library code
  -- ----------------------------------------------------------------------
```

# Equality defined by congruence/injectivity and disjointness

First, let's think about how we've defiend equality so far.  For each
datatype like natural numbers, lists, etc, we've defined a type by
recursion that represents equality in that type.
```
  module Computational where
  
    Equals : Nat → Nat → Set
    Equals Z Z = Unit
    Equals Z (1+ n) = Void
    Equals (1+ n) Z = Void
    Equals (1+ n) (1+ m) = Equals n m
```
The definition of
equality is based on the congruence (equal subparts give equal wholes),
injectivity (equal wholes have equal subparts), and disjointness
(different datatype constructors are different) properties of the
datatype constructors.
Notice that for all of these disjointness, congruence, and injectivity lemmas, the output is the same as the input.
```
    1+-Z-disjoint : (n : Nat) → Equals 0 (1+ n) → Void
    1+-Z-disjoint n v = v 

    Z-1+-disjoint : (n : Nat) → Equals (1+ n) 0 → Void
    Z-1+-disjoint n v = v

    1+-congruence : (n m : Nat) → Equals n m → Equals (1+ n) (1+ m)
    1+-congruence n m e = e

    1+-injective : (n m : Nat) → Equals (1+ n) (1+ m) → Equals n m
    1+-injective n m e = e
```

Then, we've proved various properties like showing that equality is an
equivalence relation (reflexive, symmetric, transitive). These require an inductive proof.  
```
    refl : (n : Nat) → Equals n n
    refl Z = <>
    refl (1+ n) = refl n
  
    sym : (n m : Nat) → Equals n m → Equals m n 
    sym Z Z e = <>
    sym Z (1+ m) e = e
    sym (1+ n) Z e = e
    sym (1+ n) (1+ m) e = sym n m e
  
    trans : (n m p : Nat) → Equals n m → Equals m p → Equals n p
    trans Z Z Z eq1 eq2 = <>
    trans (1+ n) (1+ m) (1+ p) eq1 eq2 = trans n m p eq1 eq2
```

We also need to prove lemmas about that each function takes equal inputs
to equal outputs, like add-k-to-equals from the HW04 support code, which
also require an inductive proof:

```
    add-k-to-equals : (k n m :  Nat) → Equals n m → Equals (k + n) (k + m)
    add-k-to-equals Z n m eq = eq
    add-k-to-equals (1+ k) n m eq = add-k-to-equals k n m eq
```

# Propositional equality

There is an alternative way to define equality is using a single
definition that works for all types at once.  

```
  module EqualityType where
  
    data Equals (A : Set) : (a : A) → A → Set where
      Refl : (a : A) → Equals A a a
```

This definition says that Refl proves Equals A a a for any type A and term a:A,
and moreover that we can reason from an assumed equality Equals A a b by pattern-matching
it as Refl a : Equals A a a, replacing b with a in the goal.  

For example, we can prove symmetry and transitivity without the induction on n:

```
    sym : (n m : Nat) → Equals Nat n m → Equals Nat m n 
    sym n n (Refl n) = Refl n

    trans : (n m p : Nat) → Equals Nat n m → Equals Nat m p → Equals Nat n p
    trans n n p (Refl n) eq2 = eq2
```

We can also prove that any function respects equality just by pattern-matching:
```
    1+-congruence : (n m : Nat) → Equals Nat n m → Equals Nat (1+ n) (1+ m)
    1+-congruence n n (Refl n) = (Refl (1+ n))

    add-k-to-equals : (k n m :  Nat) → Equals Nat n m → Equals Nat (k + n) (k + m)
    add-k-to-equals k n n (Refl n) = Refl (k + n)
```  

The one downside is that the congruence, injectivity, aand disjointness
lemmas are not true by definition, so you will have to use them
explicitly in proofs.  We can prove them using a couple of other
features of pattern matching on an equality in a datatype:

* A function input that is an equality of two different datatype
  constructors can be pattern matched as the impossible pattern ().

* A function input that is an equality of the same datatype constructor
can pattern match the equalty as reflexivity.  

```
    1+-Z-disjoint : (n : Nat) → Equals Nat 0 (1+ n) → Void
    1+-Z-disjoint n ()

    Z-1+-disjoint : (n : Nat) → Equals Nat (1+ n) 0 → Void
    Z-1+-disjoint n ()

    1+-injective : (n m : Nat) → Equals Nat (1+ n) (1+ m) → Equals Nat n m
    1+-injective n n (Refl (1+ n)) = Refl n 
```

Here is an example of using these lemmas:

```
    module Proof1 where
      plus-rh-Z : (n : Nat) → Equals Nat n (n + Z)
      plus-rh-Z Z = Refl Z
      plus-rh-Z (1+ n) = 1+-congruence n (n + Z) (plus-rh-Z n)
    
      plus-rh-S : (n m : Nat) → Equals Nat (1+ (n + m)) (n + (1+ m))
      plus-rh-S Z m = Refl (1+ m)
      plus-rh-S (1+ n) m = 1+-congruence (1+ (n + m)) (n + 1+ m)
                                         (plus-rh-S n m)
    
      plus-comm : (n m : Nat) → Equals Nat (n + m) (m + n)
      plus-comm Z m = plus-rh-Z m
      plus-comm (1+ n) m = trans (1+ n + m) (1+ (m + n)) (m + 1+ n)
                                 (1+-congruence (n + m) (m + n) (plus-comm n m))
                                 (plus-rh-S m n)
```

If you compare this to your solution from HW02, it's probably pretty
similar except that in HW02 you didn't need the 1+-congruence step,
because that was true by definition.

Note that Agda can often infer the type of an equality and some of the
inputs to these equality lemmas, in which case you can leave them off
with an _, or ask Agda to fill them in by putting in a goal and then
using C-c C-s (solve) in that goal.

```
    module Proof2 where
      plus-rh-Z : (n : Nat) → Equals _ n (n + Z)
      plus-rh-Z Z = Refl _
      plus-rh-Z (1+ n) = 1+-congruence _ _ (plus-rh-Z n)
    
      plus-rh-S : (n m : Nat) → Equals Nat (1+ (n + m)) (n + (1+ m))
      plus-rh-S Z _ = Refl _
      plus-rh-S (1+ n) m = 1+-congruence _ _ (plus-rh-S n m)
    
      plus-comm : (n m : Nat) → Equals Nat (n + m) (m + n)
      plus-comm Z _ = plus-rh-Z _
      plus-comm (1+ n) m = trans _ _ _ (1+-congruence _ _ (plus-comm n m)) (plus-rh-S m n)
```

# Interderivability

We can prove that this defines the same relation as before:

```  
    to : (x y : Nat) → Computational.Equals x y → Equals Nat x y
    to Z Z <> = Refl _
    to (1+ x) (1+ y) e = 1+-congruence _ _ (to x y e)
  
    from : (x y : Nat) → Equals Nat x y → Computational.Equals x y 
    from x x (Refl _) = Computational.refl x
```

# Polymorphic lemmas

Above, we worked with the type Equal Nat x y to make things concrete,
but the symmetry, transitivity, and congruence lemmas can be proved in
the same way for any type:

```
  module Polymorphic where
    open EqualityType using (Equals; Refl)

    sym : {A : Set} (n m : A) → Equals A n m → Equals A m n 
    sym n n (Refl n) = Refl n
  
    trans : {A : Set} (x y z : A) → Equals A x y → Equals A y z → Equals A x z 
    trans x x p (Refl x) eq2 = eq2

    cong : {A B : Set} (f : A → B) (x y : A) → Equals A x y → Equals B (f x) (f y)
    cong f x x (Refl x) = Refl (f x)

```

We can use the cong higher-order function to prove the congruence properties that we proved before:
```
    1+-congruence : (n m : Nat) → Equals Nat n m → Equals Nat (1+ n) (1+ m)
    1+-congruence n m e = cong 1+ _ _ e

    add-k-to-equals : (k n m :  Nat) → Equals Nat n m → Equals Nat (k + n) (k + m)
    add-k-to-equals k n m e = cong (λ x → k + x) _ _ e
```
You're always welcome to write lemmas like this out and define them by
pattern matching on Refl, like the definitions above, but if you want to
you can use the higher-order cong function to save some code.
