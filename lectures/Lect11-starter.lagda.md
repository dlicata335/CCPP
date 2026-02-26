
In this lecture, we will introduce a general equality type.  


```
module Lect11-starter where

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
    Equals n m = {!!}
```
  The definition of
equality is based on the congruence (equal subparts give equal wholes),
injectivity (equal wholes have equal subparts), and disjointness
(different datatype constructors are different) properties of the
datatype constructors.
Notice that for all of these disjointness, congruence, and injectivity lemmas, the output is the same as the input.
```
    1+-Z-disjoint : {!!}
    1+-Z-disjoint = {!!}

    Z-1+-disjoint : {!!}
    Z-1+-disjoint = {!!}

    1+-congruence : {!!}
    1+-congruence = {!!}

    1+-injective : {!!}
    1+-injective = {!!}
```

Then, we've proved various properties like showing that equality is an
equivalence relation (reflexive, symmetric, transitive). These require an inductive proof.  
```
    refl : (n : Nat) → Equals n n
    refl = {!!}
  
    sym : (n m : Nat) → Equals n m → Equals m n 
    sym n m e = {!!}
  
    trans : (n m p : Nat) → Equals n m → Equals m p → Equals n p
    trans n m p = {!!}
```

We also need to prove lemmas about that each function takes equal inputs
to equal outputs, like add-k-to-equals from the HW04 support code, which
also require an inductive proof:

```
    add-k-to-equals : (k n m :  Nat) → Equals n m → Equals (k + n) (k + m)
    add-k-to-equals = {!!}
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
    sym = {!!}

    trans : (n m p : Nat) → Equals Nat n m → Equals Nat m p → Equals Nat n p
    trans = {!!}
```

We can also prove that any function respects equality just by pattern-matching:
```
    add-k-to-equals : (k n m :  Nat) → Equals Nat n m → Equals Nat (k + n) (k + m)
    add-k-to-equals = {!!}
```  

The one downside is that the congruence, injectivity, aand disjointness
lemmas are not true by definition, so you will have to use them
explicitly in proofs.

```
    1+-Z-disjoint : (n : Nat) → Equals Nat 0 (1+ n) → Void
    1+-Z-disjoint = {!!}

    Z-1+-disjoint : (n : Nat) → Equals Nat (1+ n) 0 → Void
    Z-1+-disjoint = {!!}

    1+-congruence : (n m : Nat) → Equals Nat n m → Equals Nat (1+ n) (1+ m)
    1+-congruence = {!!}

    1+-injective : (n m : Nat) → Equals Nat (1+ n) (1+ m) → Equals Nat n m
    1+-injective = {!!}
```

Here is an example of using these lemmas:

```
    module Proof1 where
      plus-rh-Z : (n : Nat) → Equals Nat n (n + Z)
      plus-rh-Z = {!!}
    
      plus-rh-S : (n m : Nat) → Equals Nat (1+ (n + m)) (n + (1+ m))
      plus-rh-S = {!!}
    
      plus-comm : (n m : Nat) → Equals Nat (n + m) (m + n)
      plus-comm = {!!}
```

If you compare this to your solution from HW02, it's probably pretty
similar except that in HW02 you didn't need the 1+-congruence step,
because that was true by definition.


Note that Agda can often infer the type of an equality and some of the
inputs to these equality lemmas, in which case you can leave them off
with an _.

```
    module Proof2 where
      plus-rh-Z : (n : Nat) → Equals _ n (n + Z)
      plus-rh-Z = {!!} 
    
      plus-rh-S : (n m : Nat) → Equals Nat (1+ (n + m)) (n + (1+ m))
      plus-rh-S = {!!}
    
      plus-comm : (n m : Nat) → Equals Nat (n + m) (m + n)
      plus-comm = {!!}
```

# Interderivability

```  
    to : (x y : Nat) → Computational.Equals x y → Equals Nat x y
    to = {!!}
  
    from : (x y : Nat) → Equals Nat x y → Computational.Equals x y 
    from = {!!}
```

# Polymorphic lemmas

```
  module Polymorphic where
    open EqualityType using (Equals; Refl)

    sym : {A : Set} (n m : A) → Equals A n m → Equals A m n 
    sym = {!!}
  
    trans : {A : Set} (x y z : A) → Equals A x y → Equals A y z → Equals A x z 
    trans = {!!}

    cong : {A B : Set} (f : A → B) (x y : A) → Equals A x y → Equals B (f x) (f y)
    cong = {!!}

```

# Exercises

Prove that list equality is a congruence, injective, and disjoint:

```
    ::-disjoint : {A : Set} (x : A) (xs : List A) → Equals (List A) (x :: xs) [] → Void
    ::-disjoint = {!!}
    
    ::-disjoint2 : {A : Set} (x : A) (xs : List A) → Equals (List A) [] (x :: xs) → Void
    ::-disjoint2 = {!!}
    
    ::-injective-head : {A : Set} (x y : A) (xs ys : List A) → Equals (List A) (x :: xs) (y :: ys) → Equals A x y
    ::-injective-head = {!!}
    
    ::-injective-tail : {A : Set} (x y : A) (xs ys : List A) → Equals _ (x :: xs) (y :: ys) → Equals _ xs ys
    ::-injective-tail = {!!}
    
    ::-cong-head : {A : Set} (x y : A) (xs : List A) → Equals A x y → Equals (List A) (x :: xs) (y :: xs)
    ::-cong-head = {!!}

    ::-cong-tail : {A : Set} (x : A) (xs ys : List A) → Equals (List A) xs ys → Equals (List A) (x :: xs) (x :: ys)
    ::-cong-tail = {!!}

```

Consider the append function:

```
    append : {A : Set} → List A → List A → List A
    append [] ys = ys
    append (x :: xs) ys = x :: append xs ys
```

Prove that appending the empty list to the end of a list adds nothing to the list:

```
    append-rh-[] : {A : Set} (xs : List A) → Equals (List A) (append xs []) xs
    append-rh-[] = {!!}
```

Prove that the append function is associative: 

```
    append-assoc : {A : Set} (xs ys zs : List A) → Equals (List A) (append xs (append ys zs)) (append (append xs ys) zs)
    append-assoc = {!!}
```    

Prove that list equality is decidable, assuming you can decide equality
for the elements of the list (in this problem, characters):

```
    Decision : Set → Set
    Decision A = Either A (A → Void)

    postulate
      decide-char-equality : (x y : Char) → Either (Equals Char x y) (Equals Char x y → Void)

    decide-list-equality : (l1 l2 : List Char) → Decision (Equals _ l1 l2)
    decide-list-equality l1 l2 = {!!}
```
