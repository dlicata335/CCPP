


```
module Lect20-starter where

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

  sym : {A : Set} (n m : A) → Equals A n m → Equals A m n 
  sym n n (Refl n) = Refl n
  
  trans : {A : Set} (x y z : A) → Equals A x y → Equals A y z → Equals A x z 
  trans x x p (Refl x) eq2 = eq2

  cong : {A B : Set} (f : A → B) (x y : A) → Equals A x y → Equals B (f x) (f y)
  cong f x x (Refl x) = Refl (f x)

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

```

# Some facts about ≤ 

```
  data _≤_ : Nat → Nat → Set where
    Le0  : ∀ {m} → 0 ≤ m 
    Le1+ : ∀ {n m} → n ≤ m → 1+ n ≤ 1+ m 

  ≤-1+ : (x : Nat) → x ≤ 1+ x
  ≤-1+ Z = Le0
  ≤-1+ (1+ x) = Le1+ (≤-1+ x)

  ≤-refl : (x : Nat) → x ≤ x
  ≤-refl Z = Le0
  ≤-refl (1+ x) = Le1+ (≤-refl x)

  ≤-trans : {x y z : Nat} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans Le0 p = Le0
  ≤-trans (Le1+ p) (Le1+ q) = Le1+ (≤-trans p q)

  Positive : Nat → Set
  Positive 0 = Void
  Positive (1+ n) = Unit

  PNat : Set
  PNat = Σ[ n ∈ Nat ] Positive n

  !_ : PNat → Nat
  ! n = first n

  1- : PNat → Nat
  1- (1+ x , _) = x

  _<_ : Nat → Nat → Set
  x < 0 = Void
  x < (1+ y) = x ≤ y

  include<-≤ : {x y : Nat} → x < y → x ≤ y
  include<-≤ {y = 1+ y} p = ≤-trans p (≤-1+ y)

  add<-≤ : {x y : Nat} → x < y → (1+ x) ≤ y
  add<-≤ {y = 1+ y} p = Le1+ p

  ≤-sub< : {x y : Nat} → (1+ x) ≤ y → x < y 
  ≤-sub< {y = 1+ y} (Le1+ p) = p

  <-trans : {x y z : Nat} → x < y → y < z → x < z
  <-trans {y = 1+ y} {z = 1+ z} p (Le1+ q) = ≤-trans (≤-trans p q) (≤-1+ _)

  data Trichotomy (x y : Nat) : Set where
    Less :  x < y → Trichotomy x y
    Greater : y < x → Trichotomy x y
    Equal : Equals _ x y → Trichotomy x y

  check< : (m n : Nat) → Trichotomy m n
  check< Z Z = Equal (Refl _)
  check< Z (1+ n) = Less (Le0)
  check< (1+ m) Z = Greater Le0
  check< (1+ m) (1+ n) with check< m n
  ... | Equal (Refl _) = Equal (Refl _)
  check< (1+ m) (1+ (1+ n)) | Less lt = Less ( (Le1+ lt) )
  check< (1+ (1+ m)) (1+ n) | Greater lt = Greater ( (Le1+ lt) )

  check= : (m n : Nat) → Decision (Equals _ m n)
  check= Z Z = Inl (Refl _)
  check= (1+ m) Z = Inr (\ ())
  check= Z (1+ m) = Inr (\ ())
  check= (1+ m) (1+ n) with check= m n
  ...                     | Inl (Refl _) = Inl (Refl _)
  ...                     | Inr (neq) = Inr ((λ { (Refl _) → neq (Refl _) }))

  max : Nat → Nat → Nat
  max n m with check< n m 
  ... | Less _ = m
  ... | Equal _ = n
  ... | Greater _ = n

  min : Nat → Nat → Nat
  min n m with check< n m 
  ... | Less _ = n
  ... | _ = m

  not-reflexive : (x : Nat) → x < x → Void
  not-reflexive Z () 
  not-reflexive (1+ x) (Le1+ p) = not-reflexive _ p

  not-symmetric : {x y : Nat} → (_ : x < y) → (_ : y < x) → Void
  not-symmetric {x = 1+ x} {y = 1+ y} (Le1+ p) (Le1+ q) = not-symmetric p q
```

# Dictionary maping keys to values

```
  Value : Set
  Value = String

  Key : Set
  Key = PNat

  module Simple where
    data Tree : Set where
      Empty : Tree
      Node : Key → Value → (left : Tree) (right : Tree) → Tree
  
    data InTree : Key → Tree → Set where
      Here : {x : Key} {v : Value} {l r : Tree} → InTree x (Node x v l r)
      ThereLeft : {k x : Key} {v : Value} {l r : Tree} → InTree k l → InTree k (Node x v l r)
      ThereRight : {k x : Key} {v : Value} {l r : Tree} → InTree k r → InTree k (Node x v l r)
  
    lookup : (t : Tree) → (x : Key) → Decision (InTree x t)
    lookup Empty x = Inr (\ ())
    lookup (Node (1+ k , _) v l r) x with check= (1+ k) (! x)
    ... | Inl (Refl _) = Inl Here
    ... | Inr nothere with lookup l x
    ...              | Inl inleft = Inl (ThereLeft inleft)
    ...              | Inr notinleft with lookup r x
    ...                                 | Inl inright = Inl (ThereRight inright)
    ...                                 | Inr notinright = Inr nowhere where
      nowhere : _ → _
      nowhere Here = nothere (Refl _)
      nowhere (ThereLeft i) = notinleft i
      nowhere (ThereRight i) = notinright i
```

# Sorted Trees

```
  data SortedTree : (low : Nat) (high : Nat) → Set where
    Empty : {low high : Nat} (lh : low < high) → SortedTree low high 
    Node : (x : Key) (xv : Value)
           {low : Nat} (left : SortedTree low (! x))
           {high : Nat} (right : SortedTree (! x) high)
         → SortedTree low high 

  get-interval : {low high : Nat} → SortedTree low high → low < high
  get-interval = {!!}

  data InTree : Key → {low high : Nat}→ SortedTree low high → Set where
    Here : {x : Key} {xv : Value}
           {low : Nat} {left : SortedTree low (! x) }
           {high : Nat} {right : SortedTree (! x) high }
         → InTree x (Node x xv left right)
    ThereLeft : {x k : Key} {xv : Value}
           {low : Nat} {left : SortedTree low (! x) }
           {high : Nat} {right : SortedTree (! x) high }
            → InTree k left
            → InTree k (Node x xv left right)
    ThereRight : {x k : Key} {xv : Value}
           {low : Nat} {left : SortedTree low (! x)}
           {high : Nat} {right : SortedTree (! x) high}
            → InTree k right
            → InTree k (Node x xv left right)

  bound-low : {low high : Nat} (t : SortedTree low high)
            {y : Key}
          → InTree y t
          → low < (! y) 
  bound-low t path = {!!}

  bound-high : {low high : Nat} (t : SortedTree low high)
          {x : Key}
          → InTree x t
          → (! x) < high 
  bound-high = {!!}

  lookup : {low : Nat} {high : Nat} 
         → (t : SortedTree low high)
         → (k : Key)
         → Decision (InTree k t)
  lookup (Empty lh) lookkey = {!!}
  lookup (Node x xv l r) lookkey with check< (! lookkey) (! x)
  lookup (Node (1+ x , _) xv l r) lookkey    | Equal (Refl _) = {!!}
  lookup (Node x xv l r) lookkey    | Less lookkeyx with lookup l lookkey
  lookup (Node x xv l r) lookkey    | Less lookkeyx    | Inl inleft =  {!!}
  lookup (Node x xv l r) lookkey    | Less lookkeyx    | Inr notinleft = Inr nowhere where
    nowhere : InTree lookkey (Node x xv l r) → Void
    nowhere Here = {!!}
    nowhere (ThereLeft inleft) = {!!}
    nowhere (ThereRight inright) = {!!}
  lookup  (Node x xv l r) lookkey | Greater xlookkey = {!!}

  insert : {low : Nat} {high : Nat} 
         → SortedTree low high 
         → (newkey : Key) (newv : Value)
         → SortedTree (min (1- newkey) low) (max (1+ (! newkey)) high)
  insert = {!!}
```


