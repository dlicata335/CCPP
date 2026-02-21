In this lecture, we will begin looking at regular expression matching.  

```
module Lect09 where

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
```

# List definitions

Fill in the following analgously to Homework 2.  

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
```

# Regular expressions

A regular expression (or regexp) is a pattern that you can match against
strings.  For example, the regexp _.(com|edu) matches a domain name,
like wesleyan.edu or google.com.  For this week, regular expressions
will be built up from the following grammar:
* The wild regular expression Wild matches every string

* The character literal regular expression Lit c matches a length-one
  string containing just the letter c.

* The disjunction of two regular expressions r1 ∨ r2 matches a string s when either s
matches r1 or s matches r2.  (On paper, it is common to write r1 ∨ r2 as r1|r2).  

* The sequencing of two regular expressions r1 · r2 matches a string s
  when s splits into two strings f followed b, where f matches r1 and
  b matches r2.  (On paper, it is common to write r1 · r2 as juxtaposition r1r2.)

```
  data RegExp : Set where
    Lit : Char → RegExp
    Wild : RegExp
    _·_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \cdot 
    _∨_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \vee

  infixr 2 _·_
  infixr 3 _∨_
```

The above example _(.com|.edu) is coded as follows:

```
  example : RegExp
  example = Wild · ( (Lit '.' · Lit 'c' · Lit 'o' · Lit 'm') ∨ (Lit '.' · Lit 'e' · Lit 'd' · Lit 'u'))
```

# Definition of regular languages
 
Next, we will code the definition of when a regular expression matches a strong.
It's important to note that this is just a *definition* as a type; it's not yet a function
that computes whether the match is true or not.  

To make things simpler, we will define an auxilary type for a splitting
of a list l.  A splitting of l consists of two lists, the front and the
back, with a proof that append front back is l.

```
  Splitting : List Char → Set
  Splitting s = Σ[ f ∈ List Char ] Σ[ b ∈ List Char ] EqualsList s (append f b)

  examplesplit : Splitting ('a' :: 'b' :: 'c' :: [])
  examplesplit = ('a' :: 'b' :: []) , (('c' :: []) , refl-char _ , refl-char _ , refl-char _ , <>)

  examplesplit2 : Splitting ('a' :: 'b' :: 'c' :: [])
  examplesplit2 = ('a' :: []) , (('b' :: 'c' :: []) , refl-char _ , refl-char _ , refl-char _ , <>)
```

For convenience, the functions front and back get the front and back list from l.
```
  front : (l : List Char) → Splitting l → List Char
  front l (f , _ , _) = f

  back : (l : List Char) → Splitting l → List Char
  back l (_ , b , _) = b
```

The relation s ∈L r means "s is in the language of r" or "s matches the regular expression r".  

```
  _∈L_ : List Char → RegExp → Set
  s ∈L (Lit c) = EqualsList s (c :: [])
  s ∈L Wild = Unit
  s ∈L (r1 ∨ r2) = Either (s ∈L r1) (s ∈L r2) 
  s ∈L (r1 · r2) = Σ[ sp ∈ Splitting s ] (( (front s sp) ∈L r1) × ( (back s sp) ∈L r2 ))
```

The final clause can be expanded out (and reassociated) to 
```
  {-
     Σ[ s1 ∈ List Char ] Σ[ s2 ∈ List Char ] -- there exist s1 and s2
        (EqualsList s (append s1 s2) ×
        (s1 ∈L r1) ×
        (s2 ∈L r2))
  -}
```

For example, here is a proof of matching: 

```
  example-match : ('a' :: 'b' :: 'a' :: 'b' :: 'a' :: 'b' :: []) ∈L ((Lit 'a' · Lit 'b') · Wild · Lit 'b')
  example-match = split0 , ( split1 , proof1 , proof2) ,
                  split2 , proof3 , proof2 where
      split0 : Splitting ('a' :: 'b' :: 'a' :: 'b' :: 'a' :: 'b' :: [])
      split0 = ('a' :: 'b' :: [] , 'a' :: 'b' :: 'a' :: 'b' :: [] , refl-list (('a' :: 'b' :: 'a' :: 'b' :: 'a' :: 'b' :: [])))

      split1 : Splitting ('a' :: 'b' :: [])
      split1 = ('a' :: [] , 'b' :: [] , refl-list ('a' :: 'b' :: []))
  
      proof1 : 'a' :: [] ∈L (Lit 'a')
      proof1 = refl-list ('a' :: [])

      proof2 : 'b' :: [] ∈L (Lit 'b')
      proof2 = refl-list ('b' :: [])

      split2 : Splitting ('a' :: 'b' :: 'a' :: 'b' :: [])
      split2 = ('a' :: 'b' :: 'a' :: [] , 'b' :: [] , refl-list (('a' :: 'b' :: 'a' :: 'b' :: [])))

      proof3 : ('a' :: 'b' :: 'a' :: []) ∈L Wild
      proof3 = <>
```

Notice that the proof depends on choosing the correct splittings of the
input string: the middle aba has to match the Wild to leave the
necessary parts before and after it to match ab and b.

# Sound brute-force matcher

First, we need a couple of helper functions: 

```
  decide-list-equality1 : (l : List Char) (x : Char) → Maybe (EqualsList l (x :: []))
  decide-list-equality1 [] x = None
  decide-list-equality1 (y :: []) x = case (equalChar y x) where
    case : Either (EqualsChar y x) (EqualsChar y x → Void) → Maybe (EqualsList (y :: []) (x :: []))
    case (Inl p) = Some (p , <>)
    case (Inr p) = None
  decide-list-equality1 (y :: y1 :: l) x = None
```

The next function enumerates all splittings of a list:

```
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

  test = split ('a' :: 'b' :: 'c' :: [])
```

Now, we can define the matcher.  We use the definition s ∈L r to certify
that when the matcher returns "yes" (Some), the string actually does
match the regular expression according to the definition of matching.
Below, we will do a fancier version that also certfies that when the
matcher returns "no" (None), the string doesn't match the regular
expression.

```
  match : (r : RegExp) (s : List Char) → Maybe (s ∈L r)
  match (Lit x) s = (decide-list-equality1 s x) 
  match Wild s = Some <>
  match (r1 · r2) s = trysplits (split s) where
    trysplit : Splitting s → Maybe (s ∈L (r1 · r2))
    trysplit (front , back , append-front-back) = case (match r1 front) (match r2 back)  where
      case : Maybe (front ∈L r1) → Maybe (back ∈L r2) → Maybe (s ∈L (r1 · r2))
      case (Some inr1) (Some inr2) = Some ( (front , back , append-front-back) , inr1 , inr2)
      case _ _ = None

    trysplits : List (Splitting s) → Maybe (s ∈L (r1 · r2))
    trysplits [] = None
    trysplits (s1 :: ss) = case (trysplit s1) where
      case : Maybe (s ∈L (r1 · r2)) → Maybe (s ∈L (r1 · r2))
      case (Some foundit) = Some foundit
      case None = trysplits ss 
  match (r1 ∨ r2) s = case1 (match r1 s) where
    case1 : Maybe (s ∈L r1) → Maybe (s ∈L (r1 ∨ r2))
    case1 (Some inr1) = Some (Inl inr1)
    case1 None = case2 (match r2 s) where
      case2 : Maybe (s ∈L r2) → Maybe (s ∈L (r1 ∨ r2))
      case2 (Some inr2) = Some (Inr inr2)
      case2 None = None
  
  test1 = match example ('w' :: 'e' :: 's' :: 'l' :: 'e' :: 'y' :: 'a' :: 'n' :: '.' :: 'e' :: 'd' :: 'u' :: [])

  test2 = match example ('.' :: 'e' :: 'd' :: 'u' :: '.' :: 'e' :: 'd' :: 'u' :: [])
```

In the r1 · r2 case, we loop over the splits(s), looking for one where
 the front matches r1 and the back matches r2.  Note that this is
 basically the same linear search algorithm as find-even from last week!


